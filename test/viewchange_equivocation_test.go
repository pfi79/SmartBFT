// Copyright IBM Corp. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0
//

package test

import (
	"crypto/ed25519"
	"fmt"
	"os"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/hyperledger/SmartBFT/pkg/types"
	protos "github.com/hyperledger/SmartBFT/smartbftprotos"
	"github.com/stretchr/testify/assert"
	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"
	"google.golang.org/protobuf/proto"
)

// Two strengthenings over viewchange_equivocation_test.go:
//
//   - Node 1's commit reaches node 4 by a plain NETWORK DELAY.
//     Node 4 is never disconnected; node 1 broadcasts its genuine commit for v1
//     to every replica through its own code; the network holds the copy addressed
//     to node 4 (captured on node 4's own inbound edge in phase 1) and releases
//     that exact buffered message in phase 3 via the transport (network.send).
//     No message is fabricated or sent "as node 1".
//
//   - The view change is driven by TIME without injected ViewChange messages.
//     Node 1's heartbeats are dropped, so nodes 2, 3, 4 suspect the silent leader
//     and emit their own ViewChange(nextView=1) on timeout.
//     The harness only advances their logical clocks. No ViewChange
//     is injected on any honest node's behalf.
//
//     Run:
//     go test ./test/ -run TestNoForkOnNewViewEquivocation -v

// Safety regression test: a Byzantine view leader equivocates over the content of
// the newView message, telling one replica a set of view data that satisfies
// condition A (a prepared in-flight proposal must be decided) while telling the
// others a set that satisfies condition B (no in-flight, propose fresh).
//
// The replicas must not diverge. Condition A2 may only be backed by nodes that
// actually declared InFlightPrepared -- counting a node that merely holds a
// proposal in-flight lets the leader fake a quorum and fork the log.
func TestNoForkOnNewViewEquivocation(t *testing.T) {
	runNoForkOnNewViewEquivocation(t, false)
}

func TestNoForkOnNewViewEquivocationRealCrypto(t *testing.T) {
	runNoForkOnNewViewEquivocation(t, true)
}

func runNoForkOnNewViewEquivocation(t *testing.T, realCrypto bool) {
	network := NewNetwork()
	defer network.Shutdown()

	testDir, err := os.MkdirTemp("", t.Name())
	assert.NoError(t, err)
	defer os.RemoveAll(testDir)

	const N = 4
	nodes := make([]*App, 0, N)
	for i := 1; i <= N; i++ {
		nodes = append(nodes, newNode(uint64(i), network, t.Name(), testDir, false, 0))
	}
	n := func(id uint64) *App { return nodes[id-1] }

	var keys *equivocationKeys
	if realCrypto {
		keys = newEquivocationKeys([]uint64{1, 2, 3, 4})
	}

	var mu sync.Mutex
	phase := 1 // 1: build in-flight; 2: view change; 3: split
	var node1VD, node2VD, node3VD, node4VD *protos.SignedViewData
	// heldNode1Commit is node 1's genuine commit for v1 (view 0, seq 1) that the
	// network buffers on the 1->4 link in phase 1 and releases in phase 3.
	var heldNode1Commit *protos.Message
	node1Prepared := make(chan struct{})
	node1PreparedOnce := sync.Once{}
	node4RecommitOnce := sync.Once{}

	// The phase-2 view change is driven by ticks (honest nodes time out on the silent
	// leader and emit their own ViewChange). Stop feeding ticks the moment view 1 is
	// established, so no further leader-timeout cascade can heal v1.
	stopTicks := make(chan struct{})
	var stopTicksOnce sync.Once
	stopTicking := func() { stopTicksOnce.Do(func() { close(stopTicks) }) }

	getPhase := func() int { mu.Lock(); defer mu.Unlock(); return phase }
	setPhase := func(p int) { mu.Lock(); phase = p; mu.Unlock() }

	// Nodes 2,3: never reach a prepare quorum (only node 1 prepares v1); drop node
	// 1's heartbeats in phase 2+ (provoke the timeout); node 2 drops node 1's
	// ViewData (so node 2 is condition B).
	dropIncoming := func(self uint64) func(*protos.Message) bool {
		return func(m *protos.Message) bool {
			p := getPhase()
			if p == 1 && m.GetPrepare() != nil {
				return true
			}
			if p >= 2 && m.GetHeartBeat() != nil {
				return true
			}
			if p >= 2 && self == 2 && m.GetViewData() != nil && m.GetViewData().GetSigner() == 1 {
				return true
			}
			return false
		}
	}
	n(2).LoseMessages(dropIncoming(2))
	n(3).LoseMessages(dropIncoming(3))

	// Node 4 is not disconnected. Its own inbound filter buffers node 1's genuine
	// commit and
	// otherwise keeps node 4 out of the v1 round in phase 1 (its ViewData stays nil,
	// as if it is simply behind). In phase 2 it behaves like the others.
	n(4).LoseMessages(func(m *protos.Message) bool {
		if getPhase() == 1 {
			if cm := m.GetCommit(); cm != nil && cm.GetView() == 0 && cm.GetSeq() == 1 && cm.GetSignature().GetSigner() == 1 {
				mu.Lock()
				if heldNode1Commit == nil {
					heldNode1Commit = proto.Clone(m).(*protos.Message) // node 1's own bytes, held by the network
				}
				mu.Unlock()
			}
			return true // phase 1: node 4 joins nothing (delivery to it is withheld)
		}
		return m.GetHeartBeat() != nil // phase 2+: only heartbeats dropped, like the others
	})

	// Capture every genuinely-signed ViewData off the wire (needed to build the
	// condition-A subset and, under real crypto, node 2's own c2 over v1's proposal).
	captureVD := func(tgt uint64, m *protos.Message) {
		vd := m.GetViewData()
		if vd == nil {
			return
		}
		mu.Lock()
		switch vd.GetSigner() {
		case 1:
			if node1VD == nil {
				node1VD = proto.Clone(vd).(*protos.SignedViewData)
			}
		case 2:
			if node2VD == nil {
				node2VD = proto.Clone(vd).(*protos.SignedViewData)
			}
		case 3:
			if node3VD == nil {
				node3VD = proto.Clone(vd).(*protos.SignedViewData)
			}
		case 4:
			if node4VD == nil {
				node4VD = proto.Clone(vd).(*protos.SignedViewData)
			}
		}
		mu.Unlock()
	}
	n(1).MutateSend(2, captureVD)
	n(1).MutateSend(3, captureVD)
	n(3).MutateSend(2, captureVD)
	n(4).MutateSend(2, captureVD)

	// Byzantine equivocation: node 2 rewrites its outgoing NewView per target.
	// Nodes 1,3 get node 2's genuine condition-B NewView (quorum {2,3,4}, all
	// unprepared) -> they decide v2. Node 4 gets a condition-A NewView over the
	// distinct genuine subset {2,1,4} -> it re-commits v1. Node 4 is also restricted
	// to NewView+Commit so it never adopts node 2's v2 pre-prepare.
	//
	// The subset deliberately includes node 2's own view data: the NewView
	// container is assembled by the leader and arrives over the network, so a
	// receiver only has the sender check to go on. Leaving the leader out of its
	// own NewView is a trivially detectable forgery, so we take the leader's entry
	// from the message it is really sending (processViewDataMsg always puts its own
	// signed view data first) and equivocate only over WHICH honest nodes back the
	// in-flight proposal: nodes 1 and 4, excluding the honest node 3.
	var node4Isolated sync.Once
	forge := func(target uint64, m *protos.Message) {
		nv := m.GetNewView()
		if nv == nil || target != 4 {
			return
		}
		var vd1, vd4 *protos.SignedViewData
		for range 30 {
			mu.Lock()
			vd1, vd4 = node1VD, node4VD
			mu.Unlock()
			if vd1 != nil && vd4 != nil {
				break
			}
			time.Sleep(50 * time.Millisecond)
		}
		if vd1 == nil || vd4 == nil {
			return
		}
		// node 2's genuine, correctly signed view data, taken from the message it is
		// broadcasting. Node 2 never sends its own ViewData to anyone else (it
		// registers the vote locally), so it cannot be captured off the wire.
		leaderVD := nv.SignedViewData[0]
		if leaderVD == nil || leaderVD.GetSigner() != 2 {
			return
		}
		nv.SignedViewData = []*protos.SignedViewData{leaderVD, vd1, vd4}
		node4Isolated.Do(func() {
			n(4).LoseMessages(func(mm *protos.Message) bool {
				switch mm.GetContent().(type) {
				case *protos.Message_NewView, *protos.Message_Commit:
					return false // let the condition-A NewView and the buffered/own commits through
				default:
					return true
				}
			})
			t.Log("  [isolate] node 4 restricted to NewView+Commit — it cannot adopt v2")
			stopTicking() // view 1 is established (node 2's NewView is going out); freeze the schedule
		})
		t.Log("  [equivocate] node 2 -> node 4: condition-A NewView with genuine signers [2 1 4] (leader included)")
	}
	for _, target := range []uint64{1, 3, 4} {
		n(2).MutateSend(target, func(tgt uint64) func(uint64, *protos.Message) {
			return func(_ uint64, m *protos.Message) { forge(tgt, m) }
		}(target))
	}

	// Log hooks for phase synchronisation.
	hook := func(a *App, on func(string)) {
		base := a.logger.Desugar()
		a.logger = base.WithOptions(zap.Hooks(func(e zapcore.Entry) error { on(e.Message); return nil })).Sugar()
	}
	hook(n(1), func(msg string) {
		if strings.Contains(msg, "collected") && strings.Contains(msg, "prepares") {
			node1PreparedOnce.Do(func() { close(node1Prepared) })
		}
	})
	for _, a := range nodes {
		id := a.ID
		hook(a, func(msg string) {
			if id == 4 && strings.Contains(msg, "creating a view") {
				node4RecommitOnce.Do(func() {
					t.Log("  [node 4] entered condition-A: re-committing the in-flight v1")
					go releaseNode1CommitAndByz(t, network, n, keys, realCrypto, &mu, &heldNode1Commit, &node1VD)
				})
			}
		})
	}

	for _, a := range nodes {
		a.heartbeatTime = make(chan time.Time, 1)
		a.viewChangeTime = make(chan time.Time, 1)
		a.Setup()
		a.Consensus.Config.SpeedUpViewChange = true
		if realCrypto {
			w := &equivocationSigner{App: a, id: a.ID, keys: keys}
			a.Consensus.Signer = w
			a.Consensus.Verifier = w
		}
	}
	startNodes(nodes, network)

	// Phase 1 — build the prepared-but-undecided in-flight state. Node 1 prepares
	// and commits v1 (broadcasting the commit to all, node 4 included); the network
	// holds node 4's copy. Node 4 stays out of the round, its ViewData nil.
	n(1).Submit(Request{ID: "v1", ClientID: "alice"})
	select {
	case <-node1Prepared:
		t.Log("phase 1: node 1 prepared v1 (commit broadcast; node 4's copy held by the network)")
	case <-time.After(10 * time.Second):
		t.Fatal("phase 1: node 1 never became prepared")
	}
	time.Sleep(1 * time.Second)
	assertNoDelivery(t, nodes, "phase 1")
	mu.Lock()
	heldOK := heldNode1Commit != nil
	mu.Unlock()
	if !heldOK {
		t.Fatal("phase 1: node 1's genuine commit was never observed on the 1->4 link")
	}

	// Phase 2 — drive the cluster into view 1 (node 2 leads) BY TIME.
	// Node 1's heartbeats are dropped, so nodes 2,3,4 each suspect the silent leader
	// and emit their OWN ViewChange(nextView=1) on timeout — exactly the message an
	// honest replica sends in a real run. The harness only advances their logical
	// clocks (heartbeatTime/viewChangeTime are stubbed above).
	// SpeedUpViewChange lets them adopt view 1 once
	// f+1 complaints exist.
	setPhase(2)
	n(2).Submit(Request{ID: "v2", ClientID: "bob"}) // node 2's fresh proposal for view 1
	defer stopTicking()
	go func() {
		base := time.Now()
		for i := 1; ; i++ {
			select {
			case <-stopTicks:
				return
			case <-time.After(80 * time.Millisecond):
				adv := base.Add(time.Duration(i) * 2 * time.Minute) // advance past the 1-minute timeouts
				for _, id := range []uint64{1, 2, 3, 4} {
					select {
					case n(id).heartbeatTime <- adv:
					default:
					}
					select {
					case n(id).viewChangeTime <- adv:
					default:
					}
				}
			}
		}
	}()

	// Only nodes 1 and 4 have to be captured here: node 2's own view data rides
	// along in the NewView it is broadcasting (see forge), so the subset
	// {2,1,4} is complete once 1 and 4 are in hand.
	captured := waitFor(8*time.Second, func() bool {
		mu.Lock()
		defer mu.Unlock()
		return node1VD != nil && node4VD != nil
	})
	mu.Lock()
	t.Logf("phase 2: captured ViewData 1:%v 2:%v 3:%v 4:%v (need 1,4 for condition A; node 2's comes from the NewView)",
		node1VD != nil, node2VD != nil, node3VD != nil, node4VD != nil)
	mu.Unlock()
	if !captured {
		t.Log("phase 2: condition-A subset {2,1,4} not fully captured; equivocation may not form")
	}

	// Phase 3 — the split plays out. Node 4 tries to re-commit v1 at sequence 1
	// while nodes 1,3 decide v2 at sequence 1. That would be a fork, so it must
	// NOT happen: condition A2 only accepts a NewView backed by f+1 nodes that
	// really prepared the in-flight proposal, and only node 1 ever prepared v1.
	setPhase(3)
	fork, detail := watchFork(12*time.Second, nodes)
	t.Log(detail)
	if fork {
		t.Fatalf("F1 reproduced: two honest replicas delivered different values at the same sequence\n%s", detail)
	}
	t.Log("*** F1 not reproduced: every replica agreed at every sequence ***")
}

// releaseNode1CommitAndByz completes node 4's in-flight recovery quorum for v1
// (Quorum-1 = 2 votes besides node 4's own), from the two sources one Byzantine
// node can obtain without forging an honest signature:
//
//	node 1's genuine commit — released from the network buffer, unchanged, via the
//	                          transport (network.send), i.e. delivered late on node
//	                          1's link; node 1 never re-sends it here;
//	c2 = node 2's own commit for v1 (node 2 signing under its own key).
//
// Node 3 (honest, never prepared v1) is deliberately not a source.
func releaseNode1CommitAndByz(t *testing.T, network *Network, n func(uint64) *App, keys *equivocationKeys, realCrypto bool, mu *sync.Mutex, heldNode1Commit **protos.Message, node1VD **protos.SignedViewData) {
	// Unblock commitInFlightProposal's "wait two ticks" gate.
	n(4).viewChangeTime <- time.Now()
	n(4).viewChangeTime <- time.Now()

	mu.Lock()
	held := *heldNode1Commit
	vd1raw := *node1VD
	mu.Unlock()
	if held == nil {
		t.Log("  [node 4] no buffered node-1 commit to release!")
		return
	}

	// Node 2's own commit for v1 (its Byzantine action) — built over the same
	// proposal, signed with node 2's own key under real crypto.
	c2 := proto.Clone(held).(*protos.Message)
	if realCrypto {
		vd := &protos.ViewData{}
		if err := proto.Unmarshal(vd1raw.GetRawViewData(), vd); err != nil {
			t.Errorf("node 4: cannot unmarshal node 1's view-data: %v", err)
			return
		}
		ifp := vd.GetInFlightProposal()
		v1types := types.Proposal{
			Header:               ifp.GetHeader(),
			Metadata:             ifp.GetMetadata(),
			Payload:              ifp.GetPayload(),
			VerificationSequence: int64(ifp.GetVerificationSequence()),
		}
		sig2 := (&equivocationSigner{App: n(2), id: 2, keys: keys}).SignProposal(v1types, held.GetCommit().GetSignature().GetMsg())
		if cc := c2.GetCommit(); cc != nil {
			cc.Signature = &protos.Signature{Signer: 2, Value: sig2.Value, Msg: sig2.Msg}
		}
	} else {
		if cc := c2.GetCommit(); cc != nil && cc.Signature != nil {
			cc.Signature.Signer = 2
		}
	}

	for range 6 {
		// The network releases node 1's buffered genuine commit to node 4 (raw
		// transport, source = node 1). This is delayed delivery, not a new send by
		// node 1 — node 1 has since moved on to view 1.
		network.send(1, 4, proto.Clone(held).(*protos.Message))
		// Node 2 (Byzantine) sends its own commit for v1.
		network.GetByID(2).SendConsensus(4, proto.Clone(c2).(*protos.Message))
		time.Sleep(150 * time.Millisecond)
		select { // keep the in-flight view's tick loop alive (no timeout)
		case n(4).viewChangeTime <- time.Now():
		default:
		}
	}
	t.Log("  [node 4] re-commit quorum: node 1's genuine commit (network-delayed) + node 2's own (Byzantine)")
}

// ---- helpers (same as the base PoC) ----

func assertNoDelivery(t *testing.T, nodes []*App, phase string) {
	for _, a := range nodes {
		select {
		case r := <-a.Delivered:
			t.Fatalf("%s: node %d unexpectedly delivered %v", phase, a.ID, r)
		default:
		}
	}
	t.Logf("%s: no node delivered (v1 undecided) — good", phase)
}

func waitFor(d time.Duration, cond func() bool) bool {
	deadline := time.Now().Add(d)
	for time.Now().Before(deadline) {
		if cond() {
			return true
		}
		time.Sleep(100 * time.Millisecond)
	}
	return cond()
}

// watchFork drains Delivered channels and reports whether two nodes delivered
// different values at the same decided sequence (from the proposal's
// ViewMetadata, not arrival order — the fork is v1 and v2 both at sequence 1).
func watchFork(d time.Duration, nodes []*App) (bool, string) {
	bySeq := map[int]map[string][]uint64{}
	maxSeq := 0
	deadline := time.Now().Add(d)
	for time.Now().Before(deadline) {
		for _, a := range nodes {
			select {
			case r := <-a.Delivered:
				val := recordValue(r)
				s := decidedSeq(r)
				if s > maxSeq {
					maxSeq = s
				}
				if bySeq[s] == nil {
					bySeq[s] = map[string][]uint64{}
				}
				bySeq[s][val] = append(bySeq[s][val], a.ID)
			default:
			}
		}
		time.Sleep(50 * time.Millisecond)
	}
	fork := false
	out := "deliveries by decided sequence:\n"
	for i := -1; i <= maxSeq; i++ {
		if bySeq[i] == nil {
			continue
		}
		out += "  seq " + strconv.Itoa(i) + ": "
		for v, ids := range bySeq[i] {
			out += fmt.Sprintf("%s->%v ", v, ids)
		}
		out += "\n"
		if len(bySeq[i]) > 1 {
			fork = true
		}
	}
	return fork, out
}

func decidedSeq(r *AppRecord) int {
	if r == nil || len(r.Metadata) == 0 {
		return -1
	}
	md := &protos.ViewMetadata{}
	if err := proto.Unmarshal(r.Metadata, md); err != nil {
		return -1
	}
	return int(md.LatestSequence)
}

func recordValue(r *AppRecord) string {
	if r == nil || r.Batch == nil {
		return "<nil>"
	}
	s := ""
	for _, req := range r.Batch.Requests {
		rq := requestFromBytes(req)
		s += rq.ClientID + "/" + rq.ID
	}
	return s
}

// ---- real ed25519 signing/verification, bound to the signer's ID ----

type equivocationKeys struct {
	priv map[uint64]ed25519.PrivateKey
	pubs map[uint64]ed25519.PublicKey
}

func newEquivocationKeys(ids []uint64) *equivocationKeys {
	k := &equivocationKeys{
		priv: make(map[uint64]ed25519.PrivateKey, len(ids)),
		pubs: make(map[uint64]ed25519.PublicKey, len(ids)),
	}
	for _, id := range ids {
		seed := make([]byte, ed25519.SeedSize)
		seed[0] = byte(id)
		priv := ed25519.NewKeyFromSeed(seed)
		k.priv[id] = priv
		k.pubs[id] = priv.Public().(ed25519.PublicKey)
	}
	return k
}

// f1Crypto wraps an *App and replaces only the no-op signing/verification with
// real ed25519; every other consensus callback falls through to the App.
type equivocationSigner struct {
	*App
	id   uint64
	keys *equivocationKeys
}

func (c *equivocationSigner) Sign(msg []byte) []byte { return ed25519.Sign(c.keys.priv[c.id], msg) }

func (c *equivocationSigner) SignProposal(proposal types.Proposal, aux []byte) *types.Signature {
	msg := append([]byte(proposal.Digest()), aux...)
	return &types.Signature{ID: c.id, Value: ed25519.Sign(c.keys.priv[c.id], msg), Msg: aux}
}

func (c *equivocationSigner) VerifySignature(s types.Signature) error {
	pub, ok := c.keys.pubs[s.ID]
	if !ok {
		return fmt.Errorf("no public key for signer %d", s.ID)
	}
	if !ed25519.Verify(pub, s.Msg, s.Value) {
		return fmt.Errorf("invalid ed25519 signature attributed to %d", s.ID)
	}
	return nil
}

// VerifyConsenterSig checks a commit/prepare signature against the signer's own
// public key over (digest || aux); a signature by node X cannot pass as node Y.
func (c *equivocationSigner) VerifyConsenterSig(s types.Signature, proposal types.Proposal) ([]byte, error) {
	pub, ok := c.keys.pubs[s.ID]
	if !ok {
		return nil, fmt.Errorf("no public key for signer %d", s.ID)
	}
	msg := append([]byte(proposal.Digest()), s.Msg...)
	if !ed25519.Verify(pub, msg, s.Value) {
		return nil, fmt.Errorf("invalid ed25519 consenter signature attributed to %d", s.ID)
	}
	return s.Msg, nil
}
