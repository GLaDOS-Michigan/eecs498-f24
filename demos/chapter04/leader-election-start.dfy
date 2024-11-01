// Each node's identifier
datatype Constants = Constants(ids: seq<nat>) {
  predicate ValidIdx(i: nat) {
    0<=i<|ids|
  }

  predicate UniqueIds() {
    (forall i:nat, j:nat | ValidIdx(i) && ValidIdx(j) && ids[i]==ids[j] :: i == j)
  }

  predicate WF() {
    && 0 < |ids|
  }
}

// The highest other identifier this node has heard about.
datatype Variables = Variables(highest_heard: seq<nat>) {
  predicate WF(c: Constants)
    requires c.WF()
  {
    && |highest_heard| == |c.ids|
  }
}

predicate Init(c: Constants, v: Variables)
{
  && c.WF()
  && c.UniqueIds()
  && v.WF(c)
    // Everyone begins having heard about nobody, not even themselves.
  && (forall i:nat | c.ValidIdx(i) :: v.highest_heard[i] == -1)
}

function max(a: nat, b: nat) : nat {
  if a > b then a else b
}

function NextIdx(c: Constants, idx: nat) : nat
  requires c.WF()
  requires c.ValidIdx(idx)
{
  (idx + 1) % |c.ids|
}

predicate Transmission(c: Constants, v: Variables, v': Variables, src: nat)
{
  && c.WF()
  && v.WF(c)
  && v'.WF(c)
  && c.ValidIdx(src)

  // Neighbor address in ring.
  && var dst := NextIdx(c, src);

  // src sends the max of its highest_heard value and its own id.
  && var message := max(v.highest_heard[src], c.ids[src]);

  // dst only overwrites its highest_heard if the message is higher.
  && var dst_new_max := max(v.highest_heard[dst], message);

  && v' == v.(highest_heard := v.highest_heard[dst := message])
}

datatype Step = TransmissionStep(src: nat)

predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
{
  match step {
    case TransmissionStep(src) => Transmission(c, v, v', src)
  }
}

predicate Next(c: Constants, v: Variables, v': Variables)
{
  exists step :: NextStep(c, v, v', step)
}

//////////////////////////////////////////////////////////////////////////////
// Spec (proof goal)
//////////////////////////////////////////////////////////////////////////////

predicate IsLeader(c: Constants, v: Variables, i: nat)
  requires c.WF()
  requires v.WF(c)
{
  && c.ValidIdx(i)
  && v.highest_heard[i] == c.ids[i]
}

predicate Safety(c: Constants, v: Variables)
  requires c.WF()
  requires v.WF(c)
{
  forall i, j | IsLeader(c, v, i) && IsLeader(c, v, j) :: i == j
}

//////////////////////////////////////////////////////////////////////////////
// Proof
//////////////////////////////////////////////////////////////////////////////

predicate Inv(c: Constants, v: Variables)
{
  && c.WF()
  && v.WF(c)
  && Safety(c, v)
}

lemma InitImpliesInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures Inv(c, v)
{
}

lemma NextPreservesInv(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
}

lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Safety(c, v)
{
}
