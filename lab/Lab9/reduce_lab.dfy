include "UtilitiesLibrary.dfy"
include "Types.dfy"
include "Events.dfy"

module helpers {
    import opened UtilitiesLibrary
    ghost function Sum(arr: seq<nat>) : nat {
        if |arr| == 0 then 0 else arr[0] + Sum(arr[1..])
    }

    lemma sumLemma1(seqA: seq<nat>, seqB: seq<nat>)
        ensures Sum(seqA + seqB) == Sum(seqA) + Sum(seqB)
    {
        if(|seqA| == 0){
            assert seqA + seqB == seqB;
            assert Sum(seqA + seqB) == Sum(seqA) + Sum(seqB);
        }
        else{
            assert Sum(seqA[1..] + seqB) == Sum(seqA[1..]) + Sum(seqB);
            assert [seqA[0]] + (seqA[1..] + seqB) == seqA + seqB;
            assert  seqA[0] + Sum(seqA[1..] + seqB) == Sum(seqA + seqB);
        }
    }
    lemma sumLemma2(seqA: seq<nat>, seqB: seq<nat>)
        ensures Sum(seqA) + Sum(seqB) == Sum(seqB) + Sum(seqA)
    {

    }
    ghost function OptionSum(arr: seq<Option<nat>>) : nat
        requires forall i:nat | i < |arr| :: arr[i].Some?
    {
        if |arr| == 0 then 0 else arr[0].value + OptionSum(arr[1..])
    }
}
module Spec {
    import opened Events
    import opened helpers

    datatype Constants = Constants(arr : seq<nat>)

    datatype Variables = Variables(
        sum: nat
    )

    ghost predicate Init(c: Constants, v: Variables) {
        && v.sum == 0
    }




    ghost predicate GetSum(c: Constants, v: Variables, v': Variables) {
        && v' == v.(sum := Sum(c.arr)) 
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event) {
        match evt {
            case Reduce => GetSum(c, v, v')
            case NoOp => v' == v
        }
    }

}

////////////////////////////////////////////////////////////////////////////


module Host {
    import opened Events
    import opened Types
    import opened UtilitiesLibrary
    import opened helpers

    datatype Constants = Constants(idx: nat, grp_size: nat, arr : seq<nat>)
    {
        ghost predicate WF(){
            && idx < grp_size
            && grp_size > 0
        }
    }

    datatype Variables = Variables(
        globalSum: Option<nat>,
        sum: Option<nat>,
        peerSums : seq<Option<nat>>
    )
    {
        ghost predicate WF(c: Constants){
            && c.WF()
            && |peerSums| == if c.idx == 0 then c.grp_size else 0
        }
    }

    ghost predicate Init(c: Constants, v: Variables){
        && v.WF(c)
        && (v.sum.None?)
        && (forall i:nat | i < |v.peerSums| :: v.peerSums[i].None?)
        && (v.globalSum.None?)
    }

    ghost predicate WFinGroup(c: Constants, v: Variables, idx: nat, grp_size: nat){
        && v.WF(c)
        && c.idx == idx
        && c.grp_size == grp_size
    }

    ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>)
    {
        && (|grp_c| > 0)
        && (|grp_c| == |grp_v|)
        && (forall idx | 0 <= idx < |grp_c| :: 
            && WFinGroup(grp_c[idx], grp_v[idx], idx, |grp_c|))
    }
    ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>)
    {
        && (GroupWF(grp_c, grp_v))
        && (forall idx | 0 <= idx < |grp_v| :: 
            Init(grp_c[idx], grp_v[idx]))
    }


    ghost predicate LocalSum(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && v.WF(c)
        && v'.sum == Some(Sum(c.arr))
        && v'.peerSums == v.peerSums
        && v'.globalSum == v.globalSum
        && msgOps == MessageOps(None, None)
    }
    ghost predicate SendSum(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && v.WF(c)
        && v.sum.Some?
        && v' == v
        && msgOps.recv.None?
        && msgOps.send.Some?
        && msgOps.send.value == TransferSum(v.sum.value, c.idx)
    }

    ghost predicate RecvSum(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && v.WF(c)
        && c.idx == 0
        && msgOps.recv.Some?
        && msgOps.send.None?
        && msgOps.recv.value.idx < c.grp_size
        && v' == v.(peerSums := v.peerSums[msgOps.recv.value.idx := Some(msgOps.recv.value.sum)])
    }

    ghost predicate GlobalSum(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && v.WF(c)
        && c.idx == 0
        && msgOps.recv.None?
        && msgOps.send.None?
        && (forall i:nat | i < c.grp_size :: v.peerSums[i].Some?)
        && v' == v.(globalSum := Some(OptionSum(v.peerSums)))
    }


    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps)
    {
        match evt {
            case Reduce => GlobalSum(c, v, v', evt, msgOps)
            case NoOp => LocalSum(c, v, v', evt, msgOps) || SendSum(c, v, v', evt, msgOps) || RecvSum(c, v, v', evt, msgOps) || (msgOps.send.None? && v == v')
        }
    }

}

module Network {
    import opened UtilitiesLibrary
    import opened Types

    type HostId = nat

    datatype Constants = Constants    // no constants for network

    datatype Variables = Variables(sentMsgs:set<Message>)

    ghost predicate Init(c: Constants, v: Variables)
    {
        && v.sentMsgs == {}
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        // Only allow receipt of a message if we've seen it has been sent.
        && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)

//////////////////////////////////////////////////////////////////////////////
//     _     ___   ___  _  __  _   _ _____ ____  _____ 
//    | |   / _ \ / _ \| |/ / | | | | ____|  _ \| ____|
//    | |  | | | | | | | ' /  | |_| |  _| | |_) |  _|  
//    | |__| |_| | |_| | . \  |  _  | |___|  _ <| |___ 
//    |_____\___/ \___/|_|\_\ |_| |_|_____|_| \_\_____|
//
// This network model differs from project 01 and chapter 05. It is a magical
// network that prevents the host from sending a duplicate message until the
// first copy is delivered! A little unrealistic, but it'll make your proof a
// little easier. Read the following comment & conjunct.
//
//////////////////////////////////////////////////////////////////////////////

        // Only allow sending a message if there isn't a duplicate of that
        // message already sent but not yet delivered.
        // Two better approaches I didn't take:
        //    * Define the inFlightMessages as a multiset. Turns out this leads
        //        to a much more challenging definition of disjoint in the proof.
        //    * Demand the host provide nonces and do its own duplicate prevention,
        //        proving it as an invariant. Ugh, too much to ask of students.
        // So instead, for this class project, we provide this little helpful
        // leg-up from the trusted network model.
        //&& (msgOps.send.Some? ==> msgOps.send.value !in v.inFlightMessages)

        // Record the sent message, if there was one.
        && v'.sentMsgs ==
            v.sentMsgs
                // remove a message "used up" by receipt
                //- (if msgOps.recv.None? then {} else { msgOps.recv.value })
                // add a new message supplied by send
                + (if msgOps.send.None? then {} else { msgOps.send.value })
    }
}

// // The (trusted) model of the distributed system: hosts don't share memory. Each
// // takes its steps independently, interleaved in nondeterministic order with others.
// // They only communicate through the network, and obey the communication model
// // established by the Network model.
// // This is given to you; it can be reused for just about any shared-nothing-concurrency
// // protocol model.
module DistributedSystem {
    import opened Events
    import opened UtilitiesLibrary
    import opened Types
    import Network
    import Host

    datatype Constants = Constants(
        hosts: seq<Host.Constants>,
        network: Network.Constants)
    {
        ghost predicate WF() {
            0 < |hosts|
        }

        ghost predicate ValidHostId(id: HostId) {
            id < |hosts|
        }
    }

    datatype Variables = Variables(
        hosts: seq<Host.Variables>,
        network: Network.Variables
        )
    {
        ghost predicate WF(c: Constants) {
            && c.WF()
            && Host.GroupWF(c.hosts, hosts)
        }
    }

    ghost predicate Init(c: Constants, v: Variables)
    {
        && v.WF(c)
        && Host.GroupInit(c.hosts, v.hosts)
        && Network.Init(c.network, v.network)
    }

    ghost predicate HostAction(c: Constants, v: Variables, v': Variables, evt: Event, hostid: HostId, msgOps: MessageOps)
    {
        && v.WF(c)
        && v'.WF(c)
        && c.ValidHostId(hostid)
        && Host.Next(c.hosts[hostid], v.hosts[hostid], v'.hosts[hostid], evt, msgOps)
        && Network.Next(c.network, v.network, v'.network, msgOps)
        // all other hosts UNCHANGED
        && (forall otherHost:nat | c.ValidHostId(otherHost) && otherHost != hostid :: v'.hosts[otherHost] == v.hosts[otherHost])
    }

    datatype Step =
        | HostActionStep(hostid: HostId, msgOps: MessageOps)

    ghost predicate NextStep(c: Constants, v: Variables, v': Variables, evt: Event, step: Step)
    {
        && HostAction(c, v, v', evt, step.hostid, step.msgOps)
        // network agrees recv has been sent and records sent
        && Network.Next(c.network, v.network, v'.network, step.msgOps)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event)
    {
        exists step :: NextStep(c, v, v', evt, step)
    }
}

abstract module RefinementTheorem {
    import opened Events
    import Spec
    import DistributedSystem
    

    ghost function ConstantsAbstraction(c: DistributedSystem.Constants) : Spec.Constants
        requires c.WF()

    ghost function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : Spec.Variables
        requires v.WF(c)

    ghost predicate Inv(c: DistributedSystem.Constants, v: DistributedSystem.Variables)

    lemma RefinementInit(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
        requires DistributedSystem.Init(c, v)
        ensures Inv(c, v)
        ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    
    lemma RefinementNext(c: DistributedSystem.Constants, v: DistributedSystem.Variables, v': DistributedSystem.Variables, evt: Event)
        requires DistributedSystem.Next(c, v, v', evt)
        requires Inv(c, v)
        ensures Inv(c, v') 
        ensures Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt) || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && evt == NoOp)
}

module RefinementProof refines RefinementTheorem {
    import Host
    import Network
    import opened UtilitiesLibrary
    import opened Types
    import opened helpers


    

    ghost function SumOfSequences(seqs : seq<seq<nat>>) : seq<nat>{
        if |seqs| == 0 then [] else seqs[0] + SumOfSequences(seqs[1..])
    }

    ghost function hostSeqs(hosts : seq<Host.Constants>) : (arrs: seq<seq<nat>>)
        ensures |arrs| == |hosts|
        ensures forall i:nat | i < |arrs| :: arrs[i] == hosts[i].arr
    {
        if |hosts| == 0 then [] else [hosts[0].arr] + hostSeqs(hosts[1..])
    }
    lemma SumOfSeqsEqualsSumOfSums(sums : seq<Option<nat>>, arrs: seq<seq<nat>>)
        requires |sums| == |arrs|
        requires forall i:nat | i < |sums| :: sums[i].Some? && Sum(arrs[i]) == sums[i].value
        ensures Sum(SumOfSequences(arrs)) == OptionSum(sums)
        {
            if |arrs| == 0{

            }
            else{
                assert Sum(SumOfSequences(arrs[1..])) == OptionSum(sums[1..]);
                assert sums[0].value + OptionSum(sums[1..]) == OptionSum(sums);
                assert arrs[0] + SumOfSequences(arrs[1..]) == SumOfSequences(arrs);
                sumLemma1(arrs[0],SumOfSequences(arrs[1..]));
                assert Sum(arrs[0]) + Sum(SumOfSequences(arrs[1..])) == Sum(SumOfSequences(arrs));
            }
        }

    ghost function ConstantsAbstraction(c: DistributedSystem.Constants) : Spec.Constants
    {
        Spec.Constants(SumOfSequences(hostSeqs(c.hosts)))
    }
    ghost function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : Spec.Variables
//        requires v.WF(c)
    {   
        Spec.Variables(sum := if v.hosts[0].globalSum.Some? then v.hosts[0].globalSum.value else 0)
    }


    ghost predicate LocalSumCorrect(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
        requires v.WF(c)
    {
        forall idx:nat | idx < |v.hosts| :: v.hosts[idx].sum.Some? ==> 
            (v.hosts[idx].sum.value == Sum(c.hosts[idx].arr))
    }
    ghost predicate NetworkCorrect(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
        requires v.WF(c)
    {
        forall msg | msg in v.network.sentMsgs :: (
            && msg.idx < |v.hosts| 
            && v.hosts[msg.idx].sum.Some?
            && v.hosts[msg.idx].sum.value == msg.sum)
    }

    ghost predicate TableCorrect(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
        requires v.WF(c)
    {
        forall idx:nat | idx < |v.hosts| :: v.hosts[0].peerSums[idx].Some? ==> 
            (v.hosts[idx].sum.Some? && v.hosts[0].peerSums[idx].value == v.hosts[idx].sum.value)
    }
    ghost predicate GlobalSumCorrect(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
        requires v.WF(c)
    {
        v.hosts[0].globalSum.Some? ==> (
            && (forall i:nat | i < |v.hosts| :: v.hosts[0].peerSums[i].Some?)
            && (v.hosts[0].globalSum.value == OptionSum(v.hosts[0].peerSums))
        )
    }
    ghost predicate Inv(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
    {
        && v.WF(c)
        && LocalSumCorrect(c, v)
        && NetworkCorrect(c, v)
        && TableCorrect(c,v)
        && GlobalSumCorrect(c,v)
    }


    lemma RefinementInit(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
//        requires DistributedSystem.Init(c, v)
//        ensures Inv(c, v)
//        ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    {
    }
    
    lemma RefinementNext(c: DistributedSystem.Constants, v: DistributedSystem.Variables, v': DistributedSystem.Variables, evt: Event)
//        requires DistributedSystem.Next(c, v, v', evt)
//        requires Inv(c, v)
//        ensures Inv(c, v') 
//        ensures Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt) || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && evt == NoOp)
    {
      
        var step :| DistributedSystem.NextStep(c, v, v', evt, step);
        var idx := step.hostid;
        var hc := c.hosts[idx];
        var hv := v.hosts[idx];
        var hv' := v'.hosts[idx];
        assert Host.Next(hc, hv, hv', evt, step.msgOps);

        match evt {
            
            case NoOp => {
                if(step.msgOps.send.None? && hv == hv'){
                    assert Inv(c,v');
                } 
                assert Inv(c,v');
                assert (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && evt == NoOp);
            }
            case Reduce => {
                assert Inv(c,v');
                //assert |v.hosts[0].peerSums| == |hostSeqs(c.hosts)|;
                // assert forall i :nat | i < |v.hosts| :: 
                //     (&& v.hosts[0].peerSums[i].Some?
                //     && v.hosts[0].peerSums[i].value == Sum(c.hosts[i].arr));
                SumOfSeqsEqualsSumOfSums(v.hosts[0].peerSums, hostSeqs(c.hosts));
                assert Spec.GetSum(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'));
                assert Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt);
            }

        }

    }
}

