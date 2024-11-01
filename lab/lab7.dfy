include "UtilitiesLibrary.dfy"

module Events {
    datatype Event =
        | Reduce
        | NoOp
}

//Some helpers you might find helpful!
module helpers {
    import opened UtilitiesLibrary
    ghost function Sum(arr: seq<int>) : int {
        if |arr| == 0 then 0 else arr[0] + Sum(arr[1..])
    }

    lemma sumLemma1(seqA: seq<int>, seqB: seq<int>)
        ensures Sum(seqA + seqB) == Sum(seqA) + Sum(seqB)
    {
    }
    lemma sumLemma2(seqA: seq<int>, seqB: seq<int>)
        ensures Sum(seqA) + Sum(seqB) == Sum(seqB) + Sum(seqA)
    {

    }
    ghost function OptionSum(arr: seq<Option<int>>) : int
        requires forall i:nat | i < |arr| :: arr[i].Some?
    {
        if |arr| == 0 then 0 else arr[0].value + OptionSum(arr[1..])
    }
}
module Spec {
    import opened Events
    import opened helpers

    datatype Constants = Constants(arr : seq<int>)

    datatype Variables = Variables(
        sum: int
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

module Types {
    import opened UtilitiesLibrary

    type HostId = nat

    datatype Message = TransferSum(sum :int, idx: nat)

    datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
}

module Host {
    import opened Events
    import opened Types
    import opened UtilitiesLibrary
    import opened helpers

    datatype Constants = Constants(idx: nat, grp_size: nat, arr : seq<int>)
    {
        ghost predicate WF(){
            && idx < grp_size
            && grp_size > 0
        }
    }

    datatype Variables = Variables(
        globalSum: Option<int>,
        sum: Option<int>,
        peerSums : seq<Option<int>>
    )
    {
        ghost predicate WF(c: Constants){
            && c.WF()
            && |peerSums| == if c.idx == 0 then c.grp_size else 0
        }
    }


    ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>)
    {
        && (|grp_c| > 0)
        && (|grp_c| == |grp_v|)
        && (forall idx | 0 <= idx < |grp_c| :: 
            && (grp_c[idx].idx == idx && grp_c[idx].grp_size == |grp_c|)
            && (grp_v[idx].WF(grp_c[idx])))
    }
    ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>)
    {
        && (GroupWF(grp_c, grp_v))
        && (forall idx | 0 <= idx < |grp_v| :: 
            && (grp_v[idx].sum.None?)
            && (forall i:nat | i < |grp_v[idx].peerSums| :: grp_v[idx].peerSums[i].None?)
            && (grp_v[idx].globalSum.None?))
    }


    ghost predicate LocalSum(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && v.WF(c)
        && v'.sum == Some(Sum(c.arr))
        && v'.peerSums == (if c.idx == 0 then v.peerSums[0 := Some(Sum(c.arr))] else v.peerSums)
        && v'.globalSum == v.globalSum
        && msgOps == MessageOps(None, None)
    }
    ghost predicate SendSum(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && v.WF(c)
        && c.idx > 0
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
            case NoOp => LocalSum(c, v, v', evt, msgOps) || SendSum(c, v, v', evt, msgOps) || RecvSum(c, v, v', evt, msgOps)
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

        // Record the sent message, if there was one.
        && v'.sentMsgs ==
            v.sentMsgs
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


    


    ghost function ConstantsAbstraction(c: DistributedSystem.Constants) : Spec.Constants
    {
        Spec.Constants([])
    }
    ghost function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : Spec.Variables
//        requires v.WF(c)
    {   
        Spec.Variables(sum := 0)
    }



    ghost predicate Inv(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
    {
        true
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


    }
}
