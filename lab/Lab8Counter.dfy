include "UtilitiesLibrary.dfy"

module Events {

    datatype Event =

        | Increment
        | NoOp

}

module Spec {

    import opened Events

    datatype Constants = Constants 

    datatype Variables = Variables(

        counter: nat

    )

    ghost predicate Init(c: Constants, v: Variables) {

        && v.counter == 0

    }

    ghost predicate IncrementCounter(c: Constants, v: Variables, v': Variables) {

        && v'.counter == v.counter + 1

    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event) {

        match evt {

            case Increment => IncrementCounter(c, v, v')

            case NoOp => v' == v

        }

    }

}

//////////////////////////////////////////////////////////////////////////////

//Below is (for the most part) the counter implementation from class. Modify this account for the relaxed assumptions.




module Types {

    import opened UtilitiesLibrary

    type HostId = nat

    datatype Message = TransferMessage(counterValue:nat)

    datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)

}

module Host {

    import opened Events

    import opened Types

    import opened UtilitiesLibrary

    datatype Constants = Constants(idx:nat, numHosts: nat)

    datatype Variables = Variables(

        holdingCounter: bool,

        counterValue: nat

    )

    ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>)

    {

        forall idx | 0 <= idx < |grp_v| :: 

            && (grp_v[idx].holdingCounter == if idx == 0 then true else false)

            && (grp_v[idx].counterValue == 0)

    }

    ghost predicate LocalIncrement(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {

        && v.holdingCounter

        && v' == v.(counterValue := v.counterValue + 1)

        && msgOps == MessageOps(None, None)

    }

    ghost predicate SendCounter(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {

        && v.holdingCounter

        && v' == v.(holdingCounter := false)

        && msgOps == MessageOps(None, Some(TransferMessage(v.counterValue)))

    }

    ghost predicate ReceiveCounter(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {

        && msgOps.recv.Some?

        && msgOps.send.None?

        && v' == v.(holdingCounter := true,  counterValue := msgOps.recv.value.counterValue)

    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps)

    {

        match evt {

            case Increment => LocalIncrement(c, v, v', evt, msgOps)

            case NoOp => SendCounter(c, v, v', evt, msgOps) || ReceiveCounter(c, v, v', evt, msgOps)

        }

    }

}





//Note: This is the normal bag of messsages model from the other assignments, NOT the one used in the counter lecture
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

        && (msgOps.send.Some? ==> msgOps.send.value !in v.sentMsgs)

        // Record the sent message, if there was one.

        && v'.sentMsgs ==

            v.sentMsgs

                + (if msgOps.send.None? then {} else { msgOps.send.value })

    }

}

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

            && 0 < |hosts|
            && (forall i:nat | i < |hosts| :: hosts[i].idx == i && hosts[i].numHosts == |hosts|)

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

            && |hosts| == |c.hosts|

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

        ensures Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt)

}


//Complete abstraction and proof
module RefinementProof refines RefinementTheorem {


    import Host


    import Network


    import opened Types

    import opened UtilitiesLibrary


    ghost function ConstantsAbstraction(c: DistributedSystem.Constants) : Spec.Constants

//        requires c.WF()   (implied from abstract module)

    {

        Spec.Constants()

    }

    ghost function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : Spec.Variables

//        requires v.WF(c)  (implied from abstract module)

    {   
       
        Spec.Variables(0)

    }


    ghost predicate Inv(c: DistributedSystem.Constants, v: DistributedSystem.Variables)

    {
        true
    }

    lemma RefinementInit(c: DistributedSystem.Constants, v: DistributedSystem.Variables)

//        requires DistributedSystem.Init(c, v)     (implied from abstract module)

//        ensures Inv(c, v)                         (implied from abstract module)

//        ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))    (implied from abstract module)

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

        if(evt.NoOp?){
            assert Inv(c,v');
            assert Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt);

        }
        else{
            assert Inv(c,v');
            assert Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt);
        }
        assert Inv(c,v');
        assert Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt);

    }



}