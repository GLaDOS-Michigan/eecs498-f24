include "UtilitiesLibrary.dfy"


//Question 4:

//This area is appendix
module Events {

    datatype Event =

        | Increment
        | NoOp

}

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

    datatype Constants = Constants()

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

module Network {

    import opened UtilitiesLibrary

    import opened Types

    type HostId = nat

    datatype Constants = Constants    // no constants for network

    datatype Variables = Variables(inFlightMessages:set<Message>)

    ghost predicate Init(c: Constants, v: Variables)

    {

        && v.inFlightMessages == {}

    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)

    {

        // Only allow receipt of a message if we've seen it has been sent.

        && (msgOps.recv.Some? ==> msgOps.recv.value in v.inFlightMessages)
        && (msgOps.send.Some? ==> msgOps.send.value !in v.inFlightMessages)

        // Record the sent message, if there was one.

        && v'.inFlightMessages ==

            v.inFlightMessages

                // remove a message "used up" by receipt

                - (if msgOps.recv.None? then {} else { msgOps.recv.value })

                // add a new message supplied by send

                + (if msgOps.send.None? then {} else { msgOps.send.value })

    }

}

// The (trusted) model of the distributed system: hosts don't share memory. Each

// takes its steps independently, interleaved in nondeterministic order with others.

// They only communicate through the network, and obey the communication model

// established by the Network model.

// This is given to you; it can be reused for just about any shared-nothing-concurrency

// protocol model.

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


//This is the question from the exam
module ExamTypes {

    import opened UtilitiesLibrary

    type HostId = nat

    datatype ExamMessage = TransferMessage()

    datatype ExamMessageOps = ExamMessageOps(recv:Option<ExamMessage>, send:Option<ExamMessage>)

}

module ExamHost {

    import opened Events

    import opened ExamTypes

    import opened UtilitiesLibrary

    datatype Constants = Constants(idx:nat, numHosts: nat)

    datatype Variables = Variables(

        holdingCounter: bool,

        counterValue: nat
    )

    ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>)

    {

        true

    }

    ghost predicate LocalIncrement(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: ExamMessageOps) {

        true

    }

    ghost predicate SendCounter(c: Constants, v: Variables, v': Variables, evt: Event, recipentIdx: nat, msgOps: ExamMessageOps) {

        true

    }

    ghost predicate ReceiveCounter(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: ExamMessageOps) {
        true
    }


    datatype Step = Step(idx:nat) //NextStep an idx is needed for the transition


    ghost predicate NextStep(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: ExamMessageOps, step: Step)

    {

        match evt {

            case Increment => LocalIncrement(c, v, v', evt, msgOps)

            case NoOp => SendCounter(c, v, v', evt, step.idx, msgOps) || ReceiveCounter(c, v, v', evt, msgOps)

        }

    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: ExamMessageOps)

    {

        exists step :: NextStep(c, v, v', evt, msgOps, step)

    }

}

module ExamNetwork {

    import opened UtilitiesLibrary

    import opened ExamTypes

    type HostId = nat

    datatype Constants = Constants    // no constants for network

    datatype Variables = Variables(sentMsgs:set<ExamMessage>)

    ghost predicate Init(c: Constants, v: Variables)

    {

        && v.sentMsgs == {}

    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: ExamMessageOps)

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

module ExamDistributedSystem {

    import opened Events

    import opened UtilitiesLibrary

    import opened ExamTypes

    import ExamNetwork

    import ExamHost

    datatype Constants = Constants(

        totalKeys: nat,

        hosts: seq<ExamHost.Constants>,

        network: ExamNetwork.Constants)

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

        hosts: seq<ExamHost.Variables>,

        network: ExamNetwork.Variables

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

        && ExamHost.GroupInit(c.hosts, v.hosts)

        && ExamNetwork.Init(c.network, v.network)

    }

    ghost predicate HostAction(c: Constants, v: Variables, v': Variables, evt: Event, hostid: HostId, msgOps: ExamMessageOps)

    {

        && v.WF(c)

        && v'.WF(c)

        && c.ValidHostId(hostid)

        && ExamHost.Next(c.hosts[hostid], v.hosts[hostid], v'.hosts[hostid], evt, msgOps)

        && ExamNetwork.Next(c.network, v.network, v'.network, msgOps)

        // all other hosts UNCHANGED

        && (forall otherHost:nat | c.ValidHostId(otherHost) && otherHost != hostid :: v'.hosts[otherHost] == v.hosts[otherHost])

    }

    datatype Step =

        | HostActionStep(hostid: HostId, msgOps: ExamMessageOps)

    ghost predicate NextStep(c: Constants, v: Variables, v': Variables, evt: Event, step: Step)

    {

        && HostAction(c, v, v', evt, step.hostid, step.msgOps)

        // network agrees recv has been sent and records sent

        && ExamNetwork.Next(c.network, v.network, v'.network, step.msgOps)

    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event)

    {

        exists step :: NextStep(c, v, v', evt, step)

    }

}
abstract module ExamRefinementTheorem {

    import opened Events

    import DistributedSystem

    import ExamDistributedSystem


    ghost function ConstantsAbstraction(c: ExamDistributedSystem.Constants) : DistributedSystem.Constants

        requires c.WF()

    ghost function VariablesAbstraction(c: ExamDistributedSystem.Constants, v: ExamDistributedSystem.Variables) : DistributedSystem.Variables

        requires v.WF(c)

    ghost predicate Inv(c: ExamDistributedSystem.Constants, v: ExamDistributedSystem.Variables)

    lemma RefinementInit(c: ExamDistributedSystem.Constants, v: ExamDistributedSystem.Variables)

        requires ExamDistributedSystem.Init(c, v)

        ensures Inv(c, v)

        ensures DistributedSystem.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))

    

    lemma RefinementNext(c: ExamDistributedSystem.Constants, v: ExamDistributedSystem.Variables, v': ExamDistributedSystem.Variables, evt: Event)

        requires ExamDistributedSystem.Next(c, v, v', evt)

        requires Inv(c, v)

        ensures Inv(c, v') 

        ensures DistributedSystem.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt)

}

module ExamRefinementProof refines ExamRefinementTheorem {

    import Host

    import ExamHost

    import Network

    import ExamNetwork

    import opened Types

    import opened ExamTypes

    import opened UtilitiesLibrary


    ghost function ConstantsAbstraction(c: ExamDistributedSystem.Constants) : DistributedSystem.Constants

//        requires c.WF()   (implied from abstract module)

    {

        DistributedSystem.Constants([], Network.Constants)

    }




    ghost function VariablesAbstraction(c: ExamDistributedSystem.Constants, v: ExamDistributedSystem.Variables) : DistributedSystem.Variables

//        requires v.WF(c)  (implied from abstract module)

    {   
       DistributedSystem.Variables([], Network.Variables({}))

    }

    ghost predicate Inv(c: ExamDistributedSystem.Constants, v: ExamDistributedSystem.Variables)

    {
        true
    }

    lemma RefinementInit(c: ExamDistributedSystem.Constants, v: ExamDistributedSystem.Variables)

//        requires DistributedSystem.Init(c, v)     (implied from abstract module)

//        ensures Inv(c, v)                         (implied from abstract module)

//        ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))    (implied from abstract module)

    {

        

    }
    

    lemma RefinementNext(c: ExamDistributedSystem.Constants, v: ExamDistributedSystem.Variables, v': ExamDistributedSystem.Variables, evt: Event)

//        requires DistributedSystem.Next(c, v, v', evt)

//        requires Inv(c, v)

//        ensures Inv(c, v') 

//        ensures Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt) || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && evt == NoOp)

    {

    
    }
}

