include "Events.dfy"
include "UtilitiesLibrary.dfy"
include "reduce_lab.dfy"


module HostImpl {
    import opened Events
    import opened Types
    import opened UtilitiesLibrary
    import opened Host
    import opened helpers


    datatype Constants = Constants(idx: size_t, grp_size: size_t, arr : seq<size_t>)
    {
        ghost predicate WF(){
            && idx < grp_size
            && grp_size > 0
            && |arr| < (MAX_SIZE_T as int)
        }
    }

    datatype Variables = Variables(
        globalSum: Option<size_t>,
        localSum: Option<size_t>,
        peerSums : seq<Option<size_t>>
    )
    {
        ghost predicate WF(c: Constants){
            && c.WF()
            && |peerSums| == if (c.idx as nat) == 0 then (c.grp_size as nat) else 0
        }
    }


    function ConstantsAbstraction(c: Constants) : (Host.Constants)
        requires c.WF()
    {
        Host.Constants(0, 0, [])
    }

    function VariablesAbstraction(c: Constants, v: Variables) : (Host.Variables)
        requires v.WF(c)
    {
        Host.Variables(None,
            None,
            [])
    }

    method InitHost(idx: size_t , grp_size: size_t, arr: seq<size_t>) returns (c: Constants, v: Variables)
        requires idx < grp_size
        requires |arr| < (MAX_SIZE_T as nat)
        ensures v.WF(c)
        ensures c.arr == arr
        ensures Host.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
        ensures Host.WFinGroup(ConstantsAbstraction(c), VariablesAbstraction(c, v), (idx as nat), (grp_size as nat))
    {
        

    }
        
    method LocalSumCompute(c: Constants, v: Variables) returns(v': Variables, evt: Event)
        requires v.WF(c)
        ensures v'.WF(c)
        ensures Host.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt, messageOpsAbstract(MessageOpsImpl(None, None)))
    {
        v' := v;
        evt := NoOp;
    }

    method SendSumCompute(c: Constants, v: Variables) returns(v': Variables, sendOp: Option<MessageImpl>, evt: Event)
        requires v.WF(c)
        ensures v'.WF(c)
        ensures Host.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt, messageOpsAbstract(MessageOpsImpl(None, sendOp)))
    {
        return v, None, NoOp;

    }

    method RecvSumCompute(c: Constants, v: Variables, msg: MessageImpl) returns(v': Variables, evt: Event)
        requires v.WF(c)
        requires msg.TransferSumImpl?
        ensures v'.WF(c)
        ensures Host.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt, messageOpsAbstract(MessageOpsImpl(Some(msg), None)))
    {
        return v, NoOp;
    }

    method GlobalSumCompute(c: Constants, v: Variables, ghost x:int) returns(v': Variables, evt: Event)
        requires v.WF(c)
        ensures v'.WF(c)
        ensures Host.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt, messageOpsAbstract(MessageOpsImpl(None, None)))
    {
        return v, NoOp;
       
    }


}