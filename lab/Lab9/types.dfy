include "UtilitiesLibrary.dfy"

module Types {
    import opened UtilitiesLibrary

    type HostId = nat
    newtype size_t = x:nat | 0 <= x < 2*0x8000_0000

    const MAX_SIZE_T:size_t := (2*0x8000_0000 - 1) as size_t


    datatype Message = TransferSum(sum: nat, idx: nat)

    datatype MessageImpl = TransferSumImpl(sum_size_t: size_t, idx_size_t: size_t)

    datatype MessageOpsImpl = MessageOpsImpl(recv:Option<MessageImpl>, send:Option<MessageImpl>)

    datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)

    function messageAbstract(msg_impl: MessageImpl) : (msg: Message)
    {
        TransferSum(msg_impl.sum_size_t as nat, msg_impl.idx_size_t as nat)
    }


    function messageOpsAbstract(msg_ops_impl: MessageOpsImpl) : (msg_ops: MessageOps)
    {
        MessageOps(if msg_ops_impl.recv.None? then None else Some(messageAbstract(msg_ops_impl.recv.value)),
                    if msg_ops_impl.send.None? then None else Some(messageAbstract(msg_ops_impl.send.value)))
    }

}