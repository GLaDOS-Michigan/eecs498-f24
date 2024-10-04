include "EchoProtocol.dfy"

module Obligations {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem

/*{*/
/*}*/

ghost predicate Safety(c: Constants, v: Variables)
    requires v.WF(c)
  {
    true
  }
}
