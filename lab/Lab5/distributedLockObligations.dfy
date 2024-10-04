// Note that we include the model of exercise01, so you should write your 
// spec accordingly. Of course, that also means double-checking that your
// model performs all actions as described.
include "distributedLockProtocol.dfy"

module Obligations {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem

  // Define Safety
  ghost predicate Safety(c: Constants, v: Variables)
    requires v.WF(c)
  {
    true
  }
}
