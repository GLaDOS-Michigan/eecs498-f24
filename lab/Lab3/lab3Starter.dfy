//Helpful for modelling the queue
datatype Permission = NoPermission | PermissionGranted

//Define Constant, Variables
datatype Constants = Constants()
datatype Variables = Variables()

//Describe Initial State
predicate Init(c:Constants, v:Variables)
{
    true
}

//Define the following transitions
predicate carJoinQueueOnLeft(c:Constants, v:Variables, v':Variables)
{
    true
}

predicate carJoinQueueOnRight(c:Constants, v:Variables, v':Variables)
{
    true
}

predicate GrantPermissionToCarFromLeft(c:Constants, v:Variables, v':Variables)
{
    true
}

predicate GrantPermissionToCarFromRight(c:Constants, v:Variables, v':Variables)
{
   true
}

predicate CarComingOnBridgeFromLeft(c:Constants, v:Variables, v':Variables)
{
    true
}

predicate CarComingOnBridgeFromRight(c:Constants, v:Variables, v':Variables)
{
    true
}

predicate CarOnTheBridgePassThroughTheBridge(c:Constants, v:Variables, v':Variables)
{
    true
}

//This predicate describes all possible transitions
predicate Next(c:Constants, v:Variables, v':Variables)
{
    true
}

//Define the set of safe states
predicate Safety(c:Constants, v:Variables)
{
    true
}

//Think about whether this is true? Why or why not. No need to try implementing
lemma SafetyProof()
    ensures forall c,v | Init(c, v) :: Safety(c, v)
    ensures forall c,v,v' | Safety(c, v) && Next(c, v, v') :: Safety(c, v')
{
    
}