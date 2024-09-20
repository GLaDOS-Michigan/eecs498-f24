//Helpful for modelling the queue
datatype Permission = NoPermission | PermissionGranted

//Define Constant, Variables
datatype Constants = Constants()
datatype Variables = Variables(numGrants: nat, rightCars: seq<Permission>, leftCars: seq<Permission>, carsOnBridge: nat)

//Describe Initial State
predicate Init(c:Constants, v:Variables)
{
    && v.numGrants == 0
    && v.rightCars == []
    && v.leftCars == []
    && v.carsOnBridge == 0
}

//Define the following transitions
predicate carJoinQueueOnLeft(c:Constants, v:Variables, v':Variables)
{
    && v' == v.(leftCars := v.leftCars + [NoPermission])
}

predicate carJoinQueueOnRight(c:Constants, v:Variables, v':Variables)
{
    && v' == v.(rightCars := v.rightCars + [NoPermission])
}

predicate GrantPermissionToCarFromLeft(c:Constants, v:Variables, v':Variables)
{
    && |v.leftCars| > 0
    && v.leftCars[0] == NoPermission
    && v.numGrants == 0
    && v' == v.(numGrants := v.numGrants + 1, leftCars := v.leftCars[0 := PermissionGranted])
}

predicate GrantPermissionToCarFromRight(c:Constants, v:Variables, v':Variables)
{
    && |v.rightCars| > 0
    && v.rightCars[0] == NoPermission
    && v.numGrants == 0
    && v' == v.(numGrants := v.numGrants + 1, rightCars := v.rightCars[0 := PermissionGranted])
}

predicate CarComingOnBridgeFromLeft(c:Constants, v:Variables, v':Variables)
{
    && |v.leftCars| > 0
    && v.leftCars[0] == PermissionGranted
    && v' == v.(leftCars := v.leftCars[1..], carsOnBridge := v.carsOnBridge + 1)
    
}

predicate CarComingOnBridgeFromRight(c:Constants, v:Variables, v':Variables)
{
    && |v.rightCars| > 0
    && v.rightCars[0] == PermissionGranted
    && v' == v.(rightCars := v.rightCars[1..], carsOnBridge := v.carsOnBridge + 1)
}

predicate CarOnTheBridgePassThroughTheBridge(c:Constants, v:Variables, v':Variables)
{
    && v.carsOnBridge > 0
    && v.numGrants > 0
    && v' == v.(carsOnBridge := v.carsOnBridge - 1, numGrants := v.numGrants - 1)
}

datatype Step = 
    | GrantPermissionToCarFromLeft
    | GrantPermissionToCarFromRight
    | CarComingOnBridgeFromLeft
    | CarComingOnBridgeFromRight
    | CarOnTheBridgePassThroughTheBridge
    | carJoinQueueOnLeft
    | carJoinQueueOnRight

predicate NextStep(c:Constants, v:Variables, v':Variables, step:Step)
{
    match step
    {
        case GrantPermissionToCarFromLeft => GrantPermissionToCarFromLeft(c, v, v')
        case GrantPermissionToCarFromRight => GrantPermissionToCarFromRight(c, v, v')
        case CarComingOnBridgeFromLeft => CarComingOnBridgeFromLeft(c, v, v')
        case CarComingOnBridgeFromRight => CarComingOnBridgeFromRight(c, v, v')
        case CarOnTheBridgePassThroughTheBridge => CarOnTheBridgePassThroughTheBridge(c, v, v')
        case carJoinQueueOnLeft => carJoinQueueOnLeft(c, v, v')
        case carJoinQueueOnRight => carJoinQueueOnRight(c, v, v')
    }
}

predicate Next(c:Constants, v:Variables, v':Variables)
{
    exists step :: NextStep(c, v, v', step)
}

//Define the set of safe states
predicate Safety(c:Constants, v:Variables)
{
    && v.carsOnBridge <= 1
}

//Find a suitable inductive invariant
predicate Inv(c:Constants, v:Variables)
{
    true    
}
lemma InitImpliesInv(c:Constants, v:Variables)
    requires Init(c, v)
    ensures Inv(c, v)
{

}
lemma InvImpliesSafety(c:Constants,v: Variables)
    requires Inv(c, v)
    ensures Safety(c, v)
{

}
lemma InvInductive(c:Constants, v:Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
{

}