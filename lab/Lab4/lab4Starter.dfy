datatype Dir = North | South | East | West

datatype Variables = Variables(x: int, y: int, dir: Dir)

ghost predicate Init(v: Variables){
    && v.x == 0
    && v.y == 3
    && v.dir.East?
}

ghost predicate moveEast(v: Variables, v': Variables){
    && v.dir.East?
    && v' == v.(x := v.x + 1)
}

ghost predicate moveWest(v: Variables, v': Variables){
    && v.dir.West?
    && v' == v.(x := v.x - 1)
}

ghost predicate moveNorth(v: Variables, v': Variables){
    && v.dir.North?
    && v' == v.(y := v.y + 1)
}

ghost predicate moveSouth(v: Variables, v': Variables){
    && v.dir.South?
    && v' == v.(y := v.y - 1)
}

ghost predicate turnEast(v: Variables, v': Variables)
{
    && v.y >= 3
    && v.x <= -3
    && v' == v.(dir := East)
}

ghost predicate turnWest(v: Variables, v': Variables)
{
    && v.y <= -3
    && v.x >= 3
    && v' == v.(dir := West)
}

ghost predicate turnNorth(v: Variables, v': Variables)
{
    && v.y <= -3
    && v.x <= -3
    && v' == v.(dir := North)
}

ghost predicate turnSouth(v: Variables, v': Variables)
{
    && v.y >= 3
    && v.x >= 3
    && v' == v.(dir := South)
}

ghost predicate Next(v: Variables, v': Variables)
{
    || moveEast(v, v')
    || moveNorth(v, v')
    || moveSouth(v, v')
    || moveWest(v, v')
    || turnEast(v, v')
    || turnNorth(v, v')
    || turnSouth(v, v')
    || turnWest(v, v')
}

//Define safety as you are always euclidean distance 3 away from the origin
ghost predicate Safety(v: Variables)
{
    false
}

//Define an Inductive Variant that implies safety
ghost predicate Inv(v: Variables)
{
    false
}

//The following lemmas should verify for a correct invariant (likely without proof)
//Note, these obligations are boilerplate for inductive proofs in Dafny, so you will see
//this in most of the assignments
lemma InitImpliesInv(v: Variables)
    requires Init(v)
    ensures Inv(v)
{
    
}
lemma InvImpliesSafety(v: Variables)
    requires Inv(v)
    ensures Safety(v)
{

}
lemma InvInductive(v:Variables, v': Variables)
    requires Inv(v)
    requires Next(v, v')
    ensures Inv(v')
{
}
