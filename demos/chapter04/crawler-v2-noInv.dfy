datatype Variables = Variables(y: int, isGoingNorth: bool)

predicate Init(v: Variables) {
    && v.y == 5
    && v.isGoingNorth
}

predicate Flip(v: Variables, v':Variables) {
    && v'.y + v.y == 0
    && v.isGoingNorth != v'.isGoingNorth
}

predicate MoveNorth(v: Variables, v':Variables) {
    && v.isGoingNorth
    && v' == v.(y := v.y+1)
}

predicate MoveSouth(v: Variables, v':Variables) {
    && !v.isGoingNorth
    && v' == v.(y := v.y-1)
}

predicate Next(v: Variables, v':Variables) {
    || Flip(v, v')
    || MoveNorth(v, v')
    || MoveSouth(v, v')
}

predicate Safety(v: Variables) {
     v.y*v.y > 9
}

predicate Inv(v: Variables) {
    && Safety(v)
}

lemma InvImpliesSafety(v: Variables) 
    requires Inv(v)
    ensures Safety(v)
{
}

lemma InitImpliesInv(v: Variables) 
    requires Init(v)
    ensures Inv(v)
{

}

lemma NextPreservesInv(v: Variables, v': Variables) 
    requires Inv(v)
    requires Next(v, v')
    ensures Inv(v')
{
    if (MoveNorth(v, v')) {
        if (v.y > 3) {
            assert Inv(v');
        } else if (v.y < -3){
            assert Inv(v');
        } else {
            assert false;
            assert Inv(v');
        }
        
    } else if (MoveSouth(v, v')) {
        //assume false;
        assert Inv(v');
    } else if (Flip(v, v')) {
        assert Inv(v');
    } else {
        assert false;
    }
    // assert v'.y*v'.y > 9;
    // assert Safety(v');
    assert Inv(v');
}