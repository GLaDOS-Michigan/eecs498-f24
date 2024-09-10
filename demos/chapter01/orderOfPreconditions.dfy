predicate bar()

predicate foo(x: int) 
    requires bar()
{
    x > 5
}

predicate baz(x:int ) {
    && foo(x)
    && bar()
}

predicate IsMaxIndex(a:seq<int>, x:int) {
    && (forall i | 0 <= i < |a| :: a[i] <= a[x])
    && 0 <= x < |a|
}
