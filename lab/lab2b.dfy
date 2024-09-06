//Exercise 1: Going between exists and forall

//Negating an exists statement gives us a forall statement
//This exists statement is not properly negated
//Look at the asserts in the control flow to see why
lemma existsToForall(s:seq<int>)
    requires !(exists i | 0 <= i < |s| :: s[i] < 0)
    ensures (forall i | 0 <= i < |s| :: s[i] > 0)
{
    forall i | 0 <= i < |s|
        ensures s[i] >= 0
        {
            if s[i] < 0 {
                assert false;
            }
            else {
                assert s[i] > 0;
            }
        }
}

//Exercise 2

//As a refresher, try negating this forall statement to an exists
lemma forallToExists(s:seq<int>)
    requires !(forall i | 0 <= i < |s| :: s[i] > 2 || s[i] < -2)
    ensures false
{
}
 
//Exercise 3: Map Comprehension
lemma mapComprehensionExpr()
{
    //Try using map comprehension to create a map that maps x -> 2x for x = 1,2,3 by replacing this line
    var mapComprehension : map<int,int>;
    assert mapComprehension == map[1 := 2, 2 := 4, 3 := 6];
    assert |mapComprehension| == 3;
    assert mapComprehension[1] == 2;
    assert mapComprehension[2] == 4;
    assert mapComprehension[3] == 6;
    assert forall x | x in mapComprehension :: mapComprehension[x] == x * 2;
}

//Exercise 4: Set Comprehension
lemma setComprehensionExpr()
{
    //Try using set comprehension to create a set with all positive even numbers less than 10
    var setComprehension : set<int>;

    //Sometimes dafny can be a bit annoying for proving statements about explicitly constructed sets/lists/maps
    //Luckily, this is not something we encounter much while verifying systems in this class
    //Try proving the following statement if it doesn't verify automatically
    //(note showing something is in a set is similar an exist statement, which you know how to prove)
    assert 2 in setComprehension;
}

//Exercise 5: Sequence Comprehension
lemma sequenceComprehensionExpr()
{
    //Try using set comprehension to create a set with all positive even numbers less than 10 (increasing or decreasing)
    var seqComprehension : seq<int>;
    assert |seqComprehension| == 5;

}
//Exercise 6: Using maps for practical purposes

//Recall that in dafny, maps are immutable
//With this is in mind implement a method that returns the frequency of each element in the inputsequence
//For now, don't worry about proving any correctness properties, though you may need an invariant to prove that certain keys persist
//in your map (depending on implementation)
ghost method countFreq(intSeq:seq<int>) returns (counts: map<int, int>)
{
    
}



//Exercise 7: Practicing Loop invariants
//Try making a declarative sumSpec and an imperative implementation of calcSum where you sum all elements in the the input sequence
//Use loop invariants to prove that the both of them match
//While this might seem a bit pointless for this example (as our declarative spec is basically a recursive implementation of calcSum),
//when proving properties about systems later on we will similar proofs, only with more layers of abstraction between the spec
//and implementation

//Note there are multiple ways to define this; depending on this definition, certain implementations might be extremely hard to prove.
// Dafny in some cases can't infer associativity/commutativity over an unspecified number of elements, so keep this in mind when doing 
// your proof. If you get stuck, feel free to reach out for help.
ghost function sumSpec(s: seq<int>) : (sum: int)
{
    0
}
ghost method calcSum(s:seq<int>) returns (sum:int)
    ensures sumSpec(s) == sum
{
    return 0;
}
lemma Test(){
    //depending of your implementation, this may or may not verify right away. If that is the case try checking sum of [1], then [1,2]
    // and so on. This is because dafny tries not to unroll definitions by too many iterations so that it doesn't time out
    assert sumSpec([1,2,3,4,5]) == 15;
    assert sumSpec([]) == 0;
}
