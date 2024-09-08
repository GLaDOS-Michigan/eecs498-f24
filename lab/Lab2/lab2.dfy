// Exercise 1
//Try to fix this implementation of the power funciton using the error dafny gives you
//You can technically do this in 2 different ways, after completing the lab, try coming back and figuring out a second way
ghost function pow1(base: int, exp: int) : (int)
{
    if exp == 0 then 1 else base * pow1(base, exp-1)
}


// Exercise 2
//Try to implement a version of pow2 using O(log(exp)) multiplications
//HINT: remember to make the fix from exercise 1 here as well
ghost function pow2(base: int, exp: int) : (int)
{
    base
}

lemma checkPow2()
{
    assert pow2(3, 0) == 1;
    assert pow2(5, 1) == 5;
    assert pow2(2, 8) == 256;
    assert pow2(4, 15) == 1073741824;

}

//Exercise 3
//Can you explain why this lemma verifies 
//HINT: if stuck, try calling the lemma in useCounterExample and see what happens
lemma fakeCounterExample(y: nat)
    requires y < 0
    ensures false
{

}

lemma useCounterExample()
{
    
}



//Exercise 4
//Express this predicate that states that (x, y, z) is a pythagorean triple
ghost predicate isPythagoreanTriple(x: nat, y: nat, z:nat)
{
    x*x + y*y == z*z
}

//Write a predicate to show that x is part of a pythagorean triple
//Use as few number of calls to the above function as necessary
ghost predicate partOfTriple(x: nat)
{
    exists y:nat, z:nat :: isPythagoreanTriple(x, y, z) || isPythagoreanTriple(z, y, x) || isPythagoreanTriple(x, z, y)
}
//Try to show 3 is part of a pythagorean triple
lemma proofTriple(x : nat)
{
    assert partOfTriple(3);
}



//Exercise 5
//Fermat's Last Theorem states that no three positive integers a, b, and c satisfy the equation
// a^n + b^n = c^n for any integer value of n greater than 2
//Express Fermat's Last Theorem as a forall statement using the ensures of the below lemma 
lemma FLT()
    ensures false
{

}

//Exercise 6
//Implement a declarative function + imperative method to find the max element of a sequence
//HINT: The max function might be helpful
//HINT: You may need to add preconditions
//HINT: see the examples in the slides for functions & methods in Lab 2
//Remark: you may want prove with dafny both versions are the same, we will try something like this in the next lab
//NOTE: max can't be made ghost here, as otherwise the non-ghost method cannot call it
function max(x: int, y: int) : (int)
{
    if x < y then y else x
}

function maxElementDecl(s: seq<int>) : (maxElt: int)
{
    0
}

method maxElementImp(s: seq<int>) returns (maxElt: int)
{
    maxElt := 0;
}