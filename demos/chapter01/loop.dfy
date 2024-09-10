lemma loop(target:nat) returns (result:nat)
    ensures result == target
{
  result := 0;
  while (result < target)
  {
    result := result + 1;
  }
  return result;
}
