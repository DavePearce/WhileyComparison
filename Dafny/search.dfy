// Status: verifies and compiles
method search(ls: array<int>, item: int) returns (r: int)
  requires ls != null
  // ls is an ordered array
  requires forall k: nat :: 0 <= k < ls.Length - 1 ==> ls[k] <= ls[k + 1] 
  // if not found return index is -1
  ensures r < 0  ==> forall k: nat :: k < ls.Length ==> ls[k] != item
  // if found the index is returned
  ensures r >= 0 ==> exists k: nat :: k < ls.Length ==> ls[k] == item
{
    var i: nat := 0;
    
    while i < ls.Length
      invariant i <= ls.Length
      decreases ls.Length - i
      invariant forall k: nat :: k < i ==> ls[k] != item
    {
      if ls[i] >= item
        { return i; }
      i := i + 1;
    }
    return -1;
}