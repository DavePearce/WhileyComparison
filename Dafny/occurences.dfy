// Status:  

method occurences(items: array<int>,item: nat) returns (r: nat)
  requires items != null
  // some number of occurences of item
  ensures r > 0  ==> exists k: nat :: k < items.Length && items[k] == item
  // no occurences of item
  ensures r == 0 ==> forall k: nat :: k < items.Length ==> items[k] != item
{
  var i: nat := 0;
  var count: nat := 0;
  
  while i < items.Length
    // i is increasing and there could be elements that have matched
    invariant i <= items.Length
    invariant count > 0  ==> exists k: nat :: k < i && items[k] == item
    invariant count == 0 ==> forall k: nat :: k < i ==> items[k] != item
  {
    if items[i] == item
      { count := count + 1; }
    i := i + 1;
  }
  return count;
}