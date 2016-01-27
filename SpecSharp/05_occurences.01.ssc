function count(items: seq<int>, item: int): nat
  decreases |items|
{
  if |items| == 0 then 0 else
    if items[0] == item 
      then (1 + count( items[1..], item ))
      else count( items[1..], item )
}
// Status: ???
method occurences(items: array<int>, item: int) returns (r: nat)
  requires items != null
  ensures r <= items.Length
  // some number of occurences of item
  ensures r > 0  ==> exists k: nat :: k < items.Length && items[k] == item
  // no occurences of item
  ensures r == 0 ==> forall k: nat :: k < items.Length ==> items[k] != item
  ensures r == count( items[..], item )
{
  var i: int := 0;
  var num: nat := 0;
  
  while i < items.Length
    // i is increasing and there could be elements that match
    invariant 0 <= i <= items.Length
    invariant num <= items.Length
    invariant num <= i
    invariant num > 0 ==> exists k: nat :: k < i
                          && items[k] == item
    invariant num == 0 ==> forall k: nat :: k < i
                           ==> items[k] != item
    invariant num == count( items[..i], item )
  {
    if items[i] == item
      { num := num + 1; }
    i := i + 1;
  }
  return num;
}