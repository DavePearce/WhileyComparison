// Status: verified
function count(items: seq<int>, item: int): nat
{
  multiset(items)[item]
}

method occurences(items: array<int>, item: int) returns (num: nat)
  requires items != null
  ensures num <= items.Length
  // no occurences of item
  ensures num == 0 <==> item !in items[..]
  ensures num == count( items[..], item )
{
  num := 0;
  var i: nat := 0;
  
  while i < items.Length
    // i is increasing and there could be elements that match
    invariant num <= i <= items.Length
    invariant num == 0 <==> item !in items[..i]
    invariant num == count( items[..i], item )
  {
    if items[i] == item
      { num := num + 1; }
    i := i + 1;
  }
  assert items[..i] == items[..];
}