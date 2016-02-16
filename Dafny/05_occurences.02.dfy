// Status: verified
function count(items: seq<int>, item: int): nat
  decreases |items|
{
  if |items| == 0 then 0 else
    (if items[|items|-1] == item then 1 else 0)
        + count( items[..|items|-1], item )
}

method occurences(items: array<int>, item: int) returns (num: nat)
  requires items != null
  ensures num <= items.Length
  // zero or more occurences of item
  //ensures num == 0 <==> item !in items[..]
  ensures num == count( items[..], item )
{
  var i: nat := 0;
  num := 0;
  
  while i < items.Length
    // i is increasing and count the matches so far
    invariant num <= i <= items.Length
    //invariant num == 0 <==> item !in items[..i]
    invariant num == count( items[..i], item )
  {
    // inductive definition of counting occurrences
    assert items[..i+1] == items[..i] + [items[i]];
    if items[i] == item
      { num := num + 1; }
    i := i + 1;
  }
  assert items[..i] == items[..];
}