// Status: verified
method maxArray(items: array<int>) returns (r: int)
  requires items != null
  requires items.Length > 0
  ensures forall k: nat :: 0 <= k < items.Length ==> r >= items[k]
{
  var i: int := 1;
  r := items[0];
  
  while i < items.Length
    invariant 0 < i <= items.Length
    invariant forall k: nat :: k < i ==> r >= items[k]
  {
    if items[i] > r
      { r := items[i]; }
    i := i + 1;
  }
}