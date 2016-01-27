// Status: verifies
method firstIndexOf(items: array<int>, item: int) returns (r: int)
  requires items != null
  ensures r < items.Length
  // If result is positive, element at that position must match item
  ensures r >= 0 ==> items[r] == item
  // If result is positive, no element at lesser position matches item
  ensures r >= 0 ==> forall k: nat :: k < r ==> items[k] != item
  // If result is negative, no element matches item
  ensures r < 0 ==> forall k: nat :: k < items.Length
                    ==> items[k] != item
{
  var i: int := 0;
  while i < items.Length
    // i is increasing and no element at greater position matches item
    invariant 0 <= i <= items.Length
    invariant forall k: nat :: k < i ==> items[k] != item
  {
    if items[i] == item
      { return i; }
    i := i + 1;
  } // didn't find item in entire list
  return -1;
}