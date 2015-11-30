method lastIndexOf(items: array<int>, item: nat) returns (r: int)
  requires items != null
  ensures r < items.Length
  // If result is positive, element at that position must match item
  ensures r >= 0 ==> items[r] == item
  // If result is positive, no element at greater position matches item
  ensures r >= 0 ==> forall x :: r < x < items.Length ==> items[x] != item
  // If result is negative, no element matches item
  ensures r < 0 ==> forall x :: 0 <= x < items.Length ==> items[x] != item
{
    r := items.Length;
    while r > 0
      // i is decreasing and no element at greater position matches item
      invariant 0 <= r <= items.Length
      decreases r
      invariant forall x :: r <= x < items.Length ==> items[x] != item
    {
        r := r - 1;
        if items[r] == item { return; }
    }
    // didn't find item in entire list
    r := -1;
}

