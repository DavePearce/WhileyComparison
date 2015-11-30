// This function should remove the item at the given
// index from the items array, and return the resulting 
// array otherwise unchanged.  The resulting array is of 
// course one element shorter in length.
method remove(items: array<int>, index: nat) returns (r: array<int>)

  requires items != null && index < items.Length
  requires items.Length > 0
  ensures r != null && r.Length == items.Length - 1
  ensures forall k: nat :: k < index ==> r[k] == items[k]
  ensures forall k :: index <= k < r.Length ==> r[k] == items[k + 1]
{
    // length of the new array
    var newlen := items.Length - 1;
    r := new int[newlen];
    var i: nat := 0;

    while i < index
      // items before index in result are still the same
      invariant i <= index
      decreases index - i
      invariant r.Length == newlen
      invariant forall k: nat :: k < i ==> (k < index ==> r[k] == items[k])
    {
        r[i] := items[i];
        i := i + 1;
    }
    assert i == index;
    while i < newlen
      // items after index in result are transposed by one place
      invariant index <= i <= newlen
      decreases newlen - i
      invariant r.Length == newlen
      invariant forall k: nat :: k < index ==> r[k] == items[k]
      invariant forall k :: index <= k < i ==> r[k] == items[k + 1]
    {
        r[i] := items[i + 1];
        i := i + 1;
    }
}