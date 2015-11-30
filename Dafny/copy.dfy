method copy( src: array<int>, sStart: nat, dest: array<int>, dStart: nat, len: nat)
    returns (r: array<int>)
  // starting points in both arrays cannot be negative
  requires src != null && dest != null
  // Source array must contain enough elements to be copied
  requires src.Length >= sStart + len
  // Destination array must have enough space for copied elements
  requires dest.Length >= dStart + len
  // Result is same size as dest
  ensures r != null && r.Length == dest.Length
  // All elements before copied region are same
  ensures forall k: nat :: k < dStart ==> r[k] == dest[k]
  // All elements in copied region match src
  ensures forall k: nat :: k < len ==> src[sStart + k] == r[dStart + k]
  // All elements above copied region are same
  ensures forall k: nat :: dStart + len <= k < dest.Length ==> r[k] == dest[k]
{
    var i: nat := 0;
    r := dest;
    while (i < len)
      invariant i <= len
      decreases len - i
      invariant forall k: nat :: k < dStart ==> r[k] == dest[k]
      invariant forall k: nat :: dStart + len <= k < dest.Length ==> r[k] == dest[k]
      invariant forall k: nat :: k < i ==> r[dStart + k] == src[sStart + k]
    {
        r[dStart + i] := src[sStart + i];
        i := i + 1;
    }
}