method copy( src: array<int>, sStart: int, dest: array<int>, dStart: int, len: int) returns (r: array<int>)
  // starting points in both arrays cannot be negative
  requires sStart >= 0 && dStart >= 0 && len >= 0 && src != null && dest != null;
  // Source array must contain enough elements to be copied
  requires src.Length >= sStart + len;
  // Destination array must have enough space for copied elements
  requires dest.Length >= dStart + len;
  // Result is same size as dest
  ensures r != null && r.Length == dest.Length;
  // All elements before copied region are same
  ensures forall k: int :: 0 <= k < dStart ==> r[k] == dest[k];
  // All elements in copied region match src
  ensures forall k: int :: 0 <= k < len ==> src[sStart + k] == dest[dStart + k];
  // All elements above copied region are same
  ensures forall k: int :: dStart + len <= k < dest.Length ==> r[k] == dest[k];
{
    var i := 0;
    ghost var odest := dest;
    while (len > i)
      invariant i >= 0;
      invariant forall k: int :: 0 <= k < dStart ==> odest[k] == dest[k];
      invariant forall k: int :: dStart + len <= k < dest.Length ==> odest[k] == dest[k];
      invariant forall k: int :: 0 <= k < i ==> dest[dStart + k] == src[sStart + k];
    {
        dest[dStart + i] := src[sStart + i];
        i := i + 1;
    }
    return dest;
}