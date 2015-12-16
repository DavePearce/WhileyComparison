// Status: verifies and compiles
// Copies a region of array src and overwrites the same sized region of array
// dest.
method copy( src: array<int>, sStart: nat, dest: array<int>, dStart: nat, len: nat)
    returns (r: array<int>)
  // both arrays cannot be null
  requires dest != null && src != null;
  // Source array must contain enough elements to be copied
  requires src.Length >= sStart + len;
  // Destination array must have enough space for copied elements
  requires dest.Length >= dStart + len;
  // Result is same size as dest
  ensures r != null;
  ensures r.Length == dest.Length;
  // All elements before copied region are same
  ensures r[..dStart] == dest[..dStart];
  // All elements above copied region are same
  ensures r[dStart + len..] == dest[dStart + len..];
  // All elements in copied region match src
  ensures forall k: nat :: k < len ==> r[dStart + k] == src[sStart + k];
  
{
    if len == 0 { return dest; }
    var i: nat := 0;
    r := new int[dest.Length];

    while (i < r.Length)
      invariant i <= r.Length
      invariant forall k: nat :: k < i ==> r[k] == dest[k]
    {
        r[i] := dest[i];
        i := i + 1;
    }
    assert r[..] == dest[..];
    i := 0;
    while (i < len)
      invariant i <= len
      invariant r[..dStart] == dest[..dStart]
      invariant r[dStart..dStart + i] == src[sStart..sStart + i]
      invariant r[dStart + len..] == dest[dStart + len..]
// Dafny can't verify the following
//      invariant forall k: nat :: k < i ==> r[dStart + k] == src[sStart + k]
// even though the above line:
//      r[dStart..dStart + i] == src[sStart..sStart + i] should prove the same cases
    {
        r[dStart + i] := src[sStart + i];
        i := i + 1;
    }
}