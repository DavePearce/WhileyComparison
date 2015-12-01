method copy( src: seq<int>, sStart: nat, dest: seq<int>, dStart: nat, len: nat)
    returns (r: array<int>)
  // starting points in both arrays cannot be negative
  //requires src != null && dest != null
  // Source array must contain enough elements to be copied
  requires |src| >= sStart + len
  // Destination array must have enough space for copied elements
  requires |dest| >= dStart + len
  // Result is same size as dest
  ensures r.Length == |dest|
  // All elements before copied region are same
  ensures r[..dStart] == dest[..dStart]
  // All elements in copied region match src
  ensures src[sStart..sStart + len] == r[dStart..dStart + len]
  // All elements above copied region are same
  ensures r[dStart + len..] == dest[dStart + len..]
{
    var i: nat := 0;
    r := dest[..];
    while (i < len)
      invariant i <= len
      decreases len - i
      invariant r.Length == |dest|
      invariant forall k: nat :: k < dStart ==> r[k] == dest[k]
      invariant forall k: nat :: dStart + len <= k < |dest| ==> r[k] == dest[k]
      invariant forall k: nat :: k < i ==> r[dStart + k] == src[sStart + k]
    {
        r[dStart + i] := src[sStart + i];
        i := i + 1;
    }
}