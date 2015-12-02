method copy( src: array<int>, sStart: nat, dest: array<int>, dStart: nat, len: nat)
    returns (r: array<int>)
  // starting points in both arrays cannot be negative
  requires src != null && dest != null
  // Source array must contain enough elements to be copied
  requires src.Length >= sStart + len
  // Destination array must have enough space for copied elements
  requires dest.Length >= dStart + len
  // Result is same size as dest
  ensures r != null
  ensures r.Length == dest.Length
  // All elements before copied region are same
  ensures r[..dStart] == dest[..dStart]
  // All elements above copied region are same
  ensures r[dStart + len..] == dest[dStart + len..]
  // All elements in copied region match src
  ensures forall k: nat :: k < len ==> r[dStart + k] == src[sStart + k]
  
{
    if len == 0 { return dest; }
    assert len > 0;
    var i: nat := 0;
    r := new int[dest.Length];
    while (i < dest.Length)
      invariant i <= dest.Length
      invariant r.Length == dest.Length
      invariant forall k: nat :: k < i ==> r[k] == dest[k]
      decreases dest.Length - i
    {
        r[i] := dest[i];
        i := i + 1;
    }
    assert i == dest.Length;
    i := 0;
    while (i < len)
      invariant i <= len
      invariant r.Length == dest.Length
      invariant r[..dStart] == dest[..dStart]
      invariant r[dStart + len..] == dest[dStart + len..]
      invariant forall k: nat :: k < i ==> r[dStart + k] == src[sStart + k]
      decreases len - i
    {
        r[dStart + i] := src[sStart + i];
        i := i + 1;
    }
}