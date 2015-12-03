method copy( src: array<int>, sStart: nat, dest: array<int>, dStart: nat, len: nat)
    returns (r: array<int>)
  // both arrays cannot be null
  requires dest != null && src != null
  // Source array must contain enough elements to be copied
  requires src.Length >= sStart + len
  // Destination array must have enough space for copied elements
  requires dest.Length >= dStart + len
  // Result is same size as dest
  ensures r != null
  ensures r.Length == dest.Length
  // All elements before copied region are same
  ensures r[..dStart] == dest[..dStart]
  requires dest.Length >= dStart + len
  // All elements above copied region are same
  ensures r[dStart + len..] == dest[dStart + len..]
  // All elements in copied region match src
  ensures forall k: nat :: k < len ==> r[dStart + k] == src[sStart + k]
  
{
    if len == 0 { return dest; }
    assert len > 0;
    var i: nat := 0;
    r := new int[dest.Length];
    while (i < dStart)
      invariant i <= dStart
      decreases dStart - i
      invariant r.Length == dest.Length
      invariant forall k: nat :: k < i ==> r[k] == dest[k]
    {
        r[i] := dest[i];
        i := i + 1;
    }
    assert r[..dStart] == dest[..dStart];
    assert i == dStart;
    while (i < (dStart + len))
      invariant dStart <= i <= (dStart + len)
      decreases (dStart + len) - i
      invariant r.Length == old(r.Length)
      //invariant (sStart + len) >= i
      invariant r[..dStart] == dest[..dStart]
      invariant forall k: nat :: dStart <= k < i ==> r[k] == src[k + (sStart - dStart)]
    {
        r[i] := src[i + (dStart - sStart)];
        i := i + 1;
    }
    assert i == dStart + len;
    while (i < r.Length)
      invariant (dStart + len) <= i <= r.Length
      decreases r.Length - i
      invariant r.Length == old(r.Length)
      invariant r.Length >= dStart + i
      invariant r[..dStart] == dest[..dStart]
      invariant r[dStart..(dStart + len)] == src[sStart..(sStart + len)]
      invariant r[(dStart + len + i)..] == dest[(dStart + len + i)..]
    {
        r[i] := dest[i];
        i := i + 1;
    }
}