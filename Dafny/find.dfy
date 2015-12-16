predicate sorted(s: seq<int>)
{
  forall i,j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method findIns(arr: array<int>, val: int, len: nat) returns (r: nat)
  requires arr != null
  requires len < arr.Length
  // arr is an ordered array
  requires sorted(arr[..len])
  // return value should not exceed len
  ensures r <= len
  // index of place of insertion is returned
  ensures forall k: nat :: k < r ==> arr[k] < val
  ensures sorted( arr[..r] + [val] + arr[r..len] )
{
    r := 0;
    
    while r < len
      invariant r <= len
      decreases len - r
      invariant forall k: nat :: k < r ==> arr[k] < val
      invariant arr == old(arr)
    {
        if arr[r] >= val
            { return; }
        r := r + 1;
    }
}