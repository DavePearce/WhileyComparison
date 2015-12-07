method findIns(arr: array<int>, val: int, len: nat) returns (r: nat)
  requires arr != null
  requires len < arr.Length
  // arr is an ordered array
  requires forall k: nat :: k < len - 1 ==> arr[k] <= arr[k + 1]
  // return value should not exceed len
  ensures r <= len
  // index of place of insertion is returned
  ensures forall k: nat :: k < r ==> arr[k] < val
{
    var i: nat := 0;
    
    while i < len
      invariant i <= len
      decreases len - i
      invariant forall k: nat :: k < i ==> arr[k] < val
    {
        if arr[i] >= val
          { return i; }
        i := i + 1;
    }
    return i;
}