// Status: verifier infinite loop
// rotates a region of the array by one place forward
method displace(arr: array<int>, start: nat, len: nat) returns (r: array<int>)
  requires arr != null
  requires start + len < arr.Length
  // returned array is the same size as input arr
  ensures r != null && r.Length == arr.Length
  ensures start + len <= r.Length
  // elements before the start of the region are unchanged
  ensures arr[..start] == r[..start]
  // elements after the end of the rhe region are unchanged
  ensures arr[(start + len + 1)..] == r[(start + len + 1)..]
  // elements in the region are skewed by one in a positive direction and wrap around
  ensures r[start] == arr[start + len]
  ensures forall k :: start < k < (start + len) ==> r[k + 1] == arr[k]
{
    var i: nat := 0;
    r := new int[arr.Length];
    
    while i < arr.Length
      invariant i <= arr.Length
      invariant forall k: nat :: k < i ==> r[k] == arr[k]
    {
        r[i] := arr[i];
        i := i + 1;
    }
    
    i := start;
    
    while i < (start + len)
      invariant r.Length == arr.Length
      invariant start <= i <= (start + len)
      invariant arr[..start] == r[..start]
      invariant arr[(start + len + 1)..] == r[(start + len + 1)..]
      invariant forall k :: start < k < i ==> r[k + 1] == arr[k]
      invariant i == start + len ==> r[start] == arr[start + len]
    {
        r[start + (((i + 1) - start) % len)] := arr[i];
        i := i + 1;
    }
}