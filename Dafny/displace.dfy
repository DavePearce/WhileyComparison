// Status: verifier infinite loop
// rotates a region of the array by one place forward
method displace(arr: array<int>, start: nat, len: nat) returns (r: array<int>)
  requires arr != null
  requires start + len <= arr.Length
  // returned array is the same size as input arr
  ensures r != null && r.Length == arr.Length
  // elements before the start of the region are unchanged
  ensures arr[..start] == r[..start]
  // elements after the end of the rhe region are unchanged
  ensures arr[(start + len)..] == r[(start + len)..]
  // elements in the region are skewed by one in a positive direction and wrap around
  ensures forall k :: start <= k < (start + len)
                 ==> r[start + (((k + 1) - start) % len)] == arr[k]
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
      invariant start <= i <= (start + len)
      invariant arr[..start] == r[..start]
      invariant arr[(start + len)..] == r[(start + len)..]
      invariant forall k :: start <= k < i
                ==> r[start + (((k + 1) - start) % len)] == arr[k]
    {
        r[start + (((i + 1) - start) % len)] := arr[i];
        i := i + 1;
    }
}