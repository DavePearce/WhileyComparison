// Status: verifier infinite loop
// rotates a region of the array by one place forward
method displace(arr: array<int>, start: nat, len: nat)
  requires arr != null
  requires len > 1
  requires start + len <= arr.Length
  modifies arr;
  // returned array is the same size as input arr
  ensures arr != null && arr.Length == old(arr.Length)
  // elements before the start of the region are unchanged
  ensures arr[..start] == old(arr[..start])
  // elements after the end of the rhe region are unchanged
  ensures arr[(start + len)..] == old(arr[(start + len)..])
  // elements in the region are skewed by one in a positive direction and wrap
  // around
  ensures forall k :: 0 < k < len
                 ==> arr[start + k] == old(arr[start + k - 1])
  ensures arr[start] == old(arr[start + len - 1])
{
  var i: nat := len - 1;
  var temp := arr[start + i]; // end of region element
  
  // rotate the region
  while i > 0
    invariant 0 <= i < len
    invariant arr[..start] == old(arr[..start])
    invariant arr[(start + len)..] == old(arr[(start + len)..])
    invariant forall k :: i < k < len 
              ==> arr[start + k] == old(arr[start + k - 1])
  {
    arr[start + i] := arr[start + i - 1];
    i := i - 1;
  }
  
  arr[start] := temp;
}