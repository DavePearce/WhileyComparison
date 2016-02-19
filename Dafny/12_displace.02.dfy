// Status: verified

predicate rotated(o:seq<int>, r:seq<int>) 
requires |o| == |r|
{
  (forall i :: 1 <= i < |o| ==> r[i] == o[i-1]) &&
  (|o| > 0 ==> r[0] == o[|o|-1])  
}

// rotates a region of the array by one place forward
method displace(arr: array<int>, start: nat, len: nat) returns (r: array<int>)
  requires arr != null
  requires len > 1
  requires start + len <= arr.Length
  // returned array is the same size as input arr
  ensures r != null && r.Length == arr.Length
  // elements before the start of the region are unchanged
  ensures arr[..start] == r[..start]
  // elements after the end of the rhe region are unchanged
  ensures arr[(start + len)..] == r[(start + len)..]
  // elements in the region are skewed by one in a positive direction and wrap
  // around
  ensures rotated(arr[start .. start+len], r[start .. start+len])
{
  var i: nat := 0;
  r := new int[arr.Length];
  
  // just copy the array
  while i < arr.Length
    invariant i <= arr.Length
    invariant forall k: nat :: k < i ==> r[k] == arr[k]
  {
    r[i] := arr[i];
    i := i + 1;
  }
  assert arr[..start] == r[..start] && arr[(start + len)..] == r[(start + len)..];
  
  i := 1;
  r[start] := arr[start + len - 1];
  
  // rotate the array region between start to len
  while i < len
    invariant 0 < i <= len
    invariant r[..start] == arr[..start]
    invariant r[start] == arr[start + len - 1]
    invariant r[(start + len)..] == arr[(start + len)..]
    invariant forall k :: 0 < k < i ==> r[start + k] == arr[start + k - 1]
  {
    r[start + i] := arr[start + i - 1];
    i := i + 1;
  }
  assert rotated(arr[start .. start+len], r[start .. start+len]);
}