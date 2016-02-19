// Status: verifies and compiles
// rotates a region of the array by one place forward
predicate rotated(arr1:seq<int>, arr2:seq<int>) 
  requires |arr1| == |arr2|
{
  (forall i :: 1 <= i < |arr1| ==> arr2[i] == arr1[i - 1]) &&
  ( |arr1| > 0 ==> arr2[0] == arr1[ |arr1| - 1 ] )
}
method displace(arr: array<int>, start: nat, len: nat)
    returns (r: array<int>)
  requires arr != null
  requires len > 0
  requires start + len <= arr.Length
  ensures r != null && r.Length == arr.Length
  ensures arr[..start] == r[..start]
  ensures arr[(start + len)..] == r[(start + len)..]
  ensures rotated(arr[start .. start+len], r[start .. start+len])
{
  var i: nat := 0;
  r := new int[arr.Length];
  while i < start
    invariant i <= start
    invariant forall k: nat :: k < i ==> r[k] == arr[k]
  {
    r[i] := arr[i];
    i := i + 1;
  }
  assert arr[..start] == r[..start];
  r[start] := arr[start+len-1];
  assert r[start] == arr[start+len-1];
  
  i := start+1;
  while i < start+len
    invariant start < i <= start+len
    invariant arr[..start] == r[..start]
    invariant r[start] == arr[start+len-1]
    invariant forall k: nat :: start < k < i ==> r[k] == arr[k-1]
  {
    r[i] := arr[i-1];
    i := i + 1;
  }
  assert rotated(arr[start .. start+len], r[start .. start+len]);
  
  i := start+len;
  while i < arr.Length
    invariant start+len <= i <= arr.Length
    invariant arr[..start] == r[..start]
    invariant rotated(arr[start .. start+len], r[start .. start+len])
    invariant forall k: nat :: start+len <= k < i ==> r[k] == arr[k]
  {
    r[i] := arr[i];
    i := i + 1;
  }
}
