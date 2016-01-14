// Status: verifier infinite loop
// rotates a region of the array by one place forward

predicate rotated(o:seq<int>, r:seq<int>) 
  requires |o| == |r|
{
  (forall i :: 1 <= i < |o| ==> r[i] == o[i-1]) &&
  (|o| > 0 ==> r[0] == o[|o|-1])  
}

method displace(arr: array<int>, start: nat, len: nat) returns (r: array<int>)
  requires arr != null
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
  
  if len > 0 {
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
