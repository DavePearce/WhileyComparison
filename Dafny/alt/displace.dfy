// Status: verifies and compiles
// rotates a region of the array by one place backward
method displace(arr: array<int>, start: nat, len: nat)
  modifies arr
  requires arr != null
  requires start + len <= arr.Length
  //
  ensures arr != null && arr.Length == old(arr.Length)
  ensures forall k: nat :: k < start ==> arr[k] == old(arr[k])
  ensures forall k: nat :: (start + len) <= k < arr.Length ==> arr[k] == old(arr[k])
  ensures forall k :: start <= k < (start + len)
                 ==> arr[start + (((k + 1) - start) % len)] == old(arr[k])
{
  var i := start + len - 2;
  var temp := arr[start + len - 1];
  
  while i >= start
    invariant start <= i <= (start + len)
    invariant arr[..start] == old(arr[..start])
    invariant forall k :: start <= k < i
              ==> arr[start + (((k + 1) - start) % len)] == old(arr[k])
    invariant arr[(start + len)..] == old(arr[(start + len)..])
  {
      arr[i + 1] := arr[i];
      i := i - 1;
  }
  arr[start] := temp;
}
