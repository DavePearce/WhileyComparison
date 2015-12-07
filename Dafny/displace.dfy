// Status: verifies and compiles
// rotates a region of the array by one place backward
method displace(arr: array<int>, start: nat, len: nat) returns (r: array<int>)
  requires arr != null
  requires start + len <= arr.Length
  //
  ensures r != null && r.Length == arr.Length
  ensures forall k: nat :: k < start ==> arr[k] == r[k]
  ensures forall k: nat :: (start + len) <= k < arr.Length ==> arr[k] == r[k]
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
    invariant forall k: nat :: k < start ==> r[k] == arr[k]
    invariant forall k :: start <= k < i
              ==> r[start + (((k + 1) - start) % len)] == arr[k]
    invariant forall k :: (start + len) <= k < arr.Length ==> r[k] == arr[k]
  {
      r[start + (((i + 1) - start) % len)] := arr[i];
      i := i + 1;
  }
  assert i == (start + len);
}