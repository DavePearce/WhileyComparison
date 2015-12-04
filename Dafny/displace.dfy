method displace(arr: array<int>, start: nat, len: nat)
    returns (r: array<int>)
  requires arr != null
  requires start + len <= arr.Length
  //
  ensures r != null && r.Length == arr.Length
  ensures forall k: nat :: k < start ==> arr[k] == r[k]
  ensures forall k: nat :: (start + len) <= k < arr.Length
                        ==> arr[k] == r[k]
  ensures forall k :: start <= k < (start + len)
                        ==> r[k] == arr[start + (((k + 1) - start) % len)]
{
  var i: nat := 0;
  r := new int[arr.Length];
  while i < start
    invariant i <= start
    decreases start - i
    invariant r.Length == arr.Length
    invariant forall k: nat :: k < i ==> r[k] == arr[k]
  {
      r[i] := arr[i];
      i := i + 1;
  }
  assert i == start;
  while i < (start + len)
    invariant start <= i <= (start + len)
    decreases (start + len) - i
    invariant r.Length == arr.Length
    invariant forall k: nat :: k < start ==> r[k] == arr[k]
    invariant forall k :: start <= k < i
              ==> r[k] == arr[start + (((k + 1) - start) % len)]
  {
      r[i] := arr[start + (((i + 1) - start) % len)];
      i := i + 1;
  }
  assert i == (start + len);
  while i < arr.Length
    invariant (start + len) <= i <= arr.Length
    decreases arr.Length - i
    invariant r.Length == arr.Length
    invariant forall k: nat :: k < start ==> r[k] == arr[k]
    invariant forall k :: start <= k < (start + len)
              ==> r[k] == arr[start + (((k + 1) - start) % len)]
    invariant forall k :: (start + len) <= k < i ==> r[k] == arr[k]
  {
      r[i] := arr[i];
      i := i + 1;
  }
}