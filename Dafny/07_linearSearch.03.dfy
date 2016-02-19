// Status:

method linearSearch(arr: array<int>, val: int) returns (r: int)
  requires arr != null
  // arr is an ordered array
  requires forall k :: 0 <= i < j < arr.Length ==> arr[i] < arr[j]
  // Return is between -1 and length of arr
  ensures r >= -1 && r < arr.Length
  // If index returned, it is first match
  ensures r >= 0 ==> forall k: nat :: k < r ==> arr[k] < val
  // If index return, it matches val
  ensures r >= 0 ==> arr[r] == val
  // if failure, no matching element exists
  ensures r == -1 ==> forall k: nat :: k < arr.Length ==> arr[k] != val
{
  //
  var i: int := 0;
  //
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall k: nat :: k < i ==> arr[k] < val
  {
    if arr[i] == val
      { return i; }
    else if arr[i] > val
      { return -1; }
    i := i + 1;
  }
  return -1;
}