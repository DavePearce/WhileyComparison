// Status wyc-37: verifies [3519ms] wyc-36: verifies [9570ms]
function linearSearch(int[] arr, int val) -> (int r)
  // arr is an ordered array
  requires all { i in 0..|arr|, j in 0..|arr|
               | i < j ==> arr[i] < arr[j] }
  // Return is between -1 and length of arr
  ensures r >= -1 && r < |arr|
  // If index returned, it is first match
  ensures r >= 0 ==> all { k in 0..r | arr[k] < val }
  // If index return, it matches val
  ensures r >= 0 ==> arr[r] == val
  // if failure, no matching element exists
  ensures r == -1 ==> no { k in 0..|arr| | arr[k] == val }
:
  int i = 0
  //
  while i < |arr|
    where i >= 0 && i <= |arr|
    where all { k in 0..i | arr[k] < val }
  :
    if arr[i] == val:
      return i
    else if arr[i] > val:
      return -1
    i = i + 1
  return -1