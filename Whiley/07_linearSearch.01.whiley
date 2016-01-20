// Status wyc-37: verification infinite loop.
//        wyc-36: postcondition not satisfied -> return i (line:26)
type nat is (int n) where n >= 0

function linearSearch(int[] arr, int val, nat len) -> (nat r)
  requires len < |arr|
  // arr is an ordered array
  requires all { j in 0..len, k in 0..len | j < k ==> arr[j] <= arr[k] }
  // return value should not exceed len
  ensures r <= len
  // index of place of insertion is returned
  ensures all { k in 0..r | arr[k] <  val }
  ensures all { k in r..len | arr[k] >=  val }
:
  nat i = 0
  
  while i < len
    where i <= len
    where all { k in 0..i | arr[k] < val }
    where i < (len - 1) ==> arr[i] <= arr[i + 1]
  :
    if arr[i] >= val
    :
      return i
    i = i + 1
  
  return i