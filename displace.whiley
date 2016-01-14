// Status wyc-37: verification infinite loop
//        wyc-36: loop invariant not restored [1192ms]
//                where all { k in 0 .. start | result[k] == arr[k] }
//        
type nat is (int n) where n >= 0

// rotates a region of the array by one place forward
function displace(int[] arr, nat start, nat len) -> (int[] r)
/////////////////////////////////////////////////////////////
requires len > 1
requires start + len <= |arr|
// output array is the same size as input array
ensures |r| == |arr|
// all elements before the region remain the same
ensures all { k in 0..start | r[k] == arr[k] }
// all elements after the region remain the same
ensures all { k in (start + len)..|arr| | r[k] == arr[k] }
// all elements in the region are rotated by one place
ensures all { k in start + 1..start + len | r[k] == arr[k - 1] }
ensures r[start] == arr[start + len - 1]
:
  nat i = start + 1
  int[] result = arr
  assume all { k in 0..|result| | result[k] == arr[k] }

  while i < (start + len)
  ///////////////////////
  where start < i where i <= (start + len)
  where |result| == |arr|
  where all { k in          0 .. start + 1 | result[k] == arr[k] }
  where all { k in  start + 1 .. i         | result[k] == arr[k - 1] }
  where all { k in (start+len)..|arr|      | result[k] == arr[k] }
  :
    result[i] = arr[i - 1]
    i = i + 1

  assert i == (start + len)
  result[start] = arr[start + len - 1]
  
  return result