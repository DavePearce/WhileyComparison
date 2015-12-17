// Status wyc-37: loop invariant does not hold on entry [1192ms]
//                where all { k in start..i | result[k] ==
//                          arr[start + (((k + 1) - start) % len)] }
//                (i == start on entry) --> start..start is empty.
//        wyc-36: verification infinite loop
type nat is (int n) where n >= 0

// rotates a region of the array by one place forward
function displace(int[] arr, nat start, nat len) -> (int[] r)
/////////////////////////////////////////////////////////////
requires start + len <= |arr|
// output array is the same size as input array
ensures |r| == |arr|
// all elements before the region remain the same
ensures all { k in 0..start | r[k] == arr[k] }
// all elements after the region remain the same
ensures all { k in (start + len)..|arr| | r[k] == arr[k] }
// all elements in the region are rotated by one place
ensures all { k in start..start + len | r[k] == arr[start + (((k + 1) - start) % len)] }
:
  nat i = start
  int[] result = arr
  assert all { k in 0..|result| | result[k] == arr[k] }

  while i < (start + len)

  where start <= i where i <= (start + len)
  where |result| == |arr|
  where all { k in 0..start | result[k] == arr[k] }
  where all { k in start..i | result[k] == arr[start + (((k + 1) - start) % len)] }
  where all { k in (start + len)..|arr| | result[k] == arr[k] }
  :
    result[i] = arr[start + (((i + 1) - start) % len)]
    i = i + 1

  assert i == (start + len)
  
  return result