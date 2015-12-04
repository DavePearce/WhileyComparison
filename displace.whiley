type nat is (int n) where n >= 0

// rotates a region of the array by one place forward
function displace(int[] arr, nat start, nat len) -> (int[] r)
/////////////////////////////////////////////////////////////
requires start + len <= |arr|
// 
ensures |r| == |arr|
ensures all { k in 0..start | r[k] == arr[k] }
ensures all { k in (start + len)..|arr| | r[k] == arr[k] }
ensures all { k in start..start + len | r[k] == arr[start + (((k + 1) - start) % len)] }
:
  nat i = 0
  int[] result = [ 0; |arr| ]

  while i < start

  where i <= start
  where |result| == |arr|
  where all { k in 0..i | result[k] == arr[k] }
  :
      result[i] = arr[i]
      i = i + 1

  assert i == start

  while i < (start + len)

  where start <= i where i <= (start + len)
  where |result| == |arr|
  where all { k in 0..start | result[k] == arr[k] }
  where all { k in start..i | result[k] == arr[start + (((k + 1) - start) % len)] }
  :
      result[i] = arr[start + (((i + 1) - start) % len)]
      i = i + 1

  assert i == (start + len)

  while i < |arr|

  where (start + len) <= i where i <= |arr|
  where |result| == |arr|
  where all { k in 0..start | result[k] == arr[k] }
  where all { k in start..start + len | result[k] == arr[start + (((k + 1) - start) % len)] }
  where all { k in (start + len)..i | result[k] == arr[k] }
  :
      result[i] = arr[i]
      i = i + 1
  
  return result