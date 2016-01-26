// Status wyc-37: null pointer
//        wyc-36: line 37: loop inv. !restored

function displace( int[] arr, int start, int len) -> (int[] r)
  requires len > 0
  requires start + len <= |arr|
  ensures |r| == |arr|
  ensures all { k in 0..start | r[k] == arr[k] }
  ensures all { k in (start + len)..|arr| | r[k] == arr[k] }
  ensures all { k in (start + 1)..start + len
              | r[k] == arr[k - 1] }
  ensures r[start] == arr[start + len - 1]
:
  int i = start
  int[] res = arr
  res[start] = arr[start + len - 1]
  
  while i < |arr|
    where |res| == |arr|
    where (start + len) <= i && i <= |arr|
    where res[start] == arr[start + len - 1]
    where all { k in 0..start | res[k] == arr[k] }
    where all { k in (start + len)..i | res[k] == arr[k] }
    where all { k in start..start + len - 1
              | res[k + 1] == arr[k] }
  :
    res[i] = arr[i]
    i = i + 1
  
  return res
  