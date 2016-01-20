// Status wyc-37: null pointer exception
//        wyc-36: line 37: loop invariant not restored
type nat is (int n) where n >= 0

function displace( int[] arr, nat start, nat len) -> (int[] r)
  requires len > 0
  requires start + len <= |arr|
  ensures |r| == |arr|
  ensures all { k in             0..start       | r[k] == arr[k] }
  ensures all { k in (start + len)..|arr|       | r[k] == arr[k] }
  ensures all { k in   (start + 1)..start + len | r[k] == arr[k - 1] }
  ensures r[start] == arr[start + len - 1]
:
  nat i = 0
  int[] res = [0 ; |arr|]
  
  while i < start
    where i <= start
    where |res| == |arr|
    where all { k in  0..i | res[k] == arr[k] }
  :
    res[i] = arr[i]
    i = i + 1
  
  assert all { k in 0..start | res[k] == arr[k] }

  res[start] = arr[start + len - 1]
  
  assert res[start] == arr[start + len - 1]
  
  i = start + 1
  while i < start + len
    where |res| == |arr|
    where start < i && i <= (start + len)
    where res[start] == arr[start + len - 1]
    where all { k in           0..start | res[k] == arr[k] }
    where all { k in (start + 1)..i     | res[k] == arr[k - 1] }
  :
    res[i] = arr[i - 1]
    i = i + 1
  
  assert all { k in (start + 1)..start + len | res[k] == arr[k - 1] }
  
  i = start + len
  while i < |arr|
    where |res| == |arr|
    where (start + len) <= i && i <= |arr|
    where res[start] == arr[start + len - 1]
    where all { k in             0..start       | res[k] == arr[k] }
    where all { k in   (start + 1)..start + len | res[k] == arr[k - 1] }
    where all { k in (start + len)..i           | res[k] == arr[k] }
  :
    res[i] = arr[i]
    i = i + 1
  
  return res