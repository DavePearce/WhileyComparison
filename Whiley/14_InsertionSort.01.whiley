// Insertion sort

import "12_displace.01.whiley"
import "07_linearSearch.01.whiley"

function insertSort(int[] arr) -> (int[] r)
  requires |arr| > 0
  ensures |arr| == |r|
  ensures all { j in 0..len, k in 0..len | j < k ==> r[j] <= r[k] }
:
  nat i = 0
  nat pos = 0
  int[] res = [ 0, |arr| ]
  // Simply copy the array
  while i < |res|
    where i <= |res|
    where all { k in 0..i | res[k] == arr[k] }
  :
    res[i] = arr[i]
    i = i + 1
  
  assert all { k in 0..|res| | res[k] == arr[k] }
  i = 0
  // 
  while i < |res|
    where i <= |r|
    where |arr| == |r|
    where all { j in 0..i, k in 0..i | j < k ==> res[j] <= res[k] }
  :
    pos = linearSearch(res, res[i], i)
    i = i + 1
    res = displace(res, pos, i - pos)
  
  return res
}