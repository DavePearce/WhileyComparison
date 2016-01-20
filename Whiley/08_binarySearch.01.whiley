// Status: verifies and compiles?...no
//         ( if items[mid] < key:, index out of bounds (negative) )
type nat is (int n) where n >= 0

method binarySearch( int[] items, int key ) -> (int r)
  requires |items| > 0
  requires all { j in 0..|items|, k in 0..|items|
               | j < k ==> items[j] <= items[k] }
  ensures r >= 0 ==> r < |items| && items[r] == key
  ensures r < 0  ==> all { k in 0..|items| | items[k] != key }
:
  nat low = 0
  nat high = |items|
  nat mid = 0

  while low < high
    where low <= mid
    where mid < high
    where high <= |items|
    // elements outside the search range do not equal key
    where no { i in 0..low, j in high..|items|
              | items[i] != key && items[j] == key }
  :
    mid = (low + high) / 2
    
    if items[mid] < key
    :
      low = mid + 1
    else if key < items[mid]
    :
      high = mid
    else
    :
      return mid
  
  return -1