// Status: verifies and compiles?...no
//         ( if a[mid] < key:, index out of bounds (negative) )
// Search through a sorted list by way of narrowing the search by half upon
// each iteration. rerturns the index of item or -1 if not found
type nat is (int n) where n >= 0

method BinarySearch( int[] a, int key ) -> (int r)  
//////////////////////////////////////////////////
requires all { i in 0..|a|, j in 0..|a| | i <= j ==> a[i] <= a[j] }
ensures r >= 0 ==> r < |a| && a[r] == key
ensures r < 0  ==> all { k in 0..|a| | a[k] != key }
:
  nat low = 0
  nat high = |a|
  nat mid = 0

  while low < high
  ////////////////
  where high <= |a|
  where  low <= |a|
  where  mid <= |a|
  where  low <= high 
  where  low <= mid
  where  mid <= high
  // elements outside the search range are not eqaul to key
  where all { i in 0..|a| | !(low <= i && i < high) ==> a[i] != key }
  :
    mid = (low + high) / 2
    if a[mid] < key:
      low = mid + 1
    else if key < a[mid]:
      high = mid
    else:
      return mid
  return -1