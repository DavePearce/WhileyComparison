// Status wyc-37: verifies [1048ms] ~(-27.77%)
//        wyc-36: verifies [1429ms]

function lastIndexOf(int[] items, int item) -> (int r)
// If result is positive, element at that position must match item
ensures r >= 0 ==> items[r] == item
// If result is positive, no element at greater position matches item
ensures r >= 0 ==> all { x in (r + 1)..|items| | items[x] != item }
// If result is negative, no element matches item
ensures r < 0 ==> no { x in 0..|items| | items[x] == item }
:
  int i = |items|
  while i >= 0
  // i is decreasing and no element at greater position matches item
  where 0 <= i && i <= |items|
  where no { x in i..|items| | items[x] == item }
  :
    i = i - 1
    if items[i] == item
    :
      return i
  // didn't find item in entire list
  return -1 
