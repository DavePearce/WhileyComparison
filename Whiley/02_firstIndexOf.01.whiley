// Status wyc-37: 
//        wyc-36: 

function firstIndexOf(int[] items, int item) -> (int r)
// If result is positive, element at that position must match item
ensures r >= 0 ==> items[r] == item
// If result is positive, no element at lesser position matches item
ensures r >= 0 ==> all { k in 0..r | items[k] != item }
// If result is negative, no element matches item
ensures r <  0 ==> no  { k in 0..|items| | items[k] == item }
:
  int i = 0
  while i < |items|
  // i is increasing and no element at greater position matches item
  where 0 <= i && i <= |items|
  where no { k in 0..i | items[k] == item }
  :
    i = i + 1
    if items[i] == item
    :
      return i
  // didn't find item in entire list
  return -1 