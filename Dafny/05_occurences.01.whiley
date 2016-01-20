// Status wyc-37: loop invariant not restored where count == 0 ==> ...
//        wyc-36: "
function occurences(int[] items, int item) -> (int r)
  // some number of occurences of item
  ensures r > 0  ==> some { k in 0..|items| | items[k] == item }
  // no occurences of item
  ensures r == 0 ==> all  { k in 0..|items| | items[k] != item }
:
  int i = 0
  int count = 0
  
  while i < |items|
    // i is increasing and there could be elements that match
    where 0 <= i && i <= |items|
    where count > 0  ==> some { k in 0..i | items[k] == item }
    where count == 0 ==> all  { k in 0..i | items[k] != item }
  :
    if items[i] == item
    :
      count = count + 1
    i = i + 1
  
  return count
