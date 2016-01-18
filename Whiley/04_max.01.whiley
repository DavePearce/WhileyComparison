// Status wyc-37: verifies [1745ms]. ~228.48% improvment
//        wyc-36: verifies [3987ms].

// Append a single item onto the end of the array
public function maxArray(int[] items) -> (int max)
//////////////////////////////////////////////////
requires |items| > 0
ensures some { k in 0..|items| | max >= items[k] }
:
  // The goal is to implement, specify and verify this function!
  int i = 1
  int r = items[0]
  //
  while i < |items|
  where 0 < i && i <= |items| 
  :
      if items[i] > r:
        items[i] = r
      i = i + 1
  //
  return r
