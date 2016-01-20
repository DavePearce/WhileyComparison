// Status wyc-37: verifies.
//        wyc-36: verifies.
public function maxArray(int[] items) -> (int max)
  requires |items| > 0
  ensures all { k in 0..|items| | max >= items[k] }
:
  int i = 1
  int r = items[0]
  
  while i < |items|
    where 0 < i && i <= |items|
    where all { k in 0..i | r >= items[k] }
  :
    if items[i] > r:
      r = items[i]
    i = i + 1
  
  return r
