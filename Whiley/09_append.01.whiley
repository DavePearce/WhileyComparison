// Status: verifies wyc-37: [1745ms]
//                  wyc-36: [3987ms] ~228.48 percent
public function append(int[] items, int item) -> (int[] rs)
  ensures |rs| == |items| + 1
:
  int[] result = [ 0; |items| + 1 ]
  int i = 0
  //
  while i < |items|
    where all { k in 0..i | result[k] == items[k] }
    where i >= 0
    where |result| == |items| + 1
    where i < |result|
  :
    result[i] = items[i]
    i = i + 1
  result[i] = item
  return result 
