// Status: wyc-37: verified [1761ms] wyc-36: verified [14265ms] ~810.05 percent
type nat is (int n) where n >= 0

function search(int[] ls, int item) -> (int r)
  // there is something to search through
  requires |ls| > 0
  // ls is an ordered array
  requires all { k in 0..|ls| - 1 | ls[k] <= ls[k + 1] }
  // if not found return index is -1
  ensures r < 0 ==> all { k in 0..|ls| | ls[k] != item }
  // if found the index is returned
  ensures r >= 0 ==> ls[r] == item
:
  nat i = 0

  while i < |ls|
    where i <= |ls|
    where all { k in 0..i | ls[k] != item }
  :
    if ls[i] == item
    :
      return i
    i = i + 1
    
  return -1