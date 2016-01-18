// This function should remove the item at the given
// index from the items array, and return the resulting 
// array otherwise unchanged.  The resulting array is of 
// course one element shorter in length.
function remove(int[] items, int index) -> (int[] r)

requires 0 <= index && index < |items|
requires |items| > 0
ensures |r| == |items| - 1
ensures all { k in 0..index   | r[k] == items[k] }
ensures all { k in index..|r| | r[k] == items[k + 1] }
:
  int newlen = |items| - 1
  int i = 0
  int[] result = [ 0; newlen ]

  while i < newlen
    
  where 0 <= i where i <= newlen
  where |result| == newlen
  // items before i in result are still the same or transposed
  where all { k in 0..i | k < index ==> result[k] == items[k] }
  where all { k in index..i | result[k] == items[k + 1] }
  :
    if i > index:
      result[i - 1] = items[i]
    else if i < index:
      result[i] = items[i]
    i = i + 1

  return result