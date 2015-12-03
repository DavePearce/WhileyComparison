type nat is (int n) where n >= 0
// This function should insert the item at the given
// index from the items array.  The resulting array is of 
// course one element longer in length.
function insert(int[] items, int item, nat index) -> (int[] r)
//////////////////////////////////////////////////////////////
  requires index < |items|
  requires |items| > 0
  ensures |r| == |items| + 1
  ensures all { k in 0..index | r[k] == items[k] }
  ensures r[index] == item
  ensures all { k in index..|r| | r[k] == items[k - 1] }
  :
    // length of the new array
    nat newlen = |items| + 1
    int[] result = [ 0; newlen ]
    nat i = 0

    while i < index
    // items before index in result are still the same
    where i <= index
    where |result| == newlen
    where all { k in 0..i | result[k] == items[k] }
    :
        result[i] = items[i]
        i = i + 1

    result[i] = item
    i = i + 1
    assert i == index + 1
    assume all { k in 0..index | result[k] == items[k] }

    while i < newlen
    // items after index in result are transposed by one place
    where index < i where i <= newlen
    where |result| == newlen
    where all { k in 0..index | result[k] == items[k] }
    where result[index] == item
    where all { k in (index + 1)..i | result[k] == items[k - 1] }
    :
        result[i] = items[i - 1]
        i = i + 1
    return result