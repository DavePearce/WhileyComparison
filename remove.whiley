import whiley.lang.System

function remove(int[] items, int index) -> (int[] r)
requires index >= 0
requires index < |items|
ensures |r| == |items| - 1
ensures all { k in 0..index | r[k] == items[k] }
ensures all { k in index..|r| | r[k] == items[k + 1] }
:
    //
    // This function should remove the item at the given
    // index from the items array, and return the resulting 
    // array otherwise unchanged.  The resulting array is of 
    // course one element shorter in length.
    int i = index
    int j = 0
    int newlen = |items| - 1
    int[] result = [ 0 ,newlen ]
    
    while i < newlen
    where i >= 0 && j >= 0
    where newlen >= i && j <= 1
    where |result| == newlen
    // items before i are still the same or transposed
    where all { k in index..i | result[k] == items[k + 1] }
    :
        if i == index:
            j = j + 1
        result[i] = items[i + j]
        i = i + 1
    
    return result
