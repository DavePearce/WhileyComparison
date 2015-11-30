// This function should remove the item at the given
// index from the items array, and return the resulting 
// array otherwise unchanged.  The resulting array is of 
// course one element shorter in length.
function remove(int[] items, int index) -> (int[] r)

requires 0 <= index && index < |items|
requires |items| > 0
ensures |r| == |items| - 1
ensures all { k in 0..index   | r[k] == items[k] }
//ensures all { k in index..|r| | r[k] == items[k + 1] }
:
    int newlen = |items| - 1
    int i = 0
    int[] result = [ 0; newlen ]

    while i < index
    // items before index in result are still the same
    where 0 <= i where i <= index
    where |result| == newlen
    where all { k in 0..i | k < index ==> result[k] == items[k] }
    :
        result[i] = items[i]
        i = i + 1
    assert i == index
//     while i < newlen
//     // items after index in result are transposed by one place
//     where index <= i where i <= newlen
//     where |result| == newlen
//     where all { k in 0..index | result[k] == items[k] }
//     where all { k in index..i | result[k] == items[k + 1] }
//     :
//         result[i] = items[i + 1]
//         i = i + 1
    
    return result
