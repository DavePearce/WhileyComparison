// Status wyc-37: verifies [1745ms].
//        wyc-36: verifies [3987ms].

// Append a single item onto the end of the array
public function append(int[] items, int item) -> (int[] rs)
ensures |rs| == |items| + 1:
    // The goal is to implement, specify and verify this function!
    //
    int[] result = [ 0; |items| + 1 ]
    int i = 0
    //
    while i < |items|
    where all { k in 0..i | result[k] == items[k] }
    where i >= 0
    where |result| == |items| + 1
    where i < |result|:
        result[i] = items[i]
        i = i + 1
    //
    result[i] = item
    return result 
