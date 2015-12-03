type nat is (int n) where n >= 0

// A linear search over a sorted array looking for a given element.
function search(int[] ls, int item) -> (int r)
//////////////////////////////////////////////
// ls is an ordered array
requires all { k in 1..|ls| - 1 | ls[k] <= ls[k + 1] && ls[k] >= ls[k - 1] }
// if not found return index is -1
ensures r < 0 ==> all { k in 0..|ls| | ls[k] != item }
// if found the index is returned
ensures r >= 0 ==> some { k in 0..|ls| | ls[k] == item }
:
    nat i = 0
    
    while i < |ls|
    where i <= |ls|
    where all { k in 0..i | ls[k] != item }
    :
        if ls[i] == item:
            return i
        i = i + 1
    
    return -1