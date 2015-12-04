type nat is (int n) where n >= 0

// A linear search over a sorted array looking for a given element.
function search(int[] ls, int item) -> (int r)
//////////////////////////////////////////////
requires |ls| > 0
// ls is an ordered array
requires all { k in 1..|ls| - 1 | ls[k] <= ls[k + 1] && ls[k] >= ls[k - 1] }
// if not found return index is -1
ensures r < 0 ==> all { k in 0..|ls| | ls[k] != item }
// if found the index is returned
ensures r >= 0 ==> some { k in 0..|ls| | ls[k] == item }
:
    int i = |ls|
    int res = -1
    
    while i > 0
    where 0 <= i where i <= |ls|
    where -1 <= res where res < |ls|
    where res >= 0 ==> some { k in i..|ls| | ls[k] == item }
    where res < 0 ==> no { k in i..|ls| | ls[k] == item }
    :
        i = i - 1
        if ls[i] == item:
            res = i
    
    return res