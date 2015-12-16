type nat is (int n) where n >= 0

function findIns(int[] arr, int val, nat len) -> (nat r)
///////////////////////////////////////////////
requires len < |arr|
// arr is an ordered array
requires all { k in 0..len - 1 | arr[k] <= arr[k + 1] }
// return value should not exceed len
ensures r <= len
// index of place of insertion is returned
ensures all { k in 0..r | arr[k] <  val }
:
    nat i = 0
    
    while i < len

    where i <= len
    where all { k in 0..i | arr[k] < val }
    :
        if arr[i] >= val:
            assert all { k in i..len | arr[k] >= val }
            return i
        i = i + 1
    return i