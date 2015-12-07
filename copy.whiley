import whiley.lang.System

method main(System.Console console):
    int[] src = [1,2,3,4,5]
    int[] res = copy( src, 2, [3,4,5,6,7], 1, 3 )
    console.out.println(res)

function copy(int[] src, int sStart, int[] dest, int dStart, int len) -> (int[] r)
// starting points in both arrays cannot be negative
requires sStart >= 0 && dStart >= 0 && len > 0
// Source array must contain enough elements to be copied
requires |src| >= sStart + len
// Destination array must have enough space for copied elements
requires |dest| >= dStart + len
// Result is same size as dest
ensures |r| == |dest|
// All elements before copied region are same
ensures all { k in 0..dStart | r[k] == dest[k] }
// All elements in copied region match src
ensures all { k in 0..len | r[dStart + k] == src[sStart + k] }
// All elements above copied region are same
ensures all { k in dStart + len..|dest| | r[k] == dest[k] }
:
    //
    int i = 0
    int[] odest = dest
    assert all { k in 0..|dest| | dest[k] == odest[k] }
    //
    while i < len
    where 0 <= i where i <= len
    where |dest| == |odest|
    // all items are still the same before dStart index
    where all { k in 0..dStart | dest[k] == odest[k] }
    // all items after dStart index are still the same
    where all { k in (dStart + len)..|dest| | dest[k] == odest[k] }
    // inbetween items are copied from src
    where all { k in sStart..sStart + i, j in dStart..dStart + i | src[k] == dest[j] }
    :
        dest[dStart + i] = src[sStart + i]
        i = i + 1
    //
    return dest 
