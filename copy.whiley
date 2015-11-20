import whiley.lang.System

method main(System.Console console):
    int[] src = [1,2,3,4,5]
    int[] res = copy( src, 2, [3,4,5,6,7], 1, 3 )
    console.out.println(res)

function copy(int[] src, int sStart, int[] dest, int dStart, int len) -> (int[] r)
// starting points in both arrays cannot be negative
requires sStart >= 0 && dStart >= 0 && len >= 0
// Source array must contain enough elements to be copied
requires |src| >= sStart + len
// Destination array must have enough space for copied elements
requires |dest| >= dStart + len
// Result is same size as dest
ensures |r| == |dest|
// All elements before copied region are same
ensures all { k in 0..dStart | r[k] == dest[k] }
// All elements in copied region match src
ensures all { k in 0..len | src[sStart + k] == dest[dStart + k] }
// All elements above copied region are same
ensures all { k in dStart + len..|dest| | r[k] == dest[k] }:
    //
    int i = 0
    int[] odest = dest
    //
    while i < len
    where i >= 0
    where all { k in 0..dStart | odest[k] == dest[k] }
    where all { k in dStart + len..|dest| | odest[k] == dest[k] }
    where all { k in 0..i | dest[dStart + k] == src[sStart + k] }:
        dest[dStart + i] = src[sStart + i]
        i = i + 1
    //
    return dest 
