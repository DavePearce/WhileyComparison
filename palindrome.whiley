 function isPalindrome(int[] chars) -> (bool r)
// Result holds iff array is a palindrome :)
//requires |chars| != 0
ensures r <==> all { x in 0..|chars| | chars[x] == chars[|chars| - (x + 1)] }:
    //
    int i = 0
    int j = |chars|
    //
    while i < j
    where i + j == |chars| && i >= 0
    where all { k in 0..i | chars[k] == chars[|chars| - (k+1)] }:
        j = j - 1
        if chars[i] != chars[j]:
            return false
        i = i + 1
    //
    return true
