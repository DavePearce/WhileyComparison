// Status: verifies and compiles
// Result holds iff array is a palindrome :)
method isPalindrome(chars: array<int>) returns (r: bool)
  requires chars != null
  ensures r <==> forall x: int :: 
      0 <= x < chars.Length ==> chars[x] == chars[chars.Length - (x + 1)]
{
    var i: nat := 0;
    var j: nat := chars.Length;
    //
    while i < j
      invariant i + j == chars.Length && i >= 0
      invariant forall k: int :: 0 <= k < i ==> chars[k] == chars[chars.Length - (k + 1)]
    {
        j := j - 1;
        if chars[i] != chars[j]
        {
            return false;
        }
        i := i + 1;
    }
    return true;
}