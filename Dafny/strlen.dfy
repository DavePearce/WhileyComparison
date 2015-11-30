constant NULL is 0

// ASCII character is unsigned 8bit integer
type ASCII_char is (int n) where n >= 0 && n < 256

// C String is array of chars where at least one is NULL
type C_string is (ASCII_char[] chars) where some { i in 0..|chars| | chars[i] == NULL }

// Calculate length of string
method strlen(str: C_string) returns (r: nat)
  requires C_string != null
{
  var r = 0;
  while str[r] != NULL
    invariant r <= C_string.Length
    invariant forall k: nat :: 0 <= k < r ==> str[k] != NULL
    decreases C_string.Length - r
  {
      r = r + 1;
  }
}
