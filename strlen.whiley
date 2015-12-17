// Status: wyc-37: verified and compiled [1197ms] ~(-7.76)
//         wyc-36: verified and compiled [1104ms]

constant NULL is 0

// ASCII character is unsigned 8bit integer
type ASCII_char is (int n) where n >= 0 && n < 256

// C String is array of chars where at least one is NULL
type C_string is (ASCII_char[] chars) where some { i in 0..|chars| | chars[i] == NULL }

// Calculate length of string
function strlen(C_string str) -> (int r)
////////////////////////////////////////
ensures r >= 0
:
  int i = 0
  //
  while str[i] != NULL
  where i >= 0
  where all { k in 0..i | str[k] != NULL }
  :
     i = i + 1
  return i
