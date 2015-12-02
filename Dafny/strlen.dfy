// Calculate length of string
method strlen(str: array<char>) returns (r: nat)
  requires str != null
  requires exists k: nat :: k < str.Length && str[k] == '\u0000' 
{
  r := 0;
  while str[r] != '\u0000'
    invariant r <= str.Length
    invariant forall k: nat :: k < r ==> str[k] != '\u0000'
    decreases str.Length - r
  {
      r := r + 1;
  }
}
