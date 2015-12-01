// Calculate length of string
method strlen(str: array<char>) returns (r: nat)
  requires str != null
  requires exists k: nat :: k < str.Length && str[k] == '*' 
{
  r := 0;
  while str[r] != '*'
    invariant r <= str.Length
    invariant forall k: nat :: k < r ==> str[k] != '*'
    decreases str.Length - r
  {
      r := r + 1;
  }
}
