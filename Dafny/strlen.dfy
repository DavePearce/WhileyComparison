// Calculate length of string
method strlen(str: array<char>) returns (r: nat)
  requires str != null
  requires exists k: nat :: 0 <= k < str.Length && str[k] == '\0' 
{
  r := 0;
  while str[r] != '\0'
    invariant r <= str.Length
    invariant forall k: nat :: 0 <= k < r ==> str[k] != '\0'
    //decreases str.Length - r
  {
      r := r + 1;
  }
}
