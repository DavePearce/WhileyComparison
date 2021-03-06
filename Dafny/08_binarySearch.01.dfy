// Status: verifies and compiles
predicate sorted(s: seq<int>)
{
   forall i,j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method BinarySearch(a: array<int>, key: int) returns (index: int)  
  
  requires a != null && sorted(a[..])
  ensures index >= 0 ==> index < a.Length && a[index] == key
  ensures index < 0  ==> forall k: nat :: k < a.Length ==> a[k] != key
{
  var low := 0;
  var high := a.Length;     
  

  while (low < high)
    invariant 0 <= low <= high <= a.Length
    invariant forall i :: 0 <= i < a.Length
              && !(low <= i < high) ==> a[i] != key
  {
      var mid := (low + high) / 2;
      if (a[mid] < key)
        { low:= mid + 1; }
      else if (key < a[mid])
        { high := mid; }
      else
        { return mid; }     
  
  }     
  return -1;
}       
 