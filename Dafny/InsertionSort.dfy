// Insertion sort

include "displace.dfy"
include "find.dfy"

method insertSort(arr: array<int>) returns (r: array<int>)
  requires arr != null
  ensures r != null
  ensures arr.Length == r.Length
  ensures forall k: nat :: 0 <= k < r.Length - 1 ==> r[k] <= r[k + 1]
{
    var i: nat := 0;
    var pos: nat := 0;
    r := new int[arr.Length];
    
    while (i < r.Length)
      invariant i <= r.Length
      invariant forall k: nat :: k < i ==> r[k] == arr[k]
    {
        r[i] := arr[i];
        i := i + 1;
    }
    
    i := 0;
    while (i < r.Length)
      //...
    {
        pos := findIns(r, r[i], i);
        i := i + 1;
        r := displace(r, pos, i - pos);
    }
}