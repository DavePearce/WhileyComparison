// Status: verifies and compiles
// Append a single item onto the end of the array
method append( items: array<int>, item: int ) returns (r: array<int>)
  requires items != null && items.Length > 0
  ensures r != null && r.Length == items.Length + 1
  ensures forall k: int :: 0 <= k < items.Length ==> r[k] == items[k]
{
    r := new int[items.Length + 1];
    var i: nat := 0;

    while i < items.Length
      invariant r.Length == items.Length + 1
      invariant i <= items.Length
      invariant forall k: int :: 0 <= k < i ==> r[k] == items[k]
    {
        r[i] := items[i];
        i := i + 1;
    }
    r[i] := item;
}