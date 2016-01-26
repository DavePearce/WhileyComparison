// Status wyc-37: null pointer 
//        wyc-36: loop inv. doesn't hold on entry line: 34
function insert(int[] items, int item, int index) -> (int[] r)
  requires 0 <= index && index < |items|
  requires |items| > 0
  ensures |r| == |items| + 1
  ensures all { k in 0..index | items[k] == r[k] }
  ensures r[index] == item
  ensures all { j in index..|r|, k in index..|items|
              | j == k + 1 ==> items[k] == r[j] }
:
  // length of the new array
  int newlen = |items| + 1
  int[] result = [ 0; newlen ]
  int i = 0
  //
  while i < |items|
    // items before index in result are still the same
    where 0 <= i && i <= |items|
    where |result| == newlen
    where i <= index ==> all { k in 0..i | items[k] == result[k] }
    where i > index ==> result[index] == item &&
                        all { k in 0..index | items[k] == result[k] }
    where i > index ==> all { j in index..i, k in index..i
                             | j == k + 1 ==> items[k] == result[j] }
  :
    if i < index:
      result[i] = items[i]
    else if i == index:
      result[i] = item
    else:
      result[i + 1] = items[i]
    i = i + 1
  return result