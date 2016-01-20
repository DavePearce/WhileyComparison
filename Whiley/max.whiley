// Status wyc-37: .
//        wyc-36: .
public function max(int x, int y) -> (int r)
  ensures (r == y ==> r > x) || (r == x ==> r >= y)
:
  // The goal is to implement, specify and verify this function!
  if x > y:
    return x
  return y
