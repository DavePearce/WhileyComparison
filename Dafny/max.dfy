// Status 

// find maximum value of two integers
method max(x: int,y: int) returns (r: int)
//////////////////////////////////////////
ensures (r == y ==> r > x) || (r == x ==> r >= y)
{
  // The goal is to implement, specify and verify this function!
  if x > y { return x; }
  return y;
}