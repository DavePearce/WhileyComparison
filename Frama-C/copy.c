#include "copy.h"

void copy( const int src[], const int slen, const int sStart
              , int dest[], const int dlen, const int dStart, const int range )
{
  int i = 0;
  /*All items are still the same before dStart index.
    All items after dStart index are still the same.
    Inbetween items are copied from src.
    */
  /*@ loop assigns i, dest[dStart..(dStart + i - 1)];
    @ loop invariant 0 <= i <= range;
    @ loop invariant \forall integer k; 0 <= k < i ==> src[sStart + k] == dest[dStart + k];
    @ loop variant range - i;
    */
  while( i < range )
  {
      dest[dStart + i] = src[sStart + i];
      ++i;
  }
}

