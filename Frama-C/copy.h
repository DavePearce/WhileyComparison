#ifndef COPY_H_INCLUDED
#define COPY_H_INCLUDED

#include <stdio.h>

/*@
  // Starting points in both arrays cannot be negative.
  @ requires sStart >= 0;
  @ requires dStart >= 0;
  // Source array must contain enough elements to be copied.
  @ requires range > 0;
  // Destination array must have enough space for copied elements.
  @ requires slen >= sStart + range;
  @ requires dlen >= dStart + range;
  @ requires \separated( src+ (0..(slen - 1) ), dest+ (0..(dlen - 1) ) );
  @ requires \valid( src+ (0..(slen - 1) ) );
  @ requires \valid( dest+ (0..(dlen - 1) ) );
  // All elements before and after the copied region are same.
  @ assigns dest[dStart..(dStart + range)];
  // All elements in copied region match src.
  @ ensures \forall integer k; 0 <= k < range ==> dest[dStart + k] == src[sStart + k];
  */
void copy( const int src[], const int slen, const int sStart
              , int dest[], const int dlen, const int dStart, const int range );

#endif // COPY_H_INCLUDED
