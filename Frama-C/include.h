#ifndef INCLUDE_H_INCLUDED
#define INCLUDE_H_INCLUDED

#include <stdio.h>

/*@ requires len > 0;
  @ requires items != \null;
  @ requires \valid_range( items, 0, len - 1 );
  @ assigns items[0..(len - 1)];
  @ ensures \forall integer k; 0 <= k < len ==> items[k] == k;
  */
void fillarr( int* items, size_t len );

/*@ requires len > 0;
  @ requires items != \null;
  @ requires \valid_range( items, 0, len - 1 );
  @ assigns \nothing; */
void printarr( int* items, size_t len );

#endif // INCLUDE_H_INCLUDED
