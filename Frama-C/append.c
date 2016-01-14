#include <stdio.h>
#include <stdlib.h>
#include "include.h"
// Append a single item onto the end of the array
/*@ requires 0 < len < 2147483646;
  @ requires \valid( items+ (0..(len - 1) ) );
  @ requires \valid( item );
  @ assigns result;
  @ ensures \forall integer k; 0 <= k < len ==> \result[k] == items[k];
  @ ensures \result[len] == item;
  @*/
int* append ( int* items, const int len, const int item )
{
  // The goal is to implement, specify and verify this function!
  int result[] = malloc ( ( len + 1 ) * sizeof ( int ) );
  /*@ loop assigns i, result[0..(i-1)];
    @ loop invariant \forall integer k; 0 <= k < i ==> items[k] == result[k];
    @ loop variant len - i; */
  for ( int i = 0; i < len; ++i )
    result[i] = items[i];
  result[len] = item;
  free( items );
  return result;
}

int main()
{
  int len = 15;
  int* arr = malloc ( len * sizeof ( int ) );
  fillarr ( arr, len );

  printarr ( arr, len );

  arr = append ( arr, len, len );

  printarr ( arr, len + 1 );

  free ( arr );
  return 0;
}
