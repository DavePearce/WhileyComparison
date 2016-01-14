#include "include.h"

void fillarr( int* items, size_t len )
{
  /*@ loop assigns i, items[0..(i - 1)];
    @ loop invariant \forall integer k; 0 <= k < i ==> items[k] == k;
    @ loop variant len - i; */
  for ( int i = 0; i < len; ++i )
    items[i] = i;
}

void printarr( int* items, size_t len )
{
  printf( "array = [ " );
  /*@ loop assigns i;
    @ loop variant len - i; */
  for(int i = 0; i < len - 1; i++)
    printf( "%d ,", items[i] );
  printf( len > 0 ? "%d ]\n" : "]\n", items[len - 1] );
}
