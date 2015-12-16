#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// starting points in both arrays cannot be negative
//@ requires sStart >= 0 && dStart >= 0 && range > 0;
// Source array must contain enough elements to be copied
//@ requires \length(src) >= sStart + range;
// Destination array must have enough space for copied elements
//@ requires \length(dest) >= dStart + range;
//@ assigns dest+ (dStart..dStart + range - 1);
// Result is same size as dest
//@ ensures \length(\result) == \length(dest);
// All elements before copied region are same
//@ ensures forall integer k; 0 <= k < dStart ==> r[k] == dest[k];
// All elements in copied region match src
//@ ensures forall integer k; 0 <= k < range ==> r[dStart + k] == src[sStart + k];
// All elements above copied region are same
//@ ensures forall integer k; dStart + range <= k < \length(dest) ==> r[k] == dest[k];

void copy( const int src[], const unsigned int sStart
              , int dest[], const unsigned int dStart, const size_t range )
{
  unsigned int i = 0;
  /*@loop invariant 0 <= i where i <= len
    @loop invariant \length(dest) == \length(\old(dest)) */
    // all items are still the same before dStart index
  /*@loop invariant forall k integer; 0 <= k < dStart ==> dest[k] == odest[k]; */
    // all items after dStart index are still the same
  /*@loop invariant forall integer k; (dStart + len) <= k < |dest| ==> dest[k] == odest[k]; */
    // inbetween items are copied from src
  /*@loop invariant forall integer k, j;
        sStart <= k < sStart + i, dStart <= j < dStart + i ==> src[k] == dest[j]; */
  while( i < range )
  {
      dest[dStart + i] = src[sStart + i];
      ++i;
  }
}

void fillarr( int* items, size_t len, unsigned int from )
{
  for ( int i = 0; i < len; ++i )
    items[i] = i + from;
}

void printarr( int* items, size_t len )
{
  printf( "array = [ " );
  for(int i = 0; i < len - 1; i++)
    printf( "%d ,", items[i] );
  printf( len > 0 ? "%d ]\n" : "]\n", items[len - 1] );
}

int main()
{
  int src[] = { 6, 7, 8, 9, 10 };
  int* res = malloc( 5 * sizeof(int) );
  fillarr( res, 5, 1 );
  copy( src, 1, res, 1, 3 );
  printarr( res, 5 );
}
