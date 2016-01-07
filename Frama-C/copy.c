#include <stdio.h>
#include <stdlib.h>

/*  Starting points in both arrays cannot be negative.
    Source array must contain enough elements to be copied.
    Destination array must have enough space for copied elements.
    Result is same size as dest.
    All elements before copied region are same.
    All elements in copied region match src.
    All elements above copied region are same.
  */
/*@ requires sStart >= 0;
  @ requires dStart >= 0;
  @ requires range > 0;
  @ requires slen >= sStart + range;
  @ requires dlen >= dStart + range;
  @ requires \separated( src+ (0..(slen - 1) ), dest+ (0..(dlen - 1) ) );
  @ requires \valid( src+ (0..(slen - 1) ) );
  @ requires \valid( dest+ (0..(dlen - 1) ) );
  @ assigns dest[dStart..(dStart + range)];
  @ ensures \forall integer k; 0 <= k < range ==> dest[dStart + k] == src[sStart + k];
  */
void copy( const int src[], const size_t slen, const size_t sStart
              , int dest[], const size_t dlen, const size_t dStart, const size_t range )
{
  size_t i = 0;
  /*All items are still the same before dStart index.
    All items after dStart index are still the same.
    Inbetween items are copied from src.
    */
  /*@ loop assigns i, dest[dStart..(dStart + i)];
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

/*@ requires len > 0;
  @ requires \valid( items+ ( 0..(len - 1) ) );
  @ assigns items[0..(len - 1)];
  @ ensures \forall integer k; 0 <= k < len ==> items[k] == k;
  */
void fillarr( int* items, size_t len )
{
  /*@ loop assigns i, items[0..(i - 1)];
    @ loop invariant \forall integer k; 0 <= k < i ==> items[k] == k;
    @ loop variant len - i; */
  for ( int i = 0; i < len; ++i )
    items[i] = i;
}

/*@ requires len > 0;
  @ assigns \nothing; */
void printarr( int* items, size_t len )
{
  printf( "array = [ " );
  /*@ loop assigns i;
    @ loop variant len - i; */
  for(int i = 0; i < len - 1; i++)
    printf( "%d ,", items[i] );
  printf( len > 0 ? "%d ]\n" : "]\n", items[len - 1] );
}

int main()
{
  int src[] = { 6, 7, 8, 9, 10 };
  int res[] = malloc( 5 * sizeof(int) );
  fillarr( res, 5 );
  copy( src, 5, 1, res, 5, 1, 3 );
  printarr( res, 5 );
}
