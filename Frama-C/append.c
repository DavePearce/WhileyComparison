#include <stdio.h>
#include <stdlib.h>

// Append a single item onto the end of the array
/*@ requires 0 < len < 2147483646;
  @ requires \valid( items+ (0..(len - 1) ) );
  @ assigns \nothing;
  @ ensures \forall integer k; 0 <= k < len ==> \result[k] == items[k];
  @ ensures \result[len] == item;
  @*/
int* append ( int* items, const int len, const int item )
{
  // The goal is to implement, specify and verify this function!
  int result[] = malloc ( ( len + 1 ) * sizeof ( int ) );
  /*@ loop assigns i, result[i];
    @ loop invariant \forall integer k; 0 <= k < i ==> items[k] == result[k];
    @ loop variant len - i; */
  for ( int i = 0; i < len; ++i )
    result[i] = items[i];
  result[len] = item;
  free( items );
  return result;
}

/*@ requires len > 0;
  @ requires \valid( items+ ( 0..(len - 1) ) );
  @ assigns items[0..(len - 1)];
  @ ensures \valid( items+ ( 0..(len - 1) ) );
  @ ensures \forall integer k; 0 <= k < len ==> items[k] == k;
  */
void fillarr ( int* items, const int len )
{
  /*@ loop assigns i, items[i];
    @ loop invariant \forall integer k; 0 <= k < i ==> items[k] == k;
    @ loop variant len - i; */
  for ( int i = 0; i < len; ++i )
    items[i] = i;
}

/*@ requires len > 0;
  @ assigns \nothing; */
void printarr ( int* items, const int len )
{
  printf ( "array = [ " );
  /*@ loop assigns i;
    @ loop variant len - i; */
  for ( int i = 0; i < len - 1; i++ )
    printf ( "%d ,", items[i] );
  printf ( len > 0 ? "%d ]\n" : "]\n", items[len - 1] );
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
