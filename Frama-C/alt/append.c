#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Append a single item onto the end of the array
/*@ requires len > 0;
  @ requires \valid( items+ (0..(len - 1) ) );
  @ assigns items[0..len];
  @ ensures \valid( items+ (0..len) );
  @ ensures \forall integer k; 0 <= k < len ==> \result[k] == \old(items[k]);
  @ ensures items[len] == item;
  @*/
int* append ( int* items, const int len, const int item )
{
  // The goal is to implement, specify and verify this function!
  int *temp = items;
  items = malloc ( ( len + 1 ) * sizeof ( int ) );
  if ( items == NULL )
  {
    fprintf ( stderr, "append: Out Of Memory\n" );
    free ( items );
    exit ( 1 );
  }
  //@ assert \valid( items+ (0..len) );
  memcpy ( items, temp, len * sizeof ( int ) );
  free ( temp );
  //@ assert items != \null;
  items[len] = item;
  return items;
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
    @ loop variant (len - 1) - i; */
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

