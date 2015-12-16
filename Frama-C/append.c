#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Append a single item onto the end of the array
/*@
  @ requires len >= 0;
  @ requires \valid( items+ (0..len-1) );
  @ assigns items+ (0..len-1);
  @ ensures \valid( items+ (0..len) );
  @ ensures \forall integer k; 0 <= k < len ==> \result[k] == \old(items[k]);
  @ ensures items[len] == item || items == \null;
  @*/
int* append(int* items, const size_t len, const int item)
{
  // The goal is to implement, specify and verify this function!
  int *temp = items;
  items = malloc( (len + 1) * sizeof(int) );
  if ( items == NULL )
  {
     fprintf( stderr, "append: Out Of Memory\n" );
     free( items );
     exit(1);
  }
  //@ assume \valid( items+ (0..len) );
  memcpy( items, temp, len * sizeof(int) );
  free( temp );
  //@ assert items != \null;
  items[len] = item;
  return items;
}
//@ assigns \nothing;
void fillarr( int* items, const size_t len )
{
  for ( int i = 0; i < len; ++i )
    items[i] = i;
}
//@ assigns \nothing;
void printarr( int* items, const size_t len )
{
  printf( "array = [ " );
  for(int i = 0; i < len - 1; i++)
    printf( "%d ,", items[i] );
  printf( len > 0 ? "%d ]\n" : "]\n", items[len - 1] );
}

int main()
{
  int len = 15;
  int* arr = malloc( len * sizeof(int) );
  fillarr( arr, len );

  printarr( arr, len );

  arr = append( arr, len, len );

  printarr( arr, len + 1 );

  free( arr );
  return 0;
}

