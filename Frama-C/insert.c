#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// This function should insert the item at the given
// index from the items array.  The resulting array is of
// course one element longer in length.
//  requires index < len
//  requires len > 0
//  ensures |r| == len + 1
//  ensures all { k in 0..index | r[k] == items[k] }
//  ensures r[index] == item
//  ensures all { k in index..len | r[k] == items[k - 1] }
void insert( int items[], unsigned int len, int item, unsigned int index )
{
  // length of the new array
  unsigned int newlen = len + 1;
  unsigned int i = len;
    int *temp = items;
  items = realloc( items, newlen * sizeof(int) );
  if ( items == NULL )
  {
    items = malloc( newlen * sizeof(int) );
    if ( items == NULL )
    {
      fprintf( stderr, "append: Out Of Memory\n" );
      free( items );
      exit(1);
    }
    memcpy( items, temp, len * sizeof(int) );
    free( temp );
  }

  while ( index < i )
  {
    items[i] = items[i - 1];
    --i;
  }
  items[i] = item;
}

void fillarr( int* items, int len )
{
  for ( int i = 0; i < len; ++i )
    items[i] = i;
}

void printarr( int* items, int len )
{
  printf( "array = [ " );
  for(int i = 0; i < len - 1; i++)
    printf( "%d ,", items[i] );
  printf( len > 0 ? "%d ]\n" : "]\n", items[len - 1] );
}

int main()
{
    int* res = malloc( 5 * sizeof(int) );
    fillarr( res, 5 );
    printarr( res, 5 );
    insert( res, 5, 1, 3 );
    printarr( res, 6 );
}
