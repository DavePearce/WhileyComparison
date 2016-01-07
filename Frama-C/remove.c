#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Status: verifier "GC overhead limit exceeded"
// This function should remove the item at the given
// index from the items array, and return the resulting
// array otherwise unchanged.  The resulting array is of
// course one element shorter in length.
/*@
  @ requires index < len;
  @ requires len > 0;
  @ ensures \valid(\result+ (0..len-2) );
  @ ensures forall integer k; 0 <= k < index ==> \result[k] == \old(items[k]);
  @ ensures forall integer k; index <= k < (len-1) ==> r[k] == items[k + 1];
*/
int *remv( int items[], unsigned int len , unsigned int index)
{
  unsigned int newlen = len - 1;
  unsigned int i = index;
  int *temp = items;
  // items before index in result are still the same
  /*@
    @ where 0 <= i where i <= index
    @ where |result| == newlen
    @ where all { k in 0..i | k < index ==> result[k] == items[k] }
  */

  /*@
    @ where index <= i where i <= newlen
    @ where |result| == newlen
    @ where all { k in 0..index | result[k] == items[k] }
    @ where all { k in index..i | result[k] == items[k + 1] }
  */
  while ( i < newlen )
  // items after index in result are transposed by one place
  {
    items[i] = items[i + 1];
    ++i;
  }

  items = realloc( items, (len - 1) * sizeof(int) );
  //@ assert items == \null || \valid( items+ (0..len - 2) );
  if ( items == NULL )
  {
    items = malloc( (len - 1) * sizeof(int) );
    if ( items == NULL )
    {
       fprintf( stderr, "append: Out Of Memory\n" );
       free( items );
       exit(1);
    }
    memcpy( items, temp, (len - 1) * sizeof(int) );
    free( temp );
  }

  return items;
}
