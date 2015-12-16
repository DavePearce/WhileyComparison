#include <stdio.h>

// Calculate length of string
/*@
  @ assigns \nothing;
  @ ensures str[\result] == '\0'; */
unsigned int strlength( const char* str )
{
  unsigned int i = 0;
  /*@ loop invariant i >= 0;
    @ loop invariant \forall integer k; 0 <= k < i ==> str[k] != '\0'; */
  while ( str[i] != '\0' ) ++i;

  return i;
}

void printarr( const char* items )
{
  printf( "array = [ " );
  printf( items );
  printf( " ]\n" );
}

int main()
{
  const char* res = "ABCDEFGHIJKLMNOP";
  printarr( res );
  printf( " has length of %d\n", strlength( res ) );
}
