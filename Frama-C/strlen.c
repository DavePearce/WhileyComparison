#include <stdio.h>
#include <string.h>

// Calculate length of string
/*@ requires \exists integer k; 0 <= k <= strlen(str) && str[k] == '\0';
  @ assigns \nothing; // neither changes the arguments nor any objects outside the scope.
  @ ensures \result == strlen(str) + 1;
  @ ensures str[\result] == '\0';
  @ ensures \forall integer k; 0 <= k < \result ==> str[k] != '\0'; */
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
