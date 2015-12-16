#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Result holds iff array is a palindrome :)
//@ requires |chars| != 0
//@ ensures r <==> all { x in 0..|chars| | chars[x] == chars[|chars| - (x + 1)] }:
int isPalindrome(int chars[], unsigned int len )
{
    int i = 0;
    int j = len;
//@ where i + j == |chars| && i >= 0
//@ where all { k in 0..i | chars[k] == chars[|chars| - (k+1)] }:
  while ( i < j )
  {
    --j;
    if ( chars[i] != chars[j] )
      return 0;
    ++i;
  }
  return 1;
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
  int len = 5;
  int* res = malloc( len * sizeof(int) );
  fillarr( res, len );
  printarr( res, len );
  printf( isPalindrome( res, len ) ? " is " : " is not " );
  printf( " a Palindrome." );
}
