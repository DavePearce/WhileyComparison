#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// If result is positive, element at that position must match item
//@ ensures r >= 0 ==> items[r] == item
// If result is positive, no element at greater position matches item
//@ ensures r >= 0 ==> all { x in (r + 1)..|items| | items[x] != item }
// If result is negative, no element matches item
//@ ensures r < 0 ==> no { x in 0..|items| | items[x] == item }:
int lastIndexOf( int items[], const unsigned int len, const int item )
{
    int i = len;
    // i is decreasing and no element at greater position matches item
    //@    where i <= |items|;
    //@    where no { x in i..|items| | items[x] == item };
    while ( i > 0 )
    {
        --i;
        if ( items[i] == item )
            return i;
    }
    // didn't find item in entire list
    return -1;
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
    printf( "last index of %d is %d", len, lastIndexOf( res, len, 3 ) );
}
