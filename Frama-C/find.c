#include <stdio.h>
#include <stdlib.h>
#include <string.h>

//requires len < |arr|
//// arr is an ordered array
//requires all { k in 0..len - 1 | arr[k] <= arr[k + 1] }
//// return value should not exceed len
//ensures r <= len
//// index of place of insertion is returned
//ensures all { k in 0..r | arr[k] <  val }

unsigned int findIns(int arr[], int val, unsigned int len)
{
  unsigned int i = 0;

  //@ where all { k in 0..i | arr[k] < val }
  //@ where i <= len
  while ( i < len )
  {
    if ( arr[i] >= val )
    { //@ assert all { k in i..len | arr[k] >= val }
      return i;
    }
    ++i;
  }
  return i;
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
    int arr[] = { 1,2,3,4,5 };
    findIns( arr, 3, 5 );
    printarr( arr, 5 );
}
