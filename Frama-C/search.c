#include <stdio.h>
// A linear search over a sorted array looking for a given element.

/*@ requires 0 < len;
  @ requires \valid( ls+ ( 0..(len - 1) ) );
  @ requires \forall size_t k; 0 <= k < (len - 1) ==> ls[k] <= ls[k + 1];
  @ assigns \nothing;
  @ behavior found:
  @   assumes \exists size_t k; 0 <= k < len && ls[k] == item;
  @   ensures 0 <= \result < len;
  @ behavior nfound:
  @   assumes \forall size_t k; 0 <= k < len ==> ls[k] != item;
  @   ensures \result == -1;
  @ complete behaviors found, nfound;
  @ disjoint behaviors found, nfound;
  */
int search( int ls[], const int len, int item )
{
  size_t i = 0;

  /*@ loop invariant 0 <= i <= len;
    @ loop invariant \forall size_t k; 0 <= k < i ==> ls[k] != item;
    @ loop assigns i;
    @ loop variant len - i;
    */
  while ( i < len )
  {
    if ( ls[i] == item )
      return i;
    ++i;
  }
  return -1;
}

int main()
{
  int src[] = { 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 };
  if ( search( src, 10, 5 ) >= 0 ) printf( "found item" );
  else printf( "no item found" );
}
