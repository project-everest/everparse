#include<stdio.h>
#include<stdlib.h>

#include "ExternVector_ExternalTypedefs.h"
#include "ExternVectorWrapper.h"

void ExternVectorEverParseError(const char *StructName, const char *FieldName, const char *Reason)
{
  return;
}

void Push (VEC *vec, uint32_t x, uint32_t y)
{
  if(vec->max == vec->cur) {
    return;
  } else {
    (vec->arr[vec->cur]).x = x;
    (vec->arr[vec->cur]).y = y;
    vec->cur = vec->cur+1;    
  }
}

VEC *Alloc ()
{
  VEC *vec = (VEC *) malloc(sizeof(VEC));
  vec->max = 2;
  vec->cur = 0;
  vec->arr = (POINT_T *) malloc(sizeof(POINT_T) * 2);
  return vec;
}

int main ()
{
  uint8_t *data = malloc(sizeof(uint8_t) + sizeof(uint32_t) * 6);
  data[0] = 3;
  uint32_t *arr = (uint32_t *) (data + 1);
  arr[0] = 0;
  arr[1] = 1;
  arr[2] = 2;
  arr[3] = 3;
  arr[4] = 4;
  arr[5] = 5;

  VEC *vec = Alloc();
  
  BOOLEAN b = ExternVectorCheckT(vec, (uint8_t *) data, sizeof(uint8_t) + sizeof(uint32_t) * 6);
  if(b &&
     vec->cur == 2      &&
     vec->arr[0].x == 0 &&
     vec->arr[0].y == 1 &&
     vec->arr[1].x == 2 &&
     vec->arr[1].y == 3) {
    printf("%s\n", "Validation succeeded for extern vector");
    return 0;
  } else {
    printf("%s\n", "Validation failed for extern vector");
    return 1;
  }
}
