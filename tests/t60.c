
#define INTERVAL(__p,__x,__a,__b) {if (__p) __x=__a; else __x=__b;}
int main(){
  char x,y,z1,z2,z3;
  char p1,p2;
  
  INTERVAL(p1,x,2,3);
  INTERVAL(p2,y,9,10);

  z1 = x | y; // [11,11]
  z2 = x & y; // [0,2]
  z3 = x ^ y; // [8,11]

  return 0;
}
