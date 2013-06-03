// left shift operator: simple case no overflow.

#define INTERVAL(__p,__x,__a,__b) {if (__p) __x=__a; else __x=__b;}

int main(){

  int p1,p2;
  int x1,y1;

  INTERVAL(p1,x1,-10,20); 
  INTERVAL(p2,y1,0,23456789); 
    
  while (x1 < y1){
      x1 = x1 << 4;
  }
  return x1;
}

