// Case with overflow
int foo(int x, int y){
  x=3;
  y=23456789;
    
  while (x <= y){
      x = x << 15;
  }
  return x;
}

int main(){
  int x,y;
  printf("%d\n",foo(x,y));
  return 0;
}
