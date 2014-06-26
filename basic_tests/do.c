// tvc-args: --basic-blocks 0,2,5,2,5,2,5,8 --converges 0 --iterations 400 --skip-llvm-proof
int main() {
  int x = 3;
  do {
    x = x - 1;
  } while (x);
  return x;
}
