// tvc-args: --basic-blocks 0,2,5,2,5,2,8 --converges 0 --iterations 400 --skip-llvm-proof
int main() {
  int x = 2;
  while (x) {
    x = x - 1;
  }
  return x;
}
