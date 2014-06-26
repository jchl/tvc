// tvc-args: --basic-blocks 0,2,5,9,2,5,9,2,12 --converges 1 --iterations 400 --skip-llvm-proof
int main() {
  int x = 0;
  for (int i = 0; i < 2; i = i + 1) {
    x = x + i;
  }
  return x;
}
