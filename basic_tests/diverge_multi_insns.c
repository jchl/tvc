// tvc-args: --skip-core-proof
// XXX The generalized tid doesn't play well with evaluation of memory actions
int main() {
  int x = 1;
  while (1) {
    x = 1;
  }
}
