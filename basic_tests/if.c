// tvc-args: --basic-blocks 0,4,6
int main() {
  int x = 1;
  if (x) {
    return 1;
  } else {
    return 2;
  }
}
