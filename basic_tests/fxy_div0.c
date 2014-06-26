// tvc-args: --main f
int f(int x, int y) {
  return 1 / 0;
}

// This is here just to keep csem happy.
int main() {
  return 0;
}
