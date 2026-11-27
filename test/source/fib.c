unsigned long fib(unsigned long n) {
  unsigned long a = 0;
  unsigned long b = 1;
  for (unsigned long i = 0; i < n; i++) {
    unsigned long t = a + b;
    a = b;
    b = t;
  }
  return a;
}
