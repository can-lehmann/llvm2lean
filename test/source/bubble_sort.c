void bubble_sort(int* array, unsigned long length) {
  for (unsigned long i = 0; i < length; i++) {
    for (unsigned long j = 0; j + 1 < length - i; j++) {
      if (array[j] > array[j + 1]) {
        int tmp = array[j];
        array[j] = array[j + 1];
        array[j + 1] = tmp;
      }
    }
  }
}
