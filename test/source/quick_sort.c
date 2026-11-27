void quick_sort(int* array, long low, long high) {
  if (low >= high) {
    return;
  }
  int pivot = array[high];
  long i = low;
  for (long j = low; j < high; j++) {
    if (array[j] < pivot) {
      int tmp = array[i];
      array[i] = array[j];
      array[j] = tmp;
      i++;
    }
  }
  int tmp = array[i];
  array[i] = array[high];
  array[high] = tmp;
  quick_sort(array, low, i - 1);
  quick_sort(array, i + 1, high);
}
