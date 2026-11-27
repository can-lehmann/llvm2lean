void merge(int* array, int* buffer, long low, long mid, long high) {
  long i = low;
  long j = mid;
  long k = low;
  while (i < mid && j < high) {
    if (array[j] < array[i]) {
      buffer[k++] = array[j++];
    } else {
      buffer[k++] = array[i++];
    }
  }
  while (i < mid) {
    buffer[k++] = array[i++];
  }
  while (j < high) {
    buffer[k++] = array[j++];
  }
  for (long l = low; l < high; l++) {
    array[l] = buffer[l];
  }
}

void merge_sort(int* array, int* buffer, long low, long high) {
  if (high - low < 2) {
    return;
  }
  long mid = low + (high - low) / 2;
  merge_sort(array, buffer, low, mid);
  merge_sort(array, buffer, mid, high);
  merge(array, buffer, low, mid, high);
}
