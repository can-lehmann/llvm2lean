void* malloc(unsigned long size);
void free(void* ptr);

struct node {
  int value;
  struct node* left;
  struct node* right;
};

struct node* heap_merge(struct node* a, struct node* b) {
  if (a == 0) {
    return b;
  }
  if (b == 0) {
    return a;
  }
  if (b->value < a->value) {
    struct node* tmp = a;
    a = b;
    b = tmp;
  }
  struct node* merged = heap_merge(a->right, b);
  a->right = a->left;
  a->left = merged;
  return a;
}

struct node* heap_push(struct node* heap, int value) {
  struct node* node = malloc(sizeof(struct node));
  node->value = value;
  node->left = 0;
  node->right = 0;
  return heap_merge(heap, node);
}

struct node* heap_pop(struct node* heap) {
  struct node* rest = heap_merge(heap->left, heap->right);
  free(heap);
  return rest;
}

void heap_sort(int* array, unsigned long length) {
  struct node* heap = 0;
  for (unsigned long i = 0; i < length; i++) {
    heap = heap_push(heap, array[i]);
  }
  for (unsigned long i = 0; i < length; i++) {
    array[i] = heap->value;
    heap = heap_pop(heap);
  }
}
