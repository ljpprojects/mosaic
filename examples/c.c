typedef struct {
  double x;
  double y;
} Vector;

double vector_dot_product(Vector *a, Vector *b) {
  return a->x * b->x + a->y * b->y;
}