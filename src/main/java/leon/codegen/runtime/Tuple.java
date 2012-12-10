package leon.codegen.runtime;

import java.util.Arrays;

public final class Tuple {
  private int arity;
  private Object[] elements;

  // You may think that using varargs here would show less of the internals,
  // however the bytecode to generate is exactly the same, so let's reflect
  // the reality instead.
  public Tuple(int arity, Object[] elements) {
    this.arity = arity;
    this.elements = Arrays.copyOf(elements, elements.length);
  }

  public final Object get(int index) {
    if(index < 0 || index >= arity) {
        throw new IllegalArgumentException("Invalid tuple index : " + index);
    }
    return this.elements[index];
  }
}
