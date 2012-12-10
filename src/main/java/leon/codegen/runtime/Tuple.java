package leon.codegen.runtime;

import java.util.Arrays;

public final class Tuple {
  private int arity;
  private Object[] elements;

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
