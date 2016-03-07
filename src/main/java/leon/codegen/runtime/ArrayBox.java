/* Copyright 2009-2016 EPFL, Lausanne */

package leon.codegen.runtime;

import java.util.Arrays;

public final class ArrayBox {
  private final Object[]  obj1;
  private final int[]     obj2;
  private final boolean[] obj3;
  private final int mode;

  protected final Object[] arrayValue() {
    return obj1;
  }

  protected final int[] arrayValueI() {
    return obj2;
  }

  protected final boolean[] arrayValueZ() {
    return obj3;
  }

  public ArrayBox(Object[] array) {
    obj1 = array;
    obj2 = null;
    obj3 = null;
    mode = 1;
  }

  public ArrayBox(int[] array) {
    obj1 = null;
    obj2 = array;
    obj3 = null;
    mode = 2;
  }

  public ArrayBox(boolean[] array) {
    obj1 = null;
    obj2 = null;
    obj3 = array;
    mode = 3;
  }

  @Override
  public boolean equals(Object that) {
    if(that == this) return true;
    if(!(that instanceof ArrayBox)) return false;

    ArrayBox other = (ArrayBox)that;

    if (mode == 1) {
        return (other.mode == 1) && Arrays.equals(this.obj1, other.obj1);
    } else if (mode == 2) {
        return (other.mode == 2) && Arrays.equals(this.obj2, other.obj2);
    } else {
        return (other.mode == 3) && Arrays.equals(this.obj3, other.obj3);
    }
  }

  @Override
  public String toString() {
    if (mode == 1) {
        return Arrays.toString(obj1);
    } else if (mode == 2) {
        return Arrays.toString(obj2);
    } else {
        return Arrays.toString(obj3);
    }
  }

  @Override
  public int hashCode() {
    if (mode == 1) {
        return Arrays.hashCode(obj1);
    } else if (mode == 2) {
        return Arrays.hashCode(obj2);
    } else {
        return Arrays.hashCode(obj3);
    }
  }
}
