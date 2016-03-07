/* Copyright 2009-2016 EPFL, Lausanne */

package leon.codegen.runtime;

import java.util.Arrays;

public final class Tuple {
  private int __read = 0;

  public final int __getRead() {
    return __read;
  }

  private final Object[] elements;

  // You may think that using varargs here would show less of the internals,
  // however the bytecode is exactly the same, so let's reflect the reality
  // instead.
  public Tuple(Object[] elements) {
    this.elements = Arrays.copyOf(elements, elements.length);
  }

  public final Object get(int index) {
    if(index < 0 || index >= this.elements.length) {
        throw new IllegalArgumentException("Invalid tuple index : " + index);
    }
    __read = (1 << (index)) | __read;

    return this.elements[index];
  }

  public final int getArity() {
    return this.elements.length;
  }

  @Override
  public boolean equals(Object that) {
    if(that == this) return true;
    if(!(that instanceof Tuple)) return false;
    Tuple other = (Tuple)that;
    if(other.getArity() != this.getArity()) return false;
    for(int i = 0; i < this.getArity(); i++) {
        if(!other.get(i).equals(this.get(i))) return false;
    }
    return true; 
  }

  private int _hash = 0;
  @Override
  final public int hashCode() {
    if(_hash != 0) return _hash;
    int seed = ("Tuple" + getArity()).hashCode();
    int h = LeonCodeGenRuntimeHashing.seqHash(elements, seed);
    _hash = h;
    return h;
  }

  @Override
  public String toString() {
    String str = "(";
    boolean first = true;
    for (Object obj : elements) {
      if (first) {
        first = false;
      } else {
        str += ", ";
      }
      str += obj == null ? "null" : obj.toString();
    }
    str += ")";
    return str;
  }
}
