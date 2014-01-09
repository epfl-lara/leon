/* Copyright 2009-2013 EPFL, Lausanne */

package leon.codegen.runtime;

import java.util.Arrays;

public final class Array {
  private int __read = 0;

  public final int __getRead() {
    return __read;
  }

  private final Object[] elements;

  // You may think that using varargs here would show less of the internals,
  // however the bytecode is exactly the same, so let's reflect the reality
  // instead.
  public Array(Object[] elements) {
    this.elements = Arrays.copyOf(elements, elements.length);
  }

  public final Object get(int index) {
    if(index < 0 || index >= this.elements.length) {
        throw new ArrayIndexOutOfBoundsException("Invalid array index : " + index);
    }
    __read = (1 << (index)) | __read;

    return this.elements[index];
  }

  public final int getLength() {
    return this.elements.length;
  }

  @Override
  public boolean equals(Object that) {
    if(that == this) return true;
    if(!(that instanceof Array)) return false;
    Array other = (Array)that;
    if(other.getLength() != this.getLength()) return false;
    for(int i = 0; i < this.getLength(); i++) {
        if(!other.get(i).equals(this.get(i))) return false;
    }
    return true; 
  }

  private int _hash = 0;
  @Override
  final public int hashCode() {
    if(_hash != 0) return _hash;
    int seed = (new String("Array" + getLength())).hashCode();
    int h = LeonCodeGenRuntimeHashing.seqHash(elements, seed);
    _hash = h;
    return h;
  }
}
