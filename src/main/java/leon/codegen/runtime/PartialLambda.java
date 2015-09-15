/* Copyright 2009-2015 EPFL, Lausanne */

package leon.codegen.runtime;

import java.util.HashMap;

public final class PartialLambda extends Lambda {
  final HashMap<Tuple, Object> mapping = new HashMap<Tuple, Object>();

  public PartialLambda() {
    super();
  }

  public void add(Tuple key, Object value) {
    mapping.put(key, value);
  }

  @Override
  public Object apply(Object[] args) throws LeonCodeGenRuntimeException {
    Tuple tuple = new Tuple(args);
    if (mapping.containsKey(tuple)) {
      return mapping.get(tuple);
    } else {
      throw new LeonCodeGenRuntimeException("Partial function apply on undefined arguments");
    }
  }

  @Override
  public boolean equals(Object that) {
    if (that != null && (that instanceof PartialLambda)) {
      return mapping.equals(((PartialLambda) that).mapping);
    } else {
      return false;
    }
  }

  @Override
  public int hashCode() {
    return 63 + 11 * mapping.hashCode();
  }
}
