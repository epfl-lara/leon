/* Copyright 2009-2015 EPFL, Lausanne */

package leon.codegen.runtime;

import java.util.HashMap;

public final class PartialLambda extends Lambda {
  final HashMap<Tuple, Object> mapping = new HashMap<Tuple, Object>();
  private final Object dflt;

  public PartialLambda() {
    this(null);
  }

  public PartialLambda(Object dflt) {
    super();
    this.dflt = dflt;
  }

  public void add(Tuple key, Object value) {
    mapping.put(key, value);
  }

  @Override
  public Object apply(Object[] args) throws LeonCodeGenRuntimeException {
    Tuple tuple = new Tuple(args);
    if (mapping.containsKey(tuple)) {
      return mapping.get(tuple);
    } else if (dflt != null) {
      return dflt;
    } else {
      throw new LeonCodeGenRuntimeException("Partial function apply on undefined arguments");
    }
  }

  @Override
  public boolean equals(Object that) {
    if (that != null && (that instanceof PartialLambda)) {
      PartialLambda l = (PartialLambda) that;
      return ((dflt != null && dflt.equals(l.dflt)) || (dflt == null && l.dflt == null)) && mapping.equals(l.mapping);
    } else {
      return false;
    }
  }

  @Override
  public int hashCode() {
    return 63 + 11 * mapping.hashCode() + (dflt == null ? 0 : dflt.hashCode());
  }

  @Override
  public void checkForall(boolean[] quantified) {}
}
