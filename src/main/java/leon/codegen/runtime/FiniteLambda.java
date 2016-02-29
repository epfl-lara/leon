/* Copyright 2009-2015 EPFL, Lausanne */

package leon.codegen.runtime;

import java.util.HashMap;

public final class FiniteLambda extends Lambda {
  public final HashMap<Tuple, Object> mapping = new HashMap<Tuple, Object>();
  public final Object dflt;

  public FiniteLambda(Object dflt) {
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
    } else {
      return dflt;
    }
  }

  @Override
  public boolean equals(Object that) {
    if (that != null && (that instanceof FiniteLambda)) {
      FiniteLambda l = (FiniteLambda) that;
      return dflt.equals(l.dflt) && mapping.equals(l.mapping);
    } else {
      return false;
    }
  }

  @Override
  public int hashCode() {
    return 63 + 11 * mapping.hashCode() + (dflt == null ? 0 : dflt.hashCode());
  }
}
