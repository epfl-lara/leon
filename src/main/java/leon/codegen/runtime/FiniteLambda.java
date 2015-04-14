/* Copyright 2009-2015 EPFL, Lausanne */

package leon.codegen.runtime;

import java.util.HashMap;

public final class FiniteLambda extends Lambda {
  private final HashMap<Tuple, Object> _underlying = new HashMap<Tuple, Object>();
  private final Object dflt;

  public FiniteLambda(Object dflt) {
    super();
    this.dflt = dflt;
  }

  public void add(Tuple key, Object value) {
    _underlying.put(key, value);
  }

  @Override
  public Object apply(Object[] args) {
    Tuple tuple = new Tuple(args);
    if (_underlying.containsKey(tuple)) {
      return _underlying.get(tuple);
    } else {
      return dflt;
    }
  }
}
