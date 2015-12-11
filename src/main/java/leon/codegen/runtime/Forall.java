/* Copyright 2009-2015 EPFL, Lausanne */

package leon.codegen.runtime;

import java.util.HashMap;

public abstract class Forall {
  private static final HashMap<Tuple, Boolean> cache = new HashMap<Tuple, Boolean>();

  protected final LeonCodeGenRuntimeHenkinMonitor monitor;
  protected final Tuple closures;
  protected final boolean check;

  public Forall(LeonCodeGenRuntimeMonitor monitor, Tuple closures) throws LeonCodeGenEvaluationException {
    if (!(monitor instanceof LeonCodeGenRuntimeHenkinMonitor))
      throw new LeonCodeGenEvaluationException("Can't evaluate foralls without domain");

    this.monitor = (LeonCodeGenRuntimeHenkinMonitor) monitor;
    this.closures = closures;
    this.check = (boolean) closures.get(closures.getArity() - 1);
  }

  public boolean check() {
    Tuple key = new Tuple(new Object[] { getClass(), monitor, closures }); // check is in the closures
    if (cache.containsKey(key)) {
      return cache.get(key);
    } else {
      boolean res = checkForall();
      cache.put(key, res);
      return res;
    }
  }

  public abstract boolean checkForall();
}
