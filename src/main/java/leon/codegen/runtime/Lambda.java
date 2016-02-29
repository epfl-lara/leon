/* Copyright 2009-2015 EPFL, Lausanne */

package leon.codegen.runtime;

public abstract class Lambda {
  public abstract Object apply(Object[] args) throws LeonCodeGenRuntimeException;
}
