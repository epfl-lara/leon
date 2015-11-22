/* Copyright 2009-2015 EPFL, Lausanne */

package leon.codegen.runtime;

import java.util.List;
import java.util.LinkedList;
import java.util.HashMap;

public class LeonCodeGenRuntimeHenkinMonitor extends LeonCodeGenRuntimeMonitor {
  private final HashMap<Integer, List<Tuple>> tpes = new HashMap<Integer, List<Tuple>>();
  private final HashMap<Class<?>, List<Tuple>> lambdas = new HashMap<Class<?>, List<Tuple>>();
  public final boolean checkForalls;

  public LeonCodeGenRuntimeHenkinMonitor(int maxInvocations, boolean checkForalls) {
    super(maxInvocations);
    this.checkForalls = checkForalls;
  }

  public LeonCodeGenRuntimeHenkinMonitor(int maxInvocations) {
    this(maxInvocations, false);
  }

  public void add(int type, Tuple input) {
    if (!tpes.containsKey(type)) tpes.put(type, new LinkedList<Tuple>());
    tpes.get(type).add(input);
  }

  public void add(Class<?> clazz, Tuple input) {
    if (!lambdas.containsKey(clazz)) lambdas.put(clazz, new LinkedList<Tuple>());
    lambdas.get(clazz).add(input);
  }

  public List<Tuple> domain(Object obj, int type) {
    List<Tuple> domain = new LinkedList<Tuple>();
    if (obj instanceof PartialLambda) {
      PartialLambda l = (PartialLambda) obj;
      for (Tuple key : l.mapping.keySet()) {
        domain.add(key);
      }
    } else if (obj instanceof Lambda) {
      List<Tuple> lambdaDomain = lambdas.get(obj.getClass());
      if (lambdaDomain != null) domain.addAll(lambdaDomain);
    }

    List<Tuple> tpeDomain = tpes.get(type);
    if (tpeDomain != null) domain.addAll(tpeDomain);

    return domain;
  }
}
