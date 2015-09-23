/* Copyright 2009-2015 EPFL, Lausanne */

package leon.codegen.runtime;

import java.util.List;
import java.util.LinkedList;
import java.util.HashMap;

public class LeonCodeGenRuntimeHenkinMonitor extends LeonCodeGenRuntimeMonitor {
  private final HashMap<Integer, List<Tuple>> domains = new HashMap<Integer, List<Tuple>>();

  public LeonCodeGenRuntimeHenkinMonitor(int maxInvocations) {
    super(maxInvocations);
  }

  public void add(int type, Tuple input) {
    if (!domains.containsKey(type)) domains.put(type, new LinkedList<Tuple>());
    domains.get(type).add(input);
  }

  public List<Tuple> domain(Object obj, int type) {
    List<Tuple> domain = new LinkedList<Tuple>();
    if (obj instanceof PartialLambda) {
      for (Tuple key : ((PartialLambda) obj).mapping.keySet()) {
        domain.add(key);
      }
    }

    List<Tuple> tpeDomain = domains.get(type);
    if (tpeDomain != null) domain.addAll(tpeDomain);

    return domain;
  }
}
