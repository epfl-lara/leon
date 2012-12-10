package leon.codegen.runtime;

import java.util.Arrays;
import java.util.TreeMap;

/** If someone wants to make it an efficient implementation of immutable
 *  sets, go ahead. */
public final class Map {
  private final TreeMap<Object,Object> _underlying;

  protected final TreeMap<Object,Object> underlying() {
    return _underlying;
  }

  public Map() {
    _underlying = new TreeMap<Object,Object>();
  }

  // For Maps, it's simpler to build them by starting with empty and putting
  // the elements in.
  public void add(Object key, Object value) {
    _underlying.put(key, value);
  }

  private Map(TreeMap<Object,Object> u) {
    _underlying = u;
  }

  public boolean isDefinedAt(Object element) {
    return underlying().containsKey(element);
  }

  public Object get(Object k) throws LeonCodeGenRuntimeException {
    Object result = underlying().get(k);
    if(result == null) {
      throw new LeonCodeGenRuntimeException("Get of undefined key.");
    }
    return result;
  }

  public int size() {
    return underlying().size();
  }

  public Map union(Map s) {
    TreeMap<Object,Object> n = new TreeMap<Object,Object>(underlying());
    n.putAll(s.underlying());
    return new Map(n);
  }
}
