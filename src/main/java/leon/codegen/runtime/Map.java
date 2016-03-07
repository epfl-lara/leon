/* Copyright 2009-2016 EPFL, Lausanne */

package leon.codegen.runtime;

import java.util.Iterator;
import java.util.HashMap;

/** If someone wants to make it an efficient implementation of immutable
 *  maps, go ahead. */
public final class Map {
  private final HashMap<Object,Object> _underlying;

  protected final HashMap<Object,Object> underlying() {
    return _underlying;
  }

  public Map() {
    _underlying = new HashMap<Object,Object>();
  }

  private Map(HashMap<Object,Object> u) {
    _underlying = u;
  }

  // Uses mutation! Useful at building time.
  public void add(Object key, Object value) {
    _underlying.put(key, value);
  }

  public Iterator<java.util.Map.Entry<Object,Object>> getElements() {
    return _underlying.entrySet().iterator();
  }

  public boolean isDefinedAt(Object element) {
    return _underlying.containsKey(element);
  }

  public Object get(Object k) throws LeonCodeGenRuntimeException {
    Object result = _underlying.get(k);
    if(result == null) {
      throw new LeonCodeGenRuntimeException("Get of undefined key.");
    }
    return result;
  }

  public int size() {
    return _underlying.size();
  }

  public Map union(Map s) {
    HashMap<Object,Object> n = new HashMap<Object,Object>(_underlying);
    n.putAll(s.underlying());
    return new Map(n);
  }

  @Override
  public boolean equals(Object that) {
    if(that == this) return true;
    if(!(that instanceof Map)) return false;

    Map other = (Map)that;

    if(this.size() != other.size()) return false;

    for(java.util.Map.Entry<Object,Object> entry : _underlying.entrySet()) {
      Object there = other.underlying().get(entry.getKey());
      if(there == null || !entry.getValue().equals(there)) return false;     
    }

    return true;
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("Map(");
    boolean first = true;
    for(java.util.Map.Entry<Object,Object> entry : _underlying.entrySet()) {
      if(!first) {
        sb.append(", ");
        first = false;
      }
      sb.append(entry.getKey().toString());
      sb.append(" -> ");
      sb.append(entry.getValue().toString());
    }
    sb.append(")");
    return sb.toString();
  }

  @Override
  public int hashCode() {
    return _underlying.hashCode();
  }
}
