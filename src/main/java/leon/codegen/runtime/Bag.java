/* Copyright 2009-2016 EPFL, Lausanne */

package leon.codegen.runtime;

import java.util.Arrays;
import java.util.Iterator;
import java.util.HashMap;

/** If someone wants to make it an efficient implementation of immutable
 *  sets, go ahead. */
public final class Bag {
  private final HashMap<Object, Integer> _underlying;

  protected final HashMap<Object, Integer> underlying() {
    return _underlying;
  }

  public Bag() {
    _underlying = new HashMap<Object, Integer>();
  }

  private Bag(HashMap<Object, Integer> u) {
    _underlying = u;
  }

  // Uses mutation! Useful at building time.
  public void add(Object e) {
    add(e, 1);
  }

  // Uses mutation! Useful at building time.
  private void add(Object e, int count) {
    _underlying.put(e, get(e) + count);
  }

  public Iterator<java.util.Map.Entry<Object, Integer>> getElements() {
    return _underlying.entrySet().iterator();
  }

  public int get(Object element) {
    Integer r = _underlying.get(element);
    if (r == null) return 0;
    else return r.intValue();
  }

  public Bag plus(Object e) {
    Bag n = new Bag(new HashMap<Object, Integer>(_underlying));
    n.add(e);
    return n;
  }

  public Bag union(Bag b) {
    Bag n = new Bag(new HashMap<Object, Integer>(_underlying));
    for (java.util.Map.Entry<Object, Integer> entry : b.underlying().entrySet()) {
      n.add(entry.getKey(), entry.getValue());
    }
    return n;
  }

  public Bag intersect(Bag b) {
    Bag n = new Bag();
    for (java.util.Map.Entry<Object, Integer> entry : _underlying.entrySet()) {
      int m = Math.min(entry.getValue(), b.get(entry.getKey()));
      if (m > 0) n.add(entry.getKey(), m);
    }
    return n;
  }

  public Bag difference(Bag b) {
    Bag n = new Bag();
    for (java.util.Map.Entry<Object, Integer> entry : _underlying.entrySet()) {
      int m = entry.getValue() - b.get(entry.getKey());
      if (m > 0) n.add(entry.getKey(), m);
    }
    return n;
  }

  @Override
  public boolean equals(Object that) {
    if(that == this) return true;
    if(!(that instanceof Bag)) return false;

    Bag other = (Bag) that;
    for (Object key : _underlying.keySet()) {
      if (get(key) != other.get(key)) return false;
    }

    for (Object key : other.underlying().keySet()) {
      if (get(key) != other.get(key)) return false;
    }

    return true;
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("Bag(");
    boolean first = true;
    for (java.util.Map.Entry<Object, Integer> entry : _underlying.entrySet()) {
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
