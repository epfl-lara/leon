/* Copyright 2009-2016 EPFL, Lausanne */

package leon.codegen.runtime;

import java.util.Iterator;
import java.util.HashMap;

/** If someone wants to make it an efficient implementation of immutable
 *  sets, go ahead. */
public final class Bag {
  private final HashMap<Object, BigInt> _underlying;

  protected final HashMap<Object, BigInt> underlying() {
    return _underlying;
  }

  public Bag() {
    _underlying = new HashMap<Object, BigInt>();
  }

  private Bag(HashMap<Object, BigInt> u) {
    _underlying = u;
  }

  // Uses mutation! Useful at building time.
  public void add(Object e) {
    add(e, BigInt.ONE);
  }

  // Uses mutation! Useful at building time.
  public void add(Object e, BigInt count) {
    _underlying.put(e, get(e).add(count));
  }

  public Iterator<java.util.Map.Entry<Object, BigInt>> getElements() {
    return _underlying.entrySet().iterator();
  }

  public BigInt get(Object element) {
    BigInt r = _underlying.get(element);
    if (r == null) return BigInt.ZERO;
    else return r;
  }

  public Bag plus(Object e) {
    Bag n = new Bag(new HashMap<Object, BigInt>(_underlying));
    n.add(e);
    return n;
  }

  public Bag union(Bag b) {
    Bag n = new Bag(new HashMap<Object, BigInt>(_underlying));
    for (java.util.Map.Entry<Object, BigInt> entry : b.underlying().entrySet()) {
      n.add(entry.getKey(), entry.getValue());
    }
    return n;
  }

  public Bag intersect(Bag b) {
    Bag n = new Bag();
    for (java.util.Map.Entry<Object, BigInt> entry : _underlying.entrySet()) {
      BigInt b1 = entry.getValue(), b2 = b.get(entry.getKey());
      BigInt m = b1.lessThan(b2) ? b1 : b2;
      if (m.greaterThan(BigInt.ZERO)) n.add(entry.getKey(), m);
    }
    return n;
  }

  public Bag difference(Bag b) {
    Bag n = new Bag();
    for (java.util.Map.Entry<Object, BigInt> entry : _underlying.entrySet()) {
      BigInt m = entry.getValue().sub(b.get(entry.getKey()));
      if (m.greaterThan(BigInt.ZERO)) n.add(entry.getKey(), m);
    }
    return n;
  }

  @Override
  public boolean equals(Object that) {
    if(that == this) return true;
    if(!(that instanceof Bag)) return false;

    Bag other = (Bag) that;
    for (Object key : _underlying.keySet()) {
      if (!get(key).equals(other.get(key))) return false;
    }

    for (Object key : other.underlying().keySet()) {
      if (!get(key).equals(other.get(key))) return false;
    }

    return true;
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("Bag(");
    boolean first = true;
    for (java.util.Map.Entry<Object, BigInt> entry : _underlying.entrySet()) {
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
