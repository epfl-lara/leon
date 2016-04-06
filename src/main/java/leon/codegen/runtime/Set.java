/* Copyright 2009-2016 EPFL, Lausanne */

package leon.codegen.runtime;

import java.util.Arrays;
import java.util.Iterator;
import java.util.HashSet;

/** If someone wants to make it an efficient implementation of immutable
 *  sets, go ahead. */
public final class Set {
  private final HashSet<Object> _underlying;

  protected final HashSet<Object> underlying() {
    return _underlying;
  }

  public Set() {
    _underlying = new HashSet<Object>();
  }

  public Set(Object[] elements) {
    _underlying = new HashSet<Object>(Arrays.asList(elements));
  }

  private Set(HashSet<Object> u) {
    _underlying = u;
  }

  // Uses mutation! Useful at building time.
  public void add(Object e) {
    _underlying.add(e);
  }

  public Iterator<Object> getElements() {
    return _underlying.iterator();
  }

  public boolean contains(Object element) {
    return _underlying.contains(element);
  }

  public Set plus(Object e) {
    Set n = new Set(new HashSet<Object>(_underlying));
    n.add(e);
    return n;
  }

  public boolean subsetOf(Set s) {
    for(Object o : _underlying) {
      if(!s.underlying().contains(o)) {
        return false;
      }
    }
    return true;
  }

  public BigInt size() {
    return new BigInt(""+_underlying.size());
  }

  public Set union(Set s) {
    HashSet<Object> n = new HashSet<Object>(_underlying);
    n.addAll(s.underlying());
    return new Set(n);
  }

  public Set intersect(Set s) {
    HashSet<Object> n = new HashSet<Object>();
    for(Object o : _underlying) {
      if(s.underlying().contains(o)) {
        n.add(o);
      }
    }
    return new Set(n);
  }

  public Set minus(Set s) {
    HashSet<Object> n = new HashSet<Object>(_underlying);
    for(Object o : s.underlying()) {
      n.remove(o);
    }
    return new Set(n);
  }

  @Override
  public boolean equals(Object that) {
    if(that == this) return true;
    if(!(that instanceof Set)) return false;

    Set other = (Set)that;

    return this.size().equals(other.size()) && this.subsetOf(other);
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("Set(");
    boolean first = true;
    for(Object o : _underlying) {
      if(!first) {
        sb.append(", ");
        first = false;
      }
      sb.append(o.toString());
    }
    sb.append(")");
    return sb.toString();
  }

  @Override
  public int hashCode() {
    return _underlying.hashCode();
  }
}
