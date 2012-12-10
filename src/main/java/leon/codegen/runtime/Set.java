package leon.codegen.runtime;

import java.util.Arrays;
import java.util.Iterator;
import java.util.TreeSet;

/** If someone wants to make it an efficient implementation of immutable
 *  sets, go ahead. */
public final class Set {
  private final TreeSet<Object> _underlying;

  protected final TreeSet<Object> underlying() {
    return _underlying;
  }

  public Set() {
    _underlying = new TreeSet<Object>();
  }

  public Set(Object[] elements) {
    _underlying = new TreeSet<Object>(Arrays.asList(elements));
  }

  // Uses mutation!
  public void add(Object e) {
    _underlying.add(e);
  }

  public Iterator<Object> getElements() {
    return _underlying.iterator();
  }

  private Set(TreeSet<Object> u) {
    _underlying = u;
  }

  public boolean contains(Object element) {
    return _underlying.contains(element);
  }

  public boolean subsetOf(Set s) {
    for(Object o : _underlying) {
      if(!s.underlying().contains(o)) {
        return false;
      }
    }
    return true;
  }

  public int size() {
    return _underlying.size();
  }

  public Set union(Set s) {
    TreeSet<Object> n = new TreeSet<Object>(underlying());
    n.addAll(s.underlying());
    return new Set(n);
  }

  public Set intersect(Set s) {
    TreeSet<Object> n = new TreeSet<Object>();
    for(Object o : _underlying) {
      if(s.underlying().contains(o)) {
        n.add(o);
      }
    }
    return new Set(n);
  }

  public Set minus(Set s) {
    TreeSet<Object> n = new TreeSet<Object>(_underlying);
    for(Object o : s.underlying()) {
      n.remove(o);
    }
    return new Set(n);
  }
}
