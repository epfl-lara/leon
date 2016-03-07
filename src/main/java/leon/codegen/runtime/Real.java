/* Copyright 2009-2016 EPFL, Lausanne */

package leon.codegen.runtime;

import java.math.BigInteger;
import java.math.BigDecimal;

public final class Real {

  private final BigDecimal _underlying;

  public final BigDecimal underlying() {
    return _underlying;
  }

  private Real(BigDecimal value) {
    _underlying = value;
  }

  public Real(String value) {
    _underlying = new BigDecimal(value);
  }

  public Real add(Real that) {
    return new Real(_underlying.add(that.underlying()));
  }

  public Real sub(Real that) {
    return new Real(_underlying.subtract(that.underlying()));
  }

  public Real mult(Real that) {
    return new Real(_underlying.multiply(that.underlying()));
  }

  public Real div(Real that) {
    return new Real(_underlying.divide(that.underlying()));
  }

  public Real neg() {
    return new Real(_underlying.negate());
  }


  public boolean lessThan(Real that) {
    return _underlying.compareTo(that.underlying()) < 0;
  }

  public boolean lessEquals(Real that) {
    return _underlying.compareTo(that.underlying()) <= 0;
  }

  public boolean greaterThan(Real that) {
    return _underlying.compareTo(that.underlying()) > 0;
  }

  public boolean greaterEquals(Real that) {
    return _underlying.compareTo(that.underlying()) >= 0;
  }


  @Override
  public boolean equals(Object that) {
    if(that == this) return true;
    if(!(that instanceof Real)) return false;

    Real other = (Real)that;
    return this.underlying().equals(other.underlying());
  }

  @Override
  public String toString() {
    return _underlying.toString();
  }

  @Override
  public int hashCode() {
    return _underlying.hashCode();
  }

}
