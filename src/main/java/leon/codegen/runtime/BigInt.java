/* Copyright 2009-2016 EPFL, Lausanne */

package leon.codegen.runtime;

import java.math.BigInteger;

public final class BigInt {
  public static final BigInt ZERO = new BigInt(BigInteger.ZERO);
  public static final BigInt ONE  = new BigInt(BigInteger.ONE);

  private final BigInteger _underlying;

  public final BigInteger underlying() {
    return _underlying;
  }

  private BigInt(BigInteger value) {
    _underlying = value;
  }
  public BigInt(String value) {
    _underlying = new BigInteger(value);
  }

  public BigInt add(BigInt that) {
    return new BigInt(_underlying.add(that.underlying()));
  }

  public BigInt sub(BigInt that) {
    return new BigInt(_underlying.subtract(that.underlying()));
  }

  public BigInt mult(BigInt that) {
    return new BigInt(_underlying.multiply(that.underlying()));
  }

  public BigInt div(BigInt that) {
    return new BigInt(_underlying.divide(that.underlying()));
  }

  public BigInt rem(BigInt that) {
    return new BigInt(_underlying.remainder(that.underlying()));
  }

  public BigInt mod(BigInt that) {
    if(that.underlying().compareTo(new BigInteger("0")) < 0)
      return new BigInt(_underlying.mod(that.underlying().negate()));
    else
      return new BigInt(_underlying.mod(that.underlying()));
  }

  public BigInt neg() {
    return new BigInt(_underlying.negate());
  }


  public boolean lessThan(BigInt that) {
    return _underlying.compareTo(that.underlying()) < 0;
  }

  public boolean lessEquals(BigInt that) {
    return _underlying.compareTo(that.underlying()) <= 0;
  }

  public boolean greaterThan(BigInt that) {
    return _underlying.compareTo(that.underlying()) > 0;
  }

  public boolean greaterEquals(BigInt that) {
    return _underlying.compareTo(that.underlying()) >= 0;
  }


  @Override
  public boolean equals(Object that) {
    if(that == this) return true;
    if(!(that instanceof BigInt)) return false;

    BigInt other = (BigInt)that;
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
