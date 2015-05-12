/* Copyright 2009-2015 EPFL, Lausanne */

package leon.codegen.runtime;

import java.math.BigInteger;

public final class Rational {

	private final BigInteger _num;
	private final BigInteger _denom;

	/**
	 * class invariant: the fractions are always normalized
	 *
	 * @param num
	 *            numerator
	 * @param denom
	 *            denominator
	 */
	public Rational(BigInteger num, BigInteger denom) {
		BigInteger modNum = num.abs();
		BigInteger modDenom = denom.abs();
		BigInteger divisor = modNum.gcd(modDenom);
		BigInteger simpNum = num.divide(divisor);
		BigInteger simpDenom = denom.divide(divisor);
		if (isLTZ(simpDenom)) {
			_num = simpNum.negate();
			_denom = simpDenom.negate();
		} else {
			_num = simpNum;
			_denom = simpDenom;
		}
	}

	public Rational(String num, String denom) {
		this(new BigInteger(num), new BigInteger(denom));
	}

	public BigInteger numerator() {
		return _num;
	}

	public BigInteger denominator() {
		return _denom;
	}

	public boolean isZero(BigInteger bi) {
		return bi.signum() == 0;
	}

	public boolean isLEZ(BigInteger bi) {
		return bi.signum() != 1;
	}

	public boolean isLTZ(BigInteger bi) {
		return (bi.signum() == -1);
	}

	public boolean isGEZ(BigInteger bi) {
		return (bi.signum() != -1);
	}

	public boolean isGTZ(BigInteger bi) {
		return (bi.signum() == 1);
	}

	public Rational add(Rational that) {
		return new Rational(_num.multiply(that._denom).add(
				that._num.multiply(_denom)), _denom.multiply(that._denom));
	}

	public Rational sub(Rational that) {
		return new Rational(_num.multiply(that._denom).subtract(
				that._num.multiply(_denom)), _denom.multiply(that._denom));
	}

	public Rational mult(Rational that) {
		return new Rational(_num.multiply(that._num),
				_denom.multiply(that._denom));
	}

	public Rational div(Rational that) {
		return new Rational(_num.multiply(that._denom),
				_denom.multiply(that._num));
	}

	public Rational neg() {
		return new Rational(_num.negate(), _denom);
	}

	public boolean lessThan(Rational that) {
		return isLTZ(this.sub(that)._num);
	}

	public boolean lessEquals(Rational that) {
		return isLEZ(this.sub(that)._num);
	}

	public boolean greaterThan(Rational that) {
		return isGTZ(this.sub(that)._num);
	}

	public boolean greaterEquals(Rational that) {
		return isGEZ(this.sub(that)._num);
	}

	@Override
	public boolean equals(Object that) {
		if (that == this)
			return true;
		if (!(that instanceof Rational))
			return false;

		Rational other = (Rational) that;
		return isZero(this.sub(other)._num);
	}

	@Override
	public String toString() {
		return _num.toString() + "/" + _denom.toString();
	}

	@Override
	public int hashCode() {
		return _num.hashCode() ^ _denom.hashCode();
	}
}
