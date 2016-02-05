package leon.codegen.runtime;

import org.apache.commons.lang3.StringEscapeUtils;

public class StrOps {
	public static String concat(String a, String b) {
		return a + b;
	}

	public static BigInt length(String a) {
		return new BigInt(String.valueOf(a.length()));
	}

	public static String substring(String a, BigInt start, BigInt end) {
		if (start.greaterEquals(end) || start.greaterEquals(length(a))
				|| end.lessEquals(new BigInt("0")))
			throw new RuntimeException("Invalid substring indices : " + start + ", " + end + " for string \""+a+"\"");
		else
			return a.substring(start.underlying().intValue(), end.underlying()
					.intValue());
	}

	public static String bigIntToString(BigInt a) {
		return a.toString();
	}

	public static String intToString(int a) {
		return String.valueOf(a);
	}

	public static String doubleToString(double a) {
		return String.valueOf(a);
	}

	public static String booleanToString(boolean a) {
		if (a)
			return "true";
		else
			return "false";
	}

	public static String charToString(char a) {
		return String.valueOf(a);
	}

	public static String realToString(Real a) {
		return ""; // TODO: Not supported at this moment.
	}

	public static String escape(String s) {
		return StringEscapeUtils.escapeJava(s);
	}
}
