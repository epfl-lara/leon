/* Copyright 2009-2016 EPFL, Lausanne */

package leon.codegen.runtime;

import org.apache.commons.lang3.StringEscapeUtils;

public class StrOps {
	public static String concat(String a, String b) {
		return a + b;
	}
	
	public static BigInt bigLength(String a) {
		return new BigInt(a.length() + "");
	}
	
	public static String bigSubstring(String s, BigInt start, BigInt end) {
		return s.substring(Integer.parseInt(start.toString()), Integer.parseInt(end.toString()));
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
