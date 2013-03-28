package z3;

public final class Z3ErrorException extends RuntimeException {

	private static final long serialVersionUID = 3382203884603330972L;

	private final int errCode;

    public Z3ErrorException(int errorCode, String message) {
        super(message);
        errCode = errorCode;
    }

    public int getErrorCode() {
        return errCode;
    }
}
