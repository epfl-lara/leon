package leon.codegen.runtime;

public class LeonCodeGenRuntimeException extends Exception {
    private final String msg;

    public LeonCodeGenRuntimeException(String msg) {
        this.msg = msg;
    }

    public String getMessage() {
        return this.msg;
    }
}
