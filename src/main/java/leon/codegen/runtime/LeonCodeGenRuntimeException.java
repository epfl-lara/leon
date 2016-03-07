/* Copyright 2009-2016 EPFL, Lausanne */

package leon.codegen.runtime;

/** Such exceptions are thrown when the evaluator encounters a runtime error,
 *  for instance `.get` with an undefined key on a map. */
public class LeonCodeGenRuntimeException extends Exception {

    private static final long serialVersionUID = -8033159036464950965L;

    public LeonCodeGenRuntimeException(String msg) {
        super(msg);
    }
}
