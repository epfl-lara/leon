/* Copyright 2009-2014 EPFL, Lausanne */

package leon.codegen.runtime;

/** Such exceptions are thrown when the evaluator encounters a runtime error,
 *  for instance `.get` with an undefined key on a map. */
public class LeonCodeGenRuntimeException extends Exception {
    public LeonCodeGenRuntimeException(String msg) {
        super(msg);
    }
}
