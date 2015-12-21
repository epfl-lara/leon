/* Copyright 2009-2015 EPFL, Lausanne */

package leon.codegen.runtime;

/** Such exceptions are thrown when the evaluator encounters a forall
 *  expression whose shape is not supported in Leon. */
public class LeonCodeGenQuantificationException extends Exception {
  
    private static final long serialVersionUID = -1824885321497473916L;

    public LeonCodeGenQuantificationException(String msg) {
        super(msg);
    }
}
