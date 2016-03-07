/* Copyright 2009-2016 EPFL, Lausanne */

package leon.codegen.runtime;

/** Such exceptions are thrown when the evaluator is asked to do something it
 *  cannot do, for instance evaluating a `choose` expression. It should be
 *  distinguished from `LeonCodeGenRuntimeException`s, which are thrown when
 *  the evaluator runs into a runtime error (.get on an undefined map, etc.). */
public class LeonCodeGenEvaluationException extends Exception {
  
    private static final long serialVersionUID = -1824885944356173916L;

    public LeonCodeGenEvaluationException(String msg) {
        super(msg);
    }
}
