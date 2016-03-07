/* Copyright 2009-2016 EPFL, Lausanne */

package leon.codegen.runtime;

/** Such exceptions are thrown when the evaluator encounters a runtime error,
 *  for instance `.get` with an undefined key on a map. */
public class LeonCodeGenRuntimeMonitor {
    private int invocationsLeft;

    public LeonCodeGenRuntimeMonitor(int maxInvocations) {
        this.invocationsLeft = maxInvocations;
    }

    public void onInvoke() throws LeonCodeGenEvaluationException {
        if(invocationsLeft > 0) {
            invocationsLeft--;
        } else if(invocationsLeft == 0) {
            throw new LeonCodeGenEvaluationException("Maximum number of invocations reached.");
        }
    }
}
