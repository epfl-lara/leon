package z3.java;

import z3.Z3Wrapper;

/** Contains all functionalities that do not refer to a context or other
 * pointer. */
public class Z3Global {
    public static void toggleWarningMessages(boolean enabled) {
        Z3Wrapper.toggleWarningMessages(enabled);
    }
}
