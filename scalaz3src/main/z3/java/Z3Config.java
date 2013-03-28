package z3.java;

import z3.Z3Wrapper;
import z3.Pointer;

public class Z3Config extends Pointer {
    public Z3Config() {
        super(Z3Wrapper.mkConfig());
    }

    public void delete() {
        Z3Wrapper.delConfig(this.ptr);
        this.ptr = 0;
    }

    public Z3Config setParamValue(String paramID, String paramValue) {
        Z3Wrapper.setParamValue(this.ptr, paramID, paramValue);
        return this;
    }
}
