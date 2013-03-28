package z3.java;

import z3.Z3Wrapper;
import z3.Pointer;

public class Z3Model extends Pointer {
    private final Z3Context context;

    protected Z3Model(Z3Context context) {
        super(0L);
        this.context = context;
    }

    protected long contextPtr() {
        return context.ptr;
    }

    public void delete() {
        Z3Wrapper.delModel(context.ptr, this.ptr);
        this.ptr = 0L;
    }

    public Z3AST eval(Z3AST ast) {
        if(this.ptr == 0L) {
            throw new IllegalStateException("The model is not initialized.");
        }
        Z3AST out = new Z3AST(0L);
        boolean result = Z3Wrapper.eval(context.ptr, this.ptr, ast.ptr, out);
        if (result) {
            return out;
        } else {
            return null;
        }
    }

    public Integer evalAsInt(Z3AST ast) {
        Z3AST res = this.eval(ast);
        if(res == null) return null;
        return context.getNumeralInt(res);
    }

    public Boolean evalAsBool(Z3AST ast) {
        Z3AST res = this.eval(ast);
        if(res == null) return null;
        return context.getBoolValue(res);
    }
}
