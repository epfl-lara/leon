package z3.java;

import z3.Z3Wrapper;
import z3.Pointer;

public class Z3Context extends Pointer {
    public static Boolean lbool2Boolean(int v) {
        if(v == -1)
            return false;
        else if (v == 0)
            return null;
        else
            return true;
    }

    public Z3Context(Z3Config config) {
        super(Z3Wrapper.mkContext(config.ptr));
    }

    public void delete() {
        Z3Wrapper.delContext(this.ptr);
        this.ptr = 0;
    }

    public void updateParamValue(String paramID, String paramValue) {
        Z3Wrapper.updateParamValue(this.ptr, paramID, paramValue);
    }

    public Z3Symbol mkIntSymbol(int i) {
        return new Z3Symbol(Z3Wrapper.mkIntSymbol(this.ptr, i));
    }

    public Z3Symbol mkStringSymbol(String s) {
        return new Z3Symbol(Z3Wrapper.mkStringSymbol(this.ptr, s));
    }

    public boolean isEqSort(Z3Sort s1, Z3Sort s2) {
        return Z3Wrapper.isEqSort(this.ptr, s1.ptr, s2.ptr);
    }

    public Z3Sort mkUninterpretedSort(Z3Symbol s) {
        return new Z3Sort(Z3Wrapper.mkUninterpretedSort(this.ptr, s.ptr));
    }

    public Z3Sort mkBoolSort() {
        return new Z3Sort(Z3Wrapper.mkBoolSort(this.ptr));
    }

    public Z3Sort mkIntSort() {
        return new Z3Sort(Z3Wrapper.mkIntSort(this.ptr));
    }

    public Z3Sort mkRealSort() {
        return new Z3Sort(Z3Wrapper.mkRealSort(this.ptr));
    }

    public boolean isEqAST(Z3AST t1, Z3AST t2) {
        return Z3Wrapper.isEqAST(this.ptr, t1.ptr, t2.ptr);
    }

    public Z3AST mkConst(Z3Symbol symbol, Z3Sort sort) {
        return new Z3AST(Z3Wrapper.mkConst(this.ptr, symbol.ptr, sort.ptr));
    }

    public Z3AST mkTrue() {
        return new Z3AST(Z3Wrapper.mkTrue(this.ptr));
    }

    public Z3AST mkFalse() {
        return new Z3AST(Z3Wrapper.mkFalse(this.ptr));
    }

    public Z3AST mkEq(Z3AST ast1, Z3AST ast2) {
        return new Z3AST(Z3Wrapper.mkEq(this.ptr, ast1.ptr, ast2.ptr));
    }

    public Z3AST mkDistinct(Z3AST ... args) {
        if(args.length == 0)
            throw new IllegalArgumentException("mkDistinct needs at least one argument");
        return new Z3AST(Z3Wrapper.mkDistinct(this.ptr, args.length, Z3Wrapper.toPtrArray(args)));
    }

    public Z3AST mkNot(Z3AST ast) {
        return new Z3AST(Z3Wrapper.mkNot(this.ptr, ast.ptr));
    }

    public Z3AST mkITE(Z3AST t1, Z3AST t2, Z3AST t3) {
        return new Z3AST(Z3Wrapper.mkITE(this.ptr, t1.ptr, t2.ptr, t3.ptr));
    }

    public Z3AST mkIff(Z3AST t1, Z3AST t2) {
        return new Z3AST(Z3Wrapper.mkIff(this.ptr, t1.ptr, t2.ptr));
    }

    public Z3AST mkImplies(Z3AST t1, Z3AST t2) {
        return new Z3AST(Z3Wrapper.mkImplies(this.ptr, t1.ptr, t2.ptr));
    }

    public Z3AST mkXor(Z3AST t1, Z3AST t2) {
        return new Z3AST(Z3Wrapper.mkXor(this.ptr, t1.ptr, t2.ptr));
    }

    public Z3AST mkAnd(Z3AST ... args) {
        if(args.length == 0)
            throw new IllegalArgumentException("mkAnd needs at least one argument");
        return new Z3AST(Z3Wrapper.mkAnd(this.ptr, args.length, Z3Wrapper.toPtrArray(args)));
    }

    public Z3AST mkOr(Z3AST ... args) {
        if(args.length == 0)
            throw new IllegalArgumentException("mkOr needs at least one argument");
        return new Z3AST(Z3Wrapper.mkOr(this.ptr, args.length, Z3Wrapper.toPtrArray(args)));
    }

    public Z3AST mkAdd(Z3AST ... args) {
        if(args.length == 0)
            throw new IllegalArgumentException("mkAdd needs at least one argument");
        return new Z3AST(Z3Wrapper.mkAdd(this.ptr, args.length, Z3Wrapper.toPtrArray(args)));
    }

    public Z3AST mkMul(Z3AST ... args) {
        if(args.length == 0)
            throw new IllegalArgumentException("mkMul needs at least one argument");
        return new Z3AST(Z3Wrapper.mkMul(this.ptr, args.length, Z3Wrapper.toPtrArray(args)));
    }

    public Z3AST mkSub(Z3AST ... args) {
        if(args.length == 0)
            throw new IllegalArgumentException("mkSub needs at least one argument");
        return new Z3AST(Z3Wrapper.mkSub(this.ptr, args.length, Z3Wrapper.toPtrArray(args)));
    }

    public Z3AST mkUnaryMinus(Z3AST ast) {
        return new Z3AST(Z3Wrapper.mkUnaryMinus(this.ptr, ast.ptr));
    }

    public Z3AST mkDiv(Z3AST ast1, Z3AST ast2) {
        return new Z3AST(Z3Wrapper.mkDiv(this.ptr, ast1.ptr, ast2.ptr));
    }

    public Z3AST mkMod(Z3AST ast1, Z3AST ast2) {
        return new Z3AST(Z3Wrapper.mkMod(this.ptr, ast1.ptr, ast2.ptr));
    }

    public Z3AST mkRem(Z3AST ast1, Z3AST ast2) {
        return new Z3AST(Z3Wrapper.mkRem(this.ptr, ast1.ptr, ast2.ptr));
    }

    public Z3AST mkLT(Z3AST ast1, Z3AST ast2) {
        return new Z3AST(Z3Wrapper.mkLT(this.ptr, ast1.ptr, ast2.ptr));
    }

    public Z3AST mkLE(Z3AST ast1, Z3AST ast2) {
        return new Z3AST(Z3Wrapper.mkLE(this.ptr, ast1.ptr, ast2.ptr));
    }

    public Z3AST mkGT(Z3AST ast1, Z3AST ast2) {
        return new Z3AST(Z3Wrapper.mkGT(this.ptr, ast1.ptr, ast2.ptr));
    }

    public Z3AST mkGE(Z3AST ast1, Z3AST ast2) {
        return new Z3AST(Z3Wrapper.mkGE(this.ptr, ast1.ptr, ast2.ptr));
    }

    public Z3AST mkInt2Real(Z3AST ast) {
        return new Z3AST(Z3Wrapper.mkInt2Real(this.ptr, ast.ptr));
    }

    public Z3AST mkReal2Int(Z3AST ast) {
        return new Z3AST(Z3Wrapper.mkReal2Int(this.ptr, ast.ptr));
    }

    public Z3AST mkIsInt(Z3AST ast) {
        return new Z3AST(Z3Wrapper.mkIsInt(this.ptr, ast.ptr));
    }

    public Z3AST mkInt(int value, Z3Sort sort) {
        return new Z3AST(Z3Wrapper.mkInt(this.ptr, value, sort.ptr));
    }
    
    public Z3AST mkReal(double value, int numerator, int denominator) {
        return new Z3AST(Z3Wrapper.mkReal(this.ptr, numerator, denominator));
    }

    public Integer getNumeralInt(Z3AST ast) {
        Z3Wrapper.IntPtr ip = new Z3Wrapper.IntPtr();
        boolean res = Z3Wrapper.getNumeralInt(this.ptr, ast.ptr, ip);
        if(res)
            return ip.value;
        else
            return null;
    }

    public Boolean getBoolValue(Z3AST ast) {
        return lbool2Boolean(Z3Wrapper.getBoolValue(this.ptr, ast.ptr));
    }

    public void push() {
        Z3Wrapper.push(this.ptr);
    }

    public void pop(int numScopes) {
        Z3Wrapper.pop(this.ptr, numScopes);
    }

    public void assertCnstr(Z3AST ast) {
        Z3Wrapper.assertCnstr(this.ptr, ast.ptr);
    }

    public Boolean check() {
        return lbool2Boolean(Z3Wrapper.check(this.ptr));
    }

    public Z3Model mkModel() {
        return new Z3Model(this);
    }

    public Boolean checkAndGetModel(Z3Model model) {
        return lbool2Boolean(Z3Wrapper.checkAndGetModel(this.ptr, model));
    }

    public Boolean checkAssumptions(Z3AST assumptions[], Z3Model model, Z3AST core[]) {
	return checkAssumptionsImpl(assumptions, model, core);
    }
    
    public Boolean checkAssumptionsNoModel(Z3AST ... assumptions) {
	Pointer[] core = new Pointer[assumptions.length];
	// create C null pointer array
	for (int i = 0; i < assumptions.length; i++) {
	    core[i] = new Pointer(0L);
	}
	return checkAssumptionsImpl(assumptions, new Z3Model(this), core);
    }
    
    private Boolean checkAssumptionsImpl(Z3AST assumptions[], Z3Model model, Pointer core[]) {
	Z3Wrapper.IntPtr ip = new Z3Wrapper.IntPtr();
	return lbool2Boolean(Z3Wrapper.checkAssumptions(this.ptr, assumptions.length, Z3Wrapper.toPtrArray(assumptions), model, core.length, ip, Z3Wrapper.toPtrArray(core)));
    }

}
