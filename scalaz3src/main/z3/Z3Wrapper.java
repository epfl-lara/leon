package z3;

import z3.Pointer;
import z3.scala.Z3Context;

import java.io.File;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.FileOutputStream;
import java.util.Calendar;
import java.text.SimpleDateFormat;
import java.util.HashMap;
import java.lang.ref.WeakReference;

/** This class contains all the native functions. It should be accessed
 * mostly through the other classes, though. */
public final class Z3Wrapper {
    // related to the path in the jar file
	private static final String LIB_SEPARATOR = "/";
    private static final String LIB_BIN = LIB_SEPARATOR + "lib-bin" + LIB_SEPARATOR;
    // the root name of the library file. lib....so in Linux, lib....jnilib in MacOS, ....dll in Windows, etc.
    private static final String LIB_NAME = "scalaz3";
    private static final String Z3_LIB_NAME = "z3";

    public static Object gc_lock = new Object();

    private static final String versionString = LibraryChecksum.value;

    // this is just to force class loading, and therefore library loading.
    public static void init() { }

    static {
        try {
            // System.out.println("Looking for Library " + LIB_NAME + " in System path" );
            System.loadLibrary(LIB_NAME);
        } catch (UnsatisfiedLinkError e) {
            // Convert root to: lib....so in Linux, lib....jnilib in MacOS, ....dll in Windows, etc.
            String name = System.mapLibraryName(LIB_NAME);

            try {
                String curDir = System.getProperty("user.dir");
                //System.out.println("Looking for Library " + name + " in directory:" + curDir );
                System.load(curDir + LIB_SEPARATOR + name );
            } catch (UnsatisfiedLinkError e2) {
                //System.out.println("Looking for Library " + name + " in jarFile" );
                loadFromJar();
            }
        }
    }

    public static String wrapperVersionString() {
        // Version number should match smallest Z3 with which we know it to work, plus a letter for "internal" versions.
        return "ScalaZ3 4.0.a (in dev.)";
    }

    public static String z3VersionString() {
        IntPtr major = new IntPtr();
        IntPtr minor = new IntPtr();
        IntPtr buildNumber = new IntPtr();
        IntPtr revisionNumber = new IntPtr();
        getVersion(major, minor, buildNumber, revisionNumber);
        return "Z3 " + major.value + "." + minor.value + " (build " + buildNumber.value + ", rev. " + revisionNumber.value + ")";
    }

    private static void loadFromJar() {
        String path = "SCALAZ3_" + versionString;
        loadLib(path, Z3_LIB_NAME, true);
        loadLib(path, LIB_NAME, false);
    }

    private static void loadLib(String path, String name, boolean optional) {
        name = System.mapLibraryName(name);
        String completeFileName = LIB_BIN + name;
        File fileOut = new File(System.getProperty("java.io.tmpdir") + "/" + path + completeFileName);
        //System.out.println("I'll be looking for the library as: " + fileOut);

        if(fileOut.isFile() && fileOut.canRead()) {
            // Library has been copied in the past, we can just load it from there.
            //System.out.println("Looks like I found it !");
            System.load(fileOut.toString());
        } else {
            // Couldn't find the library, so we can copy before we can load it.
            try {
                //System.out.println("Oh no, I have to extract it from the jar file !");
                //System.out.println("Looking for " + completeFileName + " in the jar file...");
                InputStream in = Z3Wrapper.class.getResourceAsStream(completeFileName);
                if (in==null && optional)
                    return; // we ignore this
                if (in==null)
                    throw new java.io.FileNotFoundException("Could not find " + completeFileName);

                fileOut.getParentFile().mkdirs();
                fileOut.createNewFile();
                OutputStream out = new FileOutputStream(fileOut);
                byte buf[] = new byte[4096];
                int len;
                while((len = in.read(buf)) > 0) {
                    out.write(buf, 0, len);
                }
                out.close();
                in.close();
                System.load(fileOut.toString());
            } catch (Exception e) {
                System.err.println(e.getMessage());
                e.printStackTrace();
            }
        }
    }

    /** Placeholder class to ease JNI interaction. */
    public static class IntPtr {
        public int value;
    }

    public static long[] toPtrArray(Pointer[] ptrs) {
        long[] result = new long[ptrs.length];
        for(int i = 0; i < ptrs.length; i++) {
            result[i] = ptrs[i].ptr;
        }
        return result;
    }

    private static HashMap<Long, WeakReference<Z3Context>> ptrToCtx = new HashMap<Long, WeakReference<Z3Context>>();

    public static void onZ3Error(long contextPtr, long code) {
        Z3Context ctx = ptrToCtx.get(Long.valueOf(contextPtr)).get();
        ctx.onError(code);
    }

    public static void registerContext(long contextPtr, Z3Context ctx) {
        ptrToCtx.put(Long.valueOf(contextPtr), new WeakReference<Z3Context>(ctx));
    }

    public static void unregisterContext(long contextPtr) {
        ptrToCtx.remove(Long.valueOf(contextPtr));
    }

    public static native long mkConfig();
    public static native void delConfig(long configPtr);
    public static native void setParamValue(long configPtr, String paramID, String paramValue);
    public static native long mkContext(long configPtr);
    public static native long mkContextRC(long configPtr);
    public static native void incRef(long contextPtr, long ptr);
    public static native void decRef(long contextPtr, long ptr);
    public static native void interrupt(long contextPtr);
    public static native void delContext(long contextPtr);
    public static native void toggleWarningMessages(boolean enabled);
    public static native void updateParamValue(long contextPtr, String paramID, String paramValue);
    public static native long mkIntSymbol(long contextPtr, int i);
    public static native long mkStringSymbol(long contextPtr, String s);
    public static native boolean isEqSort(long contextPtr, long sortPtr1, long sortPtr2);
    public static native long mkUninterpretedSort(long contextPtr, long symbolPtr);
    public static native long mkBoolSort(long contextPtr);
    public static native long mkIntSort(long contextPtr);
    public static native long mkRealSort(long contextPtr);
    // ...
    
    public static native long mkConstructor(long contextPtr, long symbolPtr1, long symbolPtr2, int numFields, long[] fieldNames, long[] sorts, int[] sortRefs);
    public static native void queryConstructor(long contextPtr, long constructorPtr, int numFields, Pointer constructor, Pointer tester, long[] selectors);
    // public static native void delConstructor(long contextPtr, long constructorPtr);
    // public static native long mkDatatype(long contextPtr, long symbolPtr, int numConstructors, Pointer[] constructors);
    public static native long mkConstructorList(long contextPtr, int numConstructors, long[] constructors);
    public static native void delConstructorList(long contextPtr, long constructorListPtr);
    // returns an array containing the new sorts.
    public static native long[] mkDatatypes(long contextPtr, int numSorts, long[] sortNames, long[] constructorLists);

    // ...
    public static native boolean isEqAST(long contextPtr, long astPtr1, long astPtr2);
    // ...
    public static native long mkApp(long contextPtr, long funcDeclPtr, int numArgs, long[] args);
    public static native boolean isEqFuncDecl(long contextPtr, long fdPtr1, long fdPtr2);
    public static native long mkConst(long contextPtr, long symbolPtr, long sortPtr);
    public static native long mkFuncDecl(long contextPtr, long symbolPtr, int domainSize, long[] domainSortPtrs, long rangeSortPtr);
    public static native long mkFreshConst(long contextPtr, String prefix, long sortPtr);
    public static native long mkFreshFuncDecl(long contextPtr, String prefix, int domainSize, long[] domainSortPtrs, long rangeSortPtr);

    // ...
    public static native long mkTrue(long contextPtr);
    public static native long mkFalse(long contextPtr);
    public static native long mkEq(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkDistinct(long contextPtr, int numArgs, long[] args);
    public static native long mkNot(long contextPtr, long astPtr);
    public static native long mkITE(long contextPtr, long astPtr1, long astPtr2, long astPtr3);
    public static native long mkIff(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkImplies(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkXor(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkAnd(long contextPtr, int numArgs, long[] args);
    public static native long mkOr(long contextPtr, int numArgs, long[] args);
    public static native long mkAdd(long contextPtr, int numArgs, long[] args);
    public static native long mkMul(long contextPtr, int numArgs, long[] args);
    public static native long mkSub(long contextPtr, int numArgs, long[] args);
    public static native long mkUnaryMinus(long contextPtr, long astPtr);
    public static native long mkDiv(long contextPtr, long astPtr1, long astPtr2); 
    public static native long mkDiv2(long contextPtr, long astPtr1, long astPtr2); 
    public static native long mkMod(long contextPtr, long astPtr1, long astPtr2); 
    public static native long mkRem(long contextPtr, long astPtr1, long astPtr2); 
    public static native long mkLT(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkLE(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkGT(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkGE(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkInt2Real(long contextPtr, long astPtr);
    public static native long mkReal2Int(long contextPtr, long astPtr);
    public static native long mkIsInt(long contextPtr, long astPtr);
    // ...
    
    public static native long mkArraySort(long contextPtr, long domainSortPtr, long rangeSortPtr);
    public static native long mkSelect(long contextPtr, long astPtrArr, long astPtrInd);
    public static native long mkStore(long contextPtr, long astPtrArr, long astPtrInd, long astPtrVal);
    public static native long mkConstArray(long contextPtr, long sortPtr, long astPtrVal);
    public static native long mkArrayDefault(long contextPtr, long astPtrArr);

    public static native long mkTupleSort(long contextPtr, long symPtr, int numFields, long[] fieldNames, long[] fieldSorts, Pointer constructor, long[] projFuns);

    public static native long mkSetSort(long contextPtr, long sortPtr);
    public static native long mkEmptySet(long contextPtr, long sortPtr);
    public static native long mkFullSet(long contextPtr, long sortPtr);
    public static native long mkSetAdd(long contextPtr, long setPtr, long elemPtr);
    public static native long mkSetDel(long contextPtr, long setPtr, long elemPtr);
    public static native long mkSetUnion(long contextPtr, int argCount, long[] args);
    public static native long mkSetIntersect(long contextPtr, int argCount, long[] args);
    public static native long mkSetDifference(long contextPtr, long setPtr1, long setPtr2);
    public static native long mkSetComplement(long contextPtr, long setPtr);
    public static native long mkSetMember(long contextPtr, long elemPtr, long setPtr);
    public static native long mkSetSubset(long contextPtr, long setPtr1, long setPtr2);
    // ...
    public static native long mkInt(long contextPtr, int v, long sortPtr);
    public static native long mkReal(long contextPtr, int num, int den);
    public static native long mkNumeral(long contextPtr, String numeral, long sortPtr);
    // ...
    public static native long mkPattern(long contextPtr, int numPatterns, long[] terms);
    public static native long mkBound(long contextPtr, int index, long sortPtr);
    public static native long mkQuantifier(long contextPtr, boolean isForAll, int weight, int numPatterns, long[] patterns, int numDecls, long[] declSorts, long[] declNames, long body);
    public static native long mkQuantifierConst(long contextPtr, boolean isForAll, int weight, int numBounds, long[] bounds, int numPatterns, long[] patterns, long body);
    // ...

    // Bit vector fun
    public static native long mkBVSort(long contextPtr, int size);
    public static native long mkBVNot(long contextPtr, long astPtr);
    public static native long mkBVRedAnd(long contextPtr, long astPtr);
    public static native long mkBVRedOr(long contextPtr, long astPtr);
    public static native long mkBVAnd(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVOr(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVXor(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVNand(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVNor(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVXnor(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVNeg(long contextPtr, long astPtr);
    public static native long mkBVAdd(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVSub(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVMul(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVUdiv(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVSdiv(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVUrem(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVSrem(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVSmod(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVUlt(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVSlt(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVUle(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVSle(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVUgt(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVSgt(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVUge(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVSge(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkConcat(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkExtract(long contextPtr, int high, int low, long astPtr);
    public static native long mkSignExt(long contextPtr, int i, long astPtr);
    public static native long mkZeroExt(long contextPtr, int i, long astPtr);
    public static native long mkRepeat(long contextPtr, int i, long astPtr);
    public static native long mkBVShl(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVLshr(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVAshr(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkRotateLeft(long contextPtr, int i, long astPtr);
    public static native long mkRotateRight(long contextPtr, int i, long astPtr);
    public static native long mkExtRotateLeft(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkExtRotateRight(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkInt2BV(long contextPtr, int size, long astPtr);
    public static native long mkBV2Int(long contextPtr, long astPtr, boolean isSigned);
    public static native long mkBVAddNoOverflow(long contextPtr, long astPtr1, long astPtr2, boolean isSigned);
    public static native long mkBVAddNoUnderflow(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVSubNoUnderflow(long contextPtr, long astPtr1, long astPtr2, boolean isSigned);
    public static native long mkBVSubNoOverflow(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVSdivNoOverflow(long contextPtr, long astPtr1, long astPtr2);
    public static native long mkBVNegNoOverflow(long contextPtr, long astPtr);
    public static native long mkBVMulNoOverflow(long contextPtr, long astPtr1, long astPtr2, boolean isSigned);
    public static native long mkBVMulNoUnderflow(long contextPtr, long astPtr1, long astPtr2);

    public static native int getBVSortSize(long contextPtr, long sortPtr);

    // Returns one of the following values:
    // 0 - Z3_INT_SYMBOL
    // 1 - Z3_STRING_SYMBOL
    // ? - ???
    public static native int getSymbolKind(long contextPtr, long symbolPtr);
    public static native int getSymbolInt(long contextPtr, long symbolPtr);
    public static native String getSymbolString(long contextPtr, long symbolPtr);
    // Returns one of the following values:
    //  0 - Z3_NUMERAL_AST
    //  1 - Z3_APP_AST
    //  2 - Z3_VAR_AST
    //  3 - Z3_QUANTIFIER_AST
    //  4 - Z3_UNKNOWN_AST
    // -1 - otherwise (should not happen)
    public static native int getASTKind(long contextPtr, long astPtr);

    //  0 - OpTrue 
    //  1 - OpFalse 
    //  2 - OpEq 
    //  3 - OpDistinct 
    //  4 - OpITE 
    //  5 - OpAnd 
    //  6 - OpOr 
    //  7 - OpIff 
    //  8 - OpXor 
    //  9 - OpNot 
    // 10 - OpImplies 
    // 11 - OpANum 
    // 12 - OpLE 
    // 13 - OpGE 
    // 14 - OpLT 
    // 15 - OpGT 
    // 16 - OpAdd 
    // 17 - OpSub 
    // 18 - OpUMinus 
    // 19 - OpMul 
    // 20 - OpDiv 
    // 21 - OpIDiv 
    // 22 - OpRem 
    // 23 - OpMod 
    // 24 - OpToReal 
    // 25 - OpToInt 
    // 26 - OpIsInt 
    // 27 - OpStore 
    // 28 - OpSelect 
    // 29 - OpConstArray 
    // 30 - OpArrayDefault 
    // 31 - OpArrayMap 
    // 32 - OpSetUnion 
    // 33 - OpSetIntersect 
    // 34 - OpSetDifference 
    // 35 - OpSetComplement 
    // 36 - OpSetSubset 
    // 37 - OpAsArray 
    
    // 1000 - OpUninterpreted

    // 9999 - Other 
    public static native int getDeclKind(long contextPtr, long funcDeclPtr);
    // ...
    public static native long getAppDecl(long contextPtr, long astPtr);
    public static native int getAppNumArgs(long contextPtr, long astPtr);
    public static native long getAppArg(long contextPtr, long astPtr, int i);
    // ...
    public static native long getDeclName(long contextPtr, long funcDeclPtr);
    // ...
    public static native long getDeclFuncDeclParameter(long contextPtr, long funcDeclPtr, int idx);
    // ...
    public static native long getSort(long contextPtr, long astPtr);
    public static native int  getDomainSize(long contextPtr, long funcDeclPtr);
    public static native long getDomain(long contextPtr, long funcDeclPtr, int i);
    public static native long getRange(long contextPtr, long funcDeclPtr);
    // ...
    public static native boolean getNumeralInt(long contextPtr, long astPtr, IntPtr i);
    public static native String getNumeralString(long contextPtr, long astPtr);
    public static native long getNumerator(long contextPtr, long astPtr);
    public static native long getDenominator(long contextPtr, long astPtr);
    public static native boolean isAlgebraicNumber(long contextPtr, long astPtr);

    // ...
    public static native int getBoolValue(long contextPtr, long astPtr);


    // Returns one of the following values:
    // 0 - Z3_NO_FAILURE       The last search was successful
    // 1 - Z3_UNKNOWN          Undocumented failure reason
    // 2 - Z3_TIMEOUT          Timeout
    // 3 - Z3_MEMOUT_WATERMARK Search hit a memory high-watermak limit
    // 4 - Z3_CANCELED         External cancel flag was set
    // 5 - Z3_NUM_CONFLICTS    Maximum number of conflicts was reached
    // 6 - Z3_THEORY           Theory is incomplete
    // 7 - Z3_QUANTIFIERS      Logical context contains universal quantifiers
    // ? - ????
    public static native int getSearchFailure(long contextPtr);

    public static native void delModel(long contextPtr, long modelPtr);
    public static native void modelIncRef(long contextPtr, long modelPtr);
    public static native void modelDecRef(long contextPtr, long modelPtr);
    // decprecated
    public static native boolean eval(long contextPtr, long modelPtr, long astPtr, Pointer ast);
    public static native boolean modelEval(long contextPtr, long modelPtr, long astPtr, Pointer ast, boolean completion);
    public static native int getModelNumConstants(long contextPtr, long modelPtr);
    public static native long getModelConstant(long contextPtr, long modelPtr, int i);
    public static native boolean isArrayValue(long contextPtr, long modelPtr, long astPtr, IntPtr numEntries);
    public static native void getArrayValue(long contextPtr, long modelPtr, long astPtr, int numEntries, long[] indices, long[] values, Pointer elseValue);
    public static native int getModelNumFuncs(long contextPtr, long modelPtr);
    public static native long getModelFuncDecl(long contextPtr, long modelPtr, int i);
    public static native int getModelFuncNumEntries(long contextPtr, long modelPtr, int i);
    public static native int getModelFuncEntryNumArgs(long contextPtr, long modelPtr, int i, int j);
    public static native long getModelFuncEntryArg(long contextPtr, long modelPtr, int i, int j, int k);
    public static native long getModelFuncEntryValue(long contextPtr, long modelPtr, int i, int j);
    public static native long getModelFuncElse(long contextPtr, long modelPtr, int i);

    public static native long mkLabel(long contextPtr, long symbolPtr, boolean polarity, long astPtr);
    public static native long getRelevantLabels(long contextPtr);
    public static native long getRelevantLiterals(long contextPtr);
    public static native long getGuessedLiterals(long contextPtr);
    public static native void delLiterals(long contextPtr, long lbls);
    public static native int  getNumLiterals(long contextPtr, long lbls);
    public static native long getLabelSymbol(long contextPtr, long lbls, int idx);
    public static native long getLiteral(long contextPtr, long lbls, int idx);

    public static native boolean isQuantifierForall(long contextPtr, long astPtr);
    public static native long getQuantifierBody(long contextPtr, long astPtr);
    public static native long getQuantifierBoundName(long contextPtr, long astPtr, int i);
    public static native int getQuantifierNumBound(long contextPtr, long astPtr);
    public static native int getIndexValue(long contextPtr, long astPtr);

    public static native void disableLiteral(long contextPtr, long lbls, int idx);
    public static native void blockLiterals(long contextPtr, long lbls);

    // These are the side-effect versions...
    public static native void printAST(long contextPtr, long astPtr);
    public static native void printModel(long contextPtr, long modelPtr);
    public static native void printContext(long contextPtr);
    // ...and these return strings.
    public static native String astToString(long contextPtr, long astPtr);
    public static native String funcDeclToString(long contextPtr, long funcDeclPtr);
    public static native String sortToString(long contextPtr, long sortPtr);
    public static native String patternToString(long contextPtr, long patternPtr);
    public static native String modelToString(long contextPtr, long modelPtr);
    public static native String contextToString(long contextPtr);
    public static native String benchmarkToSMTLIBString(long contextPtr, String name, String logic, String status, String attributes, int numAssumptions, long[] assumptions, long formulaPtr);

    // The following is related to the theory plugins.
    private static HashMap<Long,AbstractTheoryProxy> tpmap = new HashMap<Long,AbstractTheoryProxy>();

    public static native long mkTheory(long ctxPtr, String name);
    // This is not a call to a Z3 function...
    public static native void setTheoryCallbacks(long thyPtr, AbstractTheoryProxy atp, boolean setDelete, boolean setReduceEq, boolean setReduceApp, boolean setReduceDistinct, boolean setNewApp, boolean setNewElem, boolean setInitSearch, boolean setPush, boolean setPop, boolean setRestart, boolean setReset, boolean setFinalCheck, boolean setNewEq, boolean setNewDiseq, boolean setNewAssignment, boolean setNewRelevant);
    public static native long theoryMkSort(long ctxPtr, long thyPtr, long symPtr);
    public static native long theoryMkValue(long ctxPtr, long thyPtr, long symPtr, long sortPtr);
    public static native long theoryMkConstant(long ctxPtr, long thyPtr, long symPtr, long sortPtr);
    public static native long theoryMkFuncDecl(long ctxPtr, long thyPtr, long symPtr, int domainSize, long[] domainSorts, long rangeSort);
    public static native void theoryAssertAxiom(long thyPtr, long astPtr);
    public static native void theoryAssumeEq(long thyPtr, long t1Ptr, long t2Ptr);
    public static native void theoryEnableAxiomSimplification(long thyPtr, boolean flag);
    public static native long theoryGetEqCRoot(long thyPtr, long astPtr);
    public static native long theoryGetEqCNext(long thyPtr, long astPtr);
    public static native int theoryGetNumParents(long thyPtr, long astPtr);
    public static native long theoryGetParent(long thyPtr, long astPtr, int i);
    public static native boolean theoryIsValue(long thyPtr, long astPtr);
    public static native boolean theoryIsDecl(long thyPtr, long declPtr);
    public static native int theoryGetNumElems(long thyPtr);
    public static native long theoryGetElem(long thyPtr, int i);
    public static native int theoryGetNumApps(long thyPtr);
    public static native long theoryGetApp(long thyPtr, int i);

    // Parser interface
    public static native void parseSMTLIBString(long ctxPtr, String str, int numSorts, long[] sortNames, long[] sorts, int numDecls, long[] declNames, long[] decls);
    public static native void parseSMTLIBFile(long ctxPtr, String fileName, int numSorts, long[] sortNames, long[] sorts, int numDecls, long[] declNames, long[] decls);
    public static native long parseSMTLIB2String(long ctxPtr, String str, int numSorts, long[] sortNames, long[] sorts, int numDecls, long[] declNames, long[] decls);
    public static native long parseSMTLIB2File(long ctxPtr, String fileName, int numSorts, long[] sortNames, long[] sorts, int numDecls, long[] declNames, long[] decls);
    public static native int getSMTLIBNumFormulas(long contextPtr);
    public static native long getSMTLIBFormula(long contextPtr, int i);
    public static native int getSMTLIBNumAssumptions(long contextPtr);
    public static native long getSMTLIBAssumption(long contextPtr, int i);
    public static native int getSMTLIBNumDecls(long contextPtr);
    public static native long getSMTLIBDecl(long contextPtr, int i);
    public static native int getSMTLIBNumSorts(long contextPtr);
    public static native long getSMTLIBSort(long contextPtr, int i);
    public static native String getSMTLIBError(long contextPtr);

    // various
    public static native long substitute(long contextPtr, long astPtr, int numExprs, long[] from, long[] to);
    public static native void setAstPrintMode(long contextPtr, int mode);
    public static native long simplify(long contextPtr, long astPtr);

    // tactics and solvers
    public static native long mkTactic(long contextPtr, String name);
    public static native long tacticAndThen(long contextPtr, long tactic1Ptr, long tactic2Ptr);
    public static native long mkSolver(long contextPtr);
    public static native long mkSolverFromTactic(long contextPtr, long tacticPtr);
    public static native void tacticIncRef(long contextPtr, long tacticPtr);
    public static native void tacticDecRef(long contextPtr, long tacticPtr);

    public static native void solverPush(long contextPtr, long solverPtr);
    public static native void solverPop(long contextPtr, long solverPtr, int numScopes);
    public static native void solverAssertCnstr(long contextPtr, long solverPtr, long astPtr);
    public static native void solverReset(long contextPtr, long solverPtr);
    public static native int solverCheck(long contextPtr, long solverPtr);
    public static native long solverGetModel(long contextPtr, long solverPtr);
    public static native void solverIncRef(long contextPtr, long solverPtr);
    public static native void solverDecRef(long contextPtr, long solverPtr);
    public static native long solverGetAssertions(long contextPtr, long solverPtr);
    public static native long solverGetUnsatCore(long contextPtr, long solverPtr);
    public static native int solverGetNumScopes(long contextPtr, long solverPtr);
    public static native int solverCheckAssumptions(long contextPtr, long solverPtr, int numAssumptions, long[] assumptions);
    public static native String solverGetReasonUnknown(long contextPtr, long solverPtr);
    public static native String solverToString(long contextPtr, long solverPtr);

    // AST Vector
    public static native void astvectorIncRef(long contextPtr, long vectorPtr);
    public static native void astvectorDecRef(long contextPtr, long vectorPtr);
    public static native int astvectorSize(long contextPtr, long vectorPtr);
    public static native long astvectorGet(long contextPtr, long vectorPtr, int i);
    public static native void astvectorSet(long contextPtr, long vectorPtr, int i, long astPtr);

    // Error handling
    // Yet to come...
    // public static native void registerErrorHandler(long contextPtr, AbstractErrorHandler handler);

    // Miscellaneous
    public static native void getVersion(IntPtr major, IntPtr minor, IntPtr buildNumber, IntPtr revisionNumber);
    public static native void resetMemory();

    // DEPRECATED API
    public static native void push(long contextPtr);
    public static native void pop(long contextPtr, int numScopes);
    public static native int getNumScopes(long contextPtr);
    public static native void assertCnstr(long contextPtr, long astPtr);
    public static native int check(long contextPtr);
    public static native int checkAndGetModel(long contextPtr, Pointer model);
    public static native int checkAssumptions(long contextPtr, int numAssumptions, long[] assumptions, Pointer model, int coreSizeIn, IntPtr coreSizeOut, long[] core);
}
