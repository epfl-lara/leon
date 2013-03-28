package z3;

import z3.Pointer;

// Such a class is used to redirect the callbacks from the C library. To the
// proper Scala/Java functions, and to reformat their output so that it looks
// like pointers. At this level, the pointers are still exposed.
public abstract class AbstractTheoryProxy {
    abstract void delete(long tPtr);
    abstract boolean reduceEq(long tPtr, long t1, long t2, Pointer out);
    abstract boolean reduceApp(long tPtr, long fdptr, int argc, long[] args, Pointer out);
    abstract boolean reduceDistinct(long tPtr, int argc, long[] args, Pointer out);
    abstract void newApp(long tPtr, long appPtr);
    abstract void newElem(long tPtr, long elemPtr);
    abstract void initSearch(long tPtr);
    abstract void push(long tPtr);
    abstract void pop(long tPtr);
    abstract void restart(long tPtr);
    abstract void reset(long tPtr);
    abstract boolean finalCheck(long tPtr);
    abstract void newEq(long tPtr, long t1, long t2);
    abstract void newDiseq(long tPtr, long t1, long t2);
    abstract void newAssignment(long tPtr, long pred, boolean polarity);
    abstract void newRelevant(long tPtr, long t);
}
