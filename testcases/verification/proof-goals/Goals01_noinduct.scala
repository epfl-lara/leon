import leon.lang._
import leon.annotation._

object Benchmark {

//-----------------------------------------------------------------------------
//                                   Axioms
//-----------------------------------------------------------------------------

    sealed abstract class Nat
    case class succ(pred:Nat) extends Nat
    case class zero() extends Nat
    def pred(n:Nat): Nat = {
        require(n!=zero())
        n match {
            case succ(p) => p
        }
    }
    
    sealed abstract class Lst
    case class cons(head:Nat,tail:Lst) extends Lst
    case class nil() extends Lst
    def head(l:Lst): Nat = {
        require(l!=nil())
        l match {
            case cons(a,_) => a
        }
    }
    def tail(l:Lst): Lst = {
        require(l!=nil())
        l match {
            case cons(_,a) => a
        }
    }
    
    sealed abstract class Pair
    case class mkpair(first:Nat,second:Nat) extends Pair
    def first(p:Pair): Nat = {
        p match {
            case mkpair(r,_) => r
        }
    }
    def second(p:Pair): Nat = {
        p match {
            case mkpair(_,r) => r
        }
    }
    
    sealed abstract class ZLst
    case class zcons(zhead:Pair,ztail:ZLst) extends ZLst
    case class znil() extends ZLst
    def zhead(l:ZLst): Pair = {
        require(l!=znil())
        l match {
            case zcons(a,_) => a
        }
    }
    def ztail(l:ZLst): ZLst = {
        require(l!=znil())
        l match {
            case zcons(_,a) => a
        }
    }
    
    sealed abstract class Tree
    case class node(data:Nat,left:Tree,right:Tree) extends Tree
    case class leaf() extends Tree
    def data(t:Tree): Nat = {
        require(t!=leaf())
        t match {
            case node(r,_,_) => r
        }
    }
    def left(t:Tree): Tree = {
        require(t!=leaf())
        t match {
            case node(_,r,_) => r
        }
    }
    def right(t:Tree): Tree = {
        require(t!=leaf())
        t match {
            case node(_,_,r) => r
        }
    }
    
    //def P(n:Nat): Boolean = {???}
    //def f(n:Nat): Nat = {???}
    
    
    
    def less(x:Nat,y:Nat): Boolean = {
        (x,y) match {
            case (_,zero()) => false
            case (zero(),succ(_)) => true
            case (succ(a),succ(b)) => less(a,b)
        }
    }

    def leq(x:Nat,y:Nat): Boolean = {
        x==y || less(x,y)
    }

    def plus(x:Nat,y:Nat): Nat = {
        (x,y) match {
            case (zero(),n) => n
            case (succ(n),m) => succ(plus(n,m))
        }
    }

    def minus(x:Nat,y:Nat): Nat = {
        (x,y) match {
            case (zero(),n) => zero()
            case (n,zero()) => n
            case (succ(n),succ(m)) => minus(n,m)
        }
    }

    def mult(x:Nat,y:Nat): Nat = {
        (x,y) match {
            case (zero(),n) => zero()
            case (succ(n),m) => plus(mult(n,m),m)
        }
    }

    def nmax(n:Nat,m:Nat): Nat = {
        if(less(n,m)) m else n
    }

    def nmin(n:Nat,m:Nat): Nat = {
        if(less(n,m)) n else m
    }

    def append(l1:Lst,l2:Lst): Lst = {
        (l1,l2) match {
            case (nil(),x) => x
            case (cons(x,y),z) => cons(x,append(y,z))
        }
    }

    def len(l:Lst): Nat = {
        (l) match {
            case (nil()) => zero()
            case (cons(_,y)) => succ(len(y))
        }
    }

    def drop(n:Nat,l:Lst): Lst = {
        (n,l) match {
            case (_,nil()) => nil()
            case (zero(),x) => x
            case (succ(x),cons(_,z)) => drop(x,z)
        }
    }

    def take(n:Nat,l:Lst): Lst = {
        (n,l) match {
            case (_,nil()) => nil()
            case (zero(),x) => nil()
            case (succ(x),cons(y,z)) => cons(y,take(x,z))
        }
    }

    def count(n:Nat,l:Lst): Nat = {
        (n,l) match {
            case (_,nil()) => zero()
            case (x,cons(y,z)) => if (x == y) succ(count(x,z)) else count(x,z)
        }
    }

    def last(l:Lst): Nat = {
        (l) match {
            case (nil()) => zero()
            case (cons(x,y)) => if (y==nil()) x else last(y)
        }
    }

    def butlast(l:Lst): Lst = {
        (l) match {
            case (nil()) => nil()
            case (cons(x,y)) => if (y==nil()) nil() else cons(x,butlast(y))
        }
    }

    def mem(n:Nat,l:Lst): Boolean = {
        (n,l) match {
            case (_,nil()) => false
            case (x,cons(y,z)) => (x==y) || (mem(x,z))
        }
    }

    def delete(n:Nat,l:Lst): Lst = {
        (n,l) match {
            case (_,nil()) => nil()
            case (x,cons(y,z)) => if (x==y) delete(x,z) else cons(y,delete(x,z))
        }
    }

    def rev(l:Lst): Lst = {
        (l) match {
            case (nil()) => nil()
            case (cons(x,y)) => append(rev(y),cons(x,nil()))
        }
    }
/*
    def lmap(l:Lst): Lst = {
        (l) match {
            case (nil()) => nil()
            case (cons(x,y)) => cons(f(x),lmap(y))
        }
    }

    def filter(l:Lst): Lst = {
        (l) match {
            case (nil()) => nil()
            case (cons(x,y)) => if(P(x)) cons(x,filter(y)) else filter(y)
        }
    }

    def dropWhile(l:Lst): Lst = {
        (l) match {
            case (nil()) => nil()
            case (cons(x,y)) => if(P(x)) dropWhile(y) else cons(x,y)
        }
    }

    def takeWhile(l:Lst): Lst = {
        (l) match {
            case (nil()) => nil()
            case (cons(x,y)) => if(P(x)) cons(x,takeWhile(y)) else nil()
        }
    }
*/
    def ins1(n:Nat,l:Lst): Lst = {
        (n,l) match {
            case (i,nil()) => cons(i,nil())
            case (i,cons(x,y)) => if (i==x) cons(x,y) else cons(x,ins1(i,y))
        }
    }

    def insort(n:Nat,l:Lst): Lst = {
        (n,l) match {
            case (i,nil()) => cons(i,nil())
            case (i,cons(x,y)) => if (less(i,x)) cons(i,cons(x,y)) else cons(x,insort(i,y))
        }
    }

    def sorted(l:Lst): Boolean = {
        (l) match {
            case (nil()) => true
            case (cons(_,nil())) => true
            case (cons(x,cons(z,y))) => sorted(cons(z,y)) && leq(x,z)
        }
    }

    def sort(l:Lst): Lst = {
        (l) match {
            case (nil()) => nil()
            case (cons(x,y)) => insort(x,sort(y))
        }
    }

    def zip(l1:Lst,l2:Lst): ZLst = {
        (l1,l2) match {
            case (nil(),_) => znil()
            case (_,nil()) => znil()
            case (cons(x,y),cons(z,w)) => zcons(mkpair(x,z),zip(y,w))
        }
    }

    def zappend(l1:ZLst,l2:ZLst): ZLst = {
        (l1,l2) match {
            case (znil(),x) => x
            case (zcons(x,y),z) => zcons(x,zappend(y,z))
        }
    }

    def zdrop(n:Nat,l:ZLst): ZLst = {
        (n,l) match {
            case (_,znil()) => znil()
            case (zero(),x) => x
            case (succ(x),zcons(_,z)) => zdrop(x,z)
        }
    }

    def ztake(n:Nat,l:ZLst): ZLst = {
        (n,l) match {
            case (_,znil()) => znil()
            case (zero(),_) => znil()
            case (succ(x),zcons(y,z)) => zcons(y,ztake(x,z))
        }
    }

    def zrev(l:ZLst): ZLst = {
        (l) match {
            case (znil()) => znil()
            case (zcons(x,y)) => zappend(zrev(y),zcons(x,znil()))
        }
    }

    def mirror(t:Tree): Tree = {
        (t) match {
            case (leaf()) => leaf()
            case (node(x,y,z)) => node(x,mirror(z),mirror(y))
        }
    }

    def height(t:Tree): Nat = {
        (t) match {
            case (leaf()) => zero()
            case (node(x,y,z)) => succ(nmax(height(y),height(z)))
        }
    }
    
    
    
    
//-----------------------------------------------------------------------------
//                                   GOALS
//-----------------------------------------------------------------------------

def G1(n:Nat, xs:Lst): Boolean = { (append(take(n, xs), drop(n, xs)) == xs) }.holds
def G2(n:Nat, l:Lst, m:Lst): Boolean = { (plus(count(n, l), count(n, m)) == count(n, append(l, m))) }.holds
def G3(n:Nat, l:Lst, m:Lst): Boolean = { leq(count(n, l), count(n, append(l, m))) }.holds
def G4(n:Nat, l:Lst): Boolean = { (plus(succ(zero()), count(n, l)) == count(n, cons(n, l))) }.holds
def G5(n:Nat, x:Nat, l:Lst): Boolean = { (!(n == x) || (plus(succ(zero()), count(n, l)) == count(n, cons(x, l)))) }.holds
def G6(n:Nat, m:Nat): Boolean = { (minus(n, plus(n, m)) == zero()) }.holds
def G7(n:Nat, m:Nat): Boolean = { (minus(plus(n, m), n) == m) }.holds
def G8(k:Nat, n:Nat, m:Nat): Boolean = { (minus(plus(k, m), plus(k, n)) == minus(m, n)) }.holds
def G9(i:Nat, j:Nat, k:Nat): Boolean = { (minus(minus(i, j), k) == minus(i, plus(j, k))) }.holds
def G10(m:Nat): Boolean = { (minus(m, m) == zero()) }.holds
def G11(xs:Lst): Boolean = { (drop(zero(), xs) == xs) }.holds
                //def G12(n:Nat, xs:Lst): Boolean = { (drop(n, lmap(xs)) == lmap(drop(n, xs))) }.holds
def G13(n:Nat, x:Nat, xs:Lst): Boolean = { (drop(succ(n), cons(x, xs)) == drop(n, xs)) }.holds
                //def G14(xs:Lst, ys:Lst): Boolean = { (filter(append(xs, ys)) == append(filter(xs), filter(ys))) }.holds
def G15(x:Nat, l:Lst): Boolean = { (len(insort(x, l)) == succ(len(l))) }.holds
def G16(xs:Lst, x:Nat): Boolean = { (!(xs == nil()) || (last(cons(x, xs)) == x)) }.holds
def G17(n:Nat): Boolean = { (leq(n, zero()) == (n == zero())) }.holds
def G18(i:Nat, m:Nat): Boolean = { less(i, succ(plus(i, m))) }.holds
def G19(n:Nat, xs:Lst): Boolean = { (len(drop(n, xs)) == minus(len(xs), n)) }.holds
def G20(l:Lst): Boolean = { (len(sort(l)) == len(l)) }.holds
def G21(n:Nat, m:Nat): Boolean = { leq(n, plus(n, m)) }.holds
def G22(a:Nat, b:Nat, c:Nat): Boolean = { (nmax(nmax(a, b), c) == nmax(a, nmax(b, c))) }.holds
def G23(a:Nat, b:Nat): Boolean = { (nmax(a, b) == nmax(b, a)) }.holds
def G24(a:Nat, b:Nat): Boolean = { ((nmax(a, b) == a) == leq(b, a)) }.holds
def G25(a:Nat, b:Nat): Boolean = { ((nmax(a, b) == b) == leq(a, b)) }.holds
def G26(x:Nat, l:Lst, t:Lst): Boolean = { (!mem(x, l) || mem(x, append(l, t))) }.holds
def G27(x:Nat, l:Lst, t:Lst): Boolean = { (!mem(x, t) || mem(x, append(l, t))) }.holds
def G28(x:Nat, l:Lst): Boolean = { mem(x, append(l, cons(x, nil()))) }.holds
def G29(x:Nat, l:Lst): Boolean = { mem(x, ins1(x, l)) }.holds
def G30(x:Nat, l:Lst): Boolean = { mem(x, insort(x, l)) }.holds
def G31(a:Nat, b:Nat, c:Nat): Boolean = { (nmin(nmin(a, b), c) == nmin(a, nmin(b, c))) }.holds
def G32(a:Nat, b:Nat): Boolean = { (nmin(a, b) == nmin(b, a)) }.holds
def G33(a:Nat, b:Nat): Boolean = { ((nmin(a, b) == a) == leq(a, b)) }.holds
def G34(a:Nat, b:Nat): Boolean = { ((nmin(a, b) == b) == leq(b, a)) }.holds
                //def G35(xs:Lst): Boolean = { (!(???) || (dropWhile(xs) == xs)) }.holds
                //def G36(xs:Lst): Boolean = { (!(???) || (takeWhile(xs) == xs)) }.holds
def G37(x:Nat, l:Lst): Boolean = { (!mem(x, delete(x, l))) }.holds
def G38(n:Nat, x:Lst): Boolean = { (count(n, append(x, cons(n, nil()))) == succ(count(n, x))) }.holds
def G39(n:Nat, h:Nat, t:Lst): Boolean = { (plus(count(n, cons(h, nil())), count(n, t)) == count(n, cons(h, t))) }.holds
def G40(xs:Lst): Boolean = { (take(zero(), xs) == nil()) }.holds
                //def G41(n:Nat, xs:Lst): Boolean = { (take(n, lmap(xs)) == lmap(take(n, xs))) }.holds
def G42(n:Nat, x:Nat, xs:Lst): Boolean = { (take(succ(n), cons(x, xs)) == cons(x, take(n, xs))) }.holds
                //def G43(xs:Lst): Boolean = { (append(takeWhile(xs), dropWhile(xs)) == xs) }.holds
def G44(x:Nat, xs:Lst, ys:Lst): Boolean = { (zip(cons(x, xs), ys) == (if ((ys == nil())) znil() else zcons(mkpair(x, head(ys)), zip(xs, tail(ys))))) }.holds//73 (74-75)
def G45(x:Nat, xs:Lst, y:Nat, ys:Lst): Boolean = { (zip(cons(x, xs), cons(y, ys)) == zcons(mkpair(x, y), zip(xs, ys))) }.holds
def G46(ys:Lst): Boolean = { (zip(nil(), ys) == znil()) }.holds
def G47(a:Tree): Boolean = { (height(mirror(a)) == height(a)) }.holds
def G48(xs:Lst): Boolean = { (xs == nil() || (butlast(append(xs, cons(last(xs), nil()))) == xs)) }.holds
def G49(xs:Lst, ys:Lst): Boolean = { (butlast(append(xs, ys)) == (if ((ys == nil())) butlast(xs) else append(xs, butlast(ys)))) }.holds
def G50(xs:Lst): Boolean = { (butlast(xs) == take(minus(len(xs), succ(zero())), xs)) }.holds
def G51(xs:Lst, x:Nat): Boolean = { (butlast(append(xs, cons(x, nil()))) == xs) }.holds
def G52(n:Nat, l:Lst): Boolean = { (count(n, l) == count(n, rev(l))) }.holds
def G53(x:Nat, l:Lst): Boolean = { (count(x, l) == count(x, sort(l))) }.holds
def G54(m:Nat, n:Nat): Boolean = { (minus(plus(m, n), n) == m) }.holds
def G55(i:Nat, j:Nat, k:Nat): Boolean = { (minus(minus(i, j), k) == minus(minus(i, k), j)) }.holds
def G56(n:Nat, xs:Lst, ys:Lst): Boolean = { (drop(n, append(xs, ys)) == append(drop(n, xs), drop(minus(n, len(xs)), ys))) }.holds
def G57(n:Nat, m:Nat, xs:Lst): Boolean = { (drop(n, drop(m, xs)) == drop(plus(n, m), xs)) }.holds
def G58(n:Nat, m:Nat, xs:Lst): Boolean = { (drop(n, take(m, xs)) == take(minus(m, n), drop(n, xs))) }.holds
def G59(n:Nat, xs:Lst, ys:Lst): Boolean = { (zdrop(n, zip(xs, ys)) == zip(drop(n, xs), drop(n, ys))) }.holds
def G60(xs:Lst, ys:Lst): Boolean = { (!(ys == nil()) || (last(append(xs, ys)) == last(xs))) }.holds
def G61(xs:Lst, ys:Lst): Boolean = { (ys == nil() || (last(append(xs, ys)) == last(ys))) }.holds
def G62(xs:Lst, ys:Lst): Boolean = { (last(append(xs, ys)) == (if ((ys == nil())) last(xs) else last(ys))) }.holds
def G63(x:Nat, xs:Lst): Boolean = { (xs == nil() || (last(cons(x, xs)) == last(xs))) }.holds
def G64(n:Nat, xs:Lst): Boolean = { (!less(n, len(xs)) || (last(drop(n, xs)) == last(xs))) }.holds
def G65(x:Nat, xs:Lst): Boolean = { (last(append(xs, cons(x, nil()))) == x) }.holds
def G66(i:Nat, m:Nat): Boolean = { less(i, succ(plus(m, i))) }.holds
                //def G67(xs:Lst): Boolean = { leq(len(filter(xs)), len(xs)) }.holds
def G68(xs:Lst): Boolean = { (len(butlast(xs)) == minus(len(xs), succ(zero()))) }.holds
def G69(x:Nat, l:Lst): Boolean = { leq(len(delete(x, l)), len(l)) }.holds
def G70(n:Nat, m:Nat): Boolean = { leq(n, plus(m, n)) }.holds
def G71(n:Nat, m:Nat): Boolean = { (!leq(m, n) || leq(m, succ(n))) }.holds
def G72(x:Nat, y:Nat, l:Lst): Boolean = { (!less(x, y) || (mem(x, insort(y, l)) == mem(x, l))) }.holds
def G73(x:Nat, y:Nat, l:Lst): Boolean = { (x == y || (mem(x, insort(y, l)) == mem(x, l))) }.holds
def G74(i:Nat, xs:Lst): Boolean = { (rev(drop(i, xs)) == take(minus(len(xs), i), rev(xs))) }.holds
                //def G75(xs:Lst): Boolean = { (rev(filter(xs)) == filter(rev(xs))) }.holds
def G76(i:Nat, xs:Lst): Boolean = { (rev(take(i, xs)) == drop(minus(len(xs), i), rev(xs))) }.holds
def G77(n:Nat, h:Nat, x:Lst): Boolean = { (n == h || (count(n, append(x, cons(h, nil()))) == count(n, x))) }.holds
def G78(n:Nat, h:Nat, t:Lst): Boolean = { (plus(count(n, t), count(n, cons(h, nil()))) == count(n, cons(h, t))) }.holds
def G79(x:Nat, l:Lst): Boolean = { (!sorted(l) || sorted(insort(x, l))) }.holds
def G80(l:Lst): Boolean = { sorted(sort(l)) }.holds
def G81(m:Nat, n:Nat, k:Nat): Boolean = { (minus(minus(succ(m), n), succ(k)) == minus(minus(m, n), k)) }.holds
def G82(n:Nat, xs:Lst, ys:Lst): Boolean = { (take(n, append(xs, ys)) == append(take(n, xs), take(minus(n, len(xs)), ys))) }.holds
def G83(n:Nat, m:Nat, xs:Lst): Boolean = { (take(n, drop(m, xs)) == drop(m, take(plus(n, m), xs))) }.holds
def G84(n:Nat, xs:Lst, ys:Lst): Boolean = { (ztake(n, zip(xs, ys)) == zip(take(n, xs), take(n, ys))) }.holds
def G85(xs:Lst, ys:Lst, zs:Lst): Boolean = { (zip(append(xs, ys), zs) == zappend(zip(xs, take(len(xs), zs)), zip(ys, drop(len(xs), zs)))) }.holds
def G86(xs:Lst, ys:Lst, zs:Lst): Boolean = { (zip(xs, append(ys, zs)) == zappend(zip(take(len(ys), xs), ys), zip(drop(len(ys), xs), zs))) }.holds
def G87(xs:Lst, ys:Lst): Boolean = { (!(len(xs) == len(ys)) || (zip(rev(xs), rev(ys)) == zrev(zip(xs, ys)))) }.holds

}


































