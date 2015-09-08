signature STATELESS_OPS = sig
  val numeral: (int * typ) -> term
  val serial_nat: unit -> term
  val word: int -> typ
  val map: ((term * term) list * (typ * typ)) -> term
end

structure Stateless_Ops: STATELESS_OPS = struct

fun numeral (n, typ) =
  let
    fun wrap numeral = HOLogic.numeral_const typ $ numeral
  in
    if n = 0 then
      Const (@{const_name "zero_class.zero"}, typ)
    else if n > 0 then
      wrap (HOLogic.mk_numeral n)
    else
      Const (@{const_name "uminus"}, dummyT) $ wrap (HOLogic.mk_numeral (~n))
  end

val serial_nat =
  numeral o rpair @{typ nat} o serial

fun word n =
  Type (@{type_name word}, [Syntax.read_typ @{context} (Markup.print_int n)])

fun map (xs, (fty, tty)) =
  let
    val opt_tty = Type (@{type_name option}, [tty])
    val fun_ty = fty --> opt_tty
    val init = Abs ("x", fty, Const (@{const_name None}, opt_tty))
    fun aux (f, t) acc =
      Const (@{const_name fun_upd}, fun_ty --> fty --> opt_tty --> fun_ty) $ acc $ f $
        (Const (@{const_name Some}, tty --> opt_tty) $ t)
  in
    fold aux xs init
  end

end