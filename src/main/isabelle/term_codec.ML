datatype ('a, 'b) either = Left of 'a | Right of 'b

structure Codec = struct

open Codec

fun triple a b c =
  tuple a (tuple b c)
  |> transform (fn (a, (b, c)) => (a, b, c)) (fn (a, b, c) => (a, (b, c)))

fun either a b =
  let
    fun enc (Left l)  = (0, encode a l)
      | enc (Right r) = (1, encode b r)
    fun dec 0 = SOME (decode a #> map_result Left)
      | dec 1 = SOME (decode b #> map_result Right)
      | dec _ = NONE
  in Codec.variant enc dec "either" end

end

signature TERM_CODEC = sig
  val typ : typ codec
  val term : term codec
end

structure Term_Codec : TERM_CODEC = struct

val sort : sort codec = Codec.list Codec.string
val indexname : indexname codec = Codec.tuple Codec.string Codec.int

fun typ () =
  let
    fun typ_type () = Codec.tuple Codec.string (Codec.list (typ ()))
    val typ_tfree = Codec.tuple Codec.string sort
    val typ_tvar = Codec.tuple indexname sort

    fun enc (Type arg) =  (0, Codec.encode (typ_type ()) arg)
      | enc (TFree arg) = (1, Codec.encode typ_tfree arg)
      | enc (TVar arg) =  (2, Codec.encode typ_tvar arg)
    fun dec 0 = SOME (Codec.decode (typ_type ()) #> Codec.map_result Type)
      | dec 1 = SOME (Codec.decode typ_tfree #> Codec.map_result TFree)
      | dec 2 = SOME (Codec.decode typ_tvar #> Codec.map_result TVar)
      | dec _ = NONE
  in Codec.variant enc dec "Pure.typ" end

val typ = typ ()

fun term () =
  let
    val term_const = Codec.tuple Codec.string typ
    val term_free = Codec.tuple Codec.string typ
    val term_var = Codec.tuple indexname typ
    val term_bound = Codec.int
    fun term_abs () = Codec.triple Codec.string typ (term ())
    fun term_app () = Codec.tuple (term ()) (term ())

    fun enc (Const arg) = (0, Codec.encode term_const arg)
      | enc (Free arg) =  (1, Codec.encode term_free arg)
      | enc (Var arg) =   (2, Codec.encode term_var arg)
      | enc (Bound arg) = (3, Codec.encode term_bound arg)
      | enc (Abs arg) =   (4, Codec.encode (term_abs ()) arg)
      | enc (op $ arg) =  (5, Codec.encode (term_app ()) arg)
    fun dec 0 = SOME (Codec.decode term_const #> Codec.map_result Const)
      | dec 1 = SOME (Codec.decode term_free #> Codec.map_result Free)
      | dec 2 = SOME (Codec.decode term_var #> Codec.map_result Var)
      | dec 3 = SOME (Codec.decode term_bound #> Codec.map_result Bound)
      | dec 4 = SOME (Codec.decode (term_abs ()) #> Codec.map_result Abs)
      | dec 5 = SOME (Codec.decode (term_app ()) #> Codec.map_result op $)
      | dec _ = NONE
  in Codec.variant enc dec "Pure.term" end

val term = term ()

end