Require Import ssreflect ssrbool eqtype.
(* Coqルービックキューブ *)
(* 2-Rubic 
 * ブロックが2x2x2のルービックキューブを考える。
 *)

(* 関数外延性公理 *)
Axiom fun_ext :
  forall (T S : Set) (f g : T -> S),
    (forall x:T, f x = g x) <-> (f = g).

(* 関数合成 *)
Definition combine {S T U : Set} (g : S -> T) (f : T -> U) :=
  fun (s:S) => f (g s).
Infix "*" := combine : fun_scope.

Open Scope type_scope.

(* 一つの四角の状態 *)
Inductive color_t := C1|C2|C3|C4|C5|C6.

(* 一つの面の状態
 * まず一次元の面集合(line)を定義し、その集合として面(surface)を定義する
 * | 0.0 | 0.1 | <- line0
 * | 1.0 | 1.1 | <- line1
 *)
Definition line_t := color_t * color_t.
Definition surface_t := line_t * line_t.

(* 
 * 面の張り方の議論のため、その枠に名前をつける
 *         Fx+
 *         -----------> 
 * Fy+ ↑ | 0.0 | 0.1 | ￤ Fy-
 *     ￤ | 1.0 | 1.1 | ↓
 *        <-----------
 *         Fx-
 *
 * 6つの面の3つずつに分解し、2つのsegment
 * {SX+, SY+, SZ+} と {SX-, SY-, SZ-} とする。
 * 
 * 次に、以下の組について、向きが反対になるようにして結合する。
 *  SX+.Fx+ , SY+.Fy+
 *  SY+.Fx+ , SZ+.Fy+
 *  SZ+.Fx+ , SX+.Fy+ 
 *  SX-.Fx+ , SY-.Fy-
 *  SY-.Fx+ , SZ-.Fy-
 *  SZ-.Fx+ , SX-.Fy-
 * これで2つのパーツが構成された。
 * この2つの間の結合は、以下の組を向きが反対になるように結合する。
 *  SX+.Fy- , SZ-.Fx-
 *  SY+.Fy- , SX-.Fx-
 *  SZ+.Fy- , SY-.Fx-
 *  SX+.Fx- , SY-.Fy+
 *  SY+.Fx- , SZ-.Fy+
 *  SZ+.Fx- , SX-.Fy+
 * 以上により、6面体が構成される。
 *)
Inductive id_t := X | Y | Z.
Inductive pn_t := Pos | Neg.
Definition surface_id_t := id_t * pn_t.
Definition segment_t := surface_t * surface_t * surface_t.
Definition state_t := segment_t * segment_t.

(*
 * 次に、状態から状態への変換(操作)を考える。
 * 面Sを底面とした時、下からn段目を右に回転させるという操作を、
 * rot S nと表す。
 * 2-Rubic場合、2段しかないので、下のみで十分。
 *)
Definition rot (bot : surface_id_t) (s : state_t) :=
  match s with
    | ((((xp00, xp01), (xp10, xp11))
        ,((yp00, yp01), (yp10, yp11))
        ,((zp00, zp01), (zp10, zp11)))
       ,(((xn00, xn01), (xn10, xn11))
         ,((yn00, yn01), (yn10, yn11))
         ,((zn00, zn01), (zn10, zn11)))) =>
      match bot with
        | (X, Pos) => ((((xp10, xp00), (xp11, xp01))
                       ,((zp01, yp01), (zp00, yp11))
                       ,((yn10, yn00), (zp10, zp11)))
                      ,(((xn00, xn01), (xn10, xn11))
                       ,((zn10, yn01), (zn11, yn11))
                       ,((zn00, zn01), (yp00, yp10))))
        | (Y, Pos) => ((((zn10, zn00), (xp10, xp11))
                       ,((yp10, yp00), (yp11, yp01))
                       ,((xp01, zp01), (xp00, zp11)))
                      ,(((xn00, xn01), (zp00, zp10))
                       ,((yn00, yn01), (yn10, yn11))
                       ,((xn10, zn01), (xn11, zn11))))
        | (Z, Pos) => ((((yp01, xp01), (yp00, xp11))
                       ,((xn10, xn00), (yp10, yp11))
                       ,((zp10, zp00), (zp11, zp01)))
                      ,(((yn10, xn01), (yn11, xn11))
                       ,((yn00, yn01), (xp00, xp10))
                       ,((zn00, zn01), (zn10, zn11))))
        | (X, Neg) => ((((xp00, xp01), (xp10, xp11))
                       ,((yp00, zn00), (yp10, zn01))
                       ,((zp00, zp01), (yp11, yp01)))
                      ,(((xn10, xn00), (xn11, xn01))
                       ,((yn00, zp11), (yn10, zp10))
                       ,((yn01, yn11), (zn10, zn11))))
        | (Y, Neg) => ((((xp00, xp01), (zp11, zp01))
                       ,((yp00, yp01), (yp10, yp11))
                       ,((zp00, xn00), (zp10, xn01)))
                      ,(((zn01, zn11), (xn10, xn11))
                       ,((yn10, yn00), (yn11, yn01))
                       ,((zn00, xp11), (zn10, xp10))))
        | (Z, Neg) => ((((xp00, yn00), (xp10, yn01))
                       ,((yp00, yp01), (xp11, xp01))
                       ,((zp00, zp01), (zp10, zp11)))
                      ,(((xn00, yp11), (xn10, yp10))
                       ,((xn01, xn11), (yn10, yn11))
                       ,((zn10, zn00), (zn11, zn01))))
      end end.

(*
 * テスト用スペース
 *)
Section example.
  Variables xp00 xp01 xp10 xp11 yp00 yp01 yp10 yp11 zp00 zp01 zp10 zp11: color_t.
  Variables xn00 xn01 xn10 xn11 yn00 yn01 yn10 yn11 zn00 zn01 zn10 zn11: color_t.
  Definition s := ((((xp00,xp01),(xp10,xp11))
                   ,((yp00,yp01),(yp10,yp11))
                   ,((zp00,zp01),(zp10,zp11))),
                   (((xn00,xn01),(xn10,xn11))
                   ,((yn00,yn01),(yn10,yn11))
                   ,((zn00,zn01),(zn10,zn11)))).
  Eval compute in rot (Z,Pos) (rot (Z,Neg) s).
  Eval compute in rot (Z,Neg) (rot (Z,Pos) s).
End example.

(*
 * 回転操作に関する命題
 *)
Open Scope fun_scope.

(* 準備
 * Pos, Negに対しそれぞれ反対側をとる操作 pn_inv を定義する。
 *)
Definition pn_inv (pn: pn_t) : pn_t :=
  match pn with Pos => Neg | Neg => Pos end.

Section rotation_prop.
  Variable s : state_t.

  (* 4回回転すると元の状態に戻る *)
  Theorem rot_four_unit :
    forall (bot : surface_id_t),
      let r := rot bot in
      s = r (r (r (r s))).
  Proof.
    case :s => [[[[[? ?] [? ?]]     (* SX+ *)
                  [[? ?] [? ?]]]    (* SY+ *)
                  [[? ?] [? ?]]]    (* SZ+ *)
                [[[[? ?] [? ?]]     (* SX- *)
                  [[? ?] [? ?]]]    (* SY- *)
                  [[? ?] [? ?]]]].  (* SZ- *)
    by case => [] [] [] //=. Qed.

  (* 対称な面を回転させる操作について *)
  (*
   * 対称な面の回転操作は可換(互いに影響を与えないため)
   *)
  Variable W: id_t.
  Lemma rotw_comm:
    forall (pn : pn_t),
      let r := rot (W, pn) in
      let r' := rot (W, (pn_inv pn)) in
      r * r' = r' * r.
  Proof.
    move => pn /=. apply fun_ext. rewrite /combine.
    case => [[[[[? ?] [? ?]]     (* SX+ *)
               [[? ?] [? ?]]]    (* SY+ *)
               [[? ?] [? ?]]]    (* SZ+ *)
             [[[[? ?] [? ?]]     (* SX- *)
               [[? ?] [? ?]]]    (* SY- *)
               [[? ?] [? ?]]]].  (* SZ- *)
    case :W => []; case :pn => [];
    rewrite //=.
  Qed.


End rotation_prop.

(*
 * 
 *)

