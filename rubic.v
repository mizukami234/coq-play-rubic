Require Import ssreflect ssrbool eqtype.
(* Coqルービックキューブ *)

(*
 * ここから準備
 *)

(* 関数外延性公理 *)
Axiom fun_ext :
  forall (T S : Set) (f g : T -> S),
    (forall x:T, f x = g x) <-> (f = g).

(* 関数合成 *)
Definition combine {S T U : Set} (g : T -> U) (f : S -> T) :=
  fun (s:S) => g (f s).
Infix "*" := combine : fun_scope.

Local Open Scope fun_scope.
(* 関数合成の結合性 *)
Theorem combine_assoc {R S T U : Set}:
  forall (f : T -> U) (g : S -> T) (h : R -> S), (f * g) * h = f * (g * h).
Proof.
  move => f g h. apply fun_ext.
    by rewrite /combine. Qed.

(* id関数 *)
Definition ident_of (S : Set) (x : S) : S := x.

(* 左単位元になる *)
Theorem func_id_unitl {S T : Set}:
  forall (f : S -> T), (ident_of T) * f = f.
Proof. move => f. apply fun_ext. by rewrite /ident_of /combine /=. Qed.

(* 右単位元になる *)
Theorem func_id_unitr {S T : Set}:
  forall (f : S -> T), f * (ident_of S) = f.
Proof. move => f. apply fun_ext. by rewrite /ident_of /combine /=. Qed.

Local Close Scope fun_scope.
(*
 * ここまで準備
 *)



(*
 * 2-Rubic 
 * ブロックが2x2x2のルービックキューブを考える。
 *)

Open Scope type_scope.

(* 一つの枠の状態 *)
Inductive color_t := C1|C2|C3|C4|C5|C6.

(* 一つの面の状態
 * まず枠の組lineを定義し、lineの組として面surfaceを定義する
 * | 0.0 | 0.1 | <- line 1
 * | 1.0 | 1.1 | <- line 2
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
 * 一般に面Sを底面とした時、下からn段目を右に回転させるという操作を考えるべきであるが、
 * 2-Rubic場合、2段しかないので、底面を回転させる操作だけで十分。
 * それを rot S と表す。
 *)
Definition rot (bot : surface_id_t) (s : state_t) : state_t :=
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

(* 単位操作(変化しない) *)
Definition op_id := ident_of state_t.

(* 操作の結合性 *)
Definition op_assoc := @combine_assoc state_t state_t state_t state_t.

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
 * +, -に対しそれぞれ反対側をとる操作 pn_inv を定義する。
 *)
Definition pn_inv (pn: pn_t) : pn_t :=
  match pn with Pos => Neg | Neg => Pos end.

Section rotation_prop.
  (* 4回回転すると元の状態に戻る *)
  Theorem rot_four_unit :
    forall (bot : surface_id_t),
      let r := rot bot in
      op_id = r * r * r * r.
  Proof.
    case => [[][]];
    move => /=;
    apply fun_ext;
    case => [[[[[? ?] [? ?]]     (* SX+ *)
               [[? ?] [? ?]]]    (* SY+ *)
               [[? ?] [? ?]]]    (* SZ+ *)
             [[[[? ?] [? ?]]     (* SX- *)
               [[? ?] [? ?]]]    (* SY- *)
               [[? ?] [? ?]]]];  (* SZ- *)
    by rewrite /combine /op_id /=. Qed.

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
 * 回転による同値類を考える。
 * まず一回の回転操作を定義する。
 *)
Definition rotate (W : id_t) :=
  let r := rot (W, Pos) in
  let s := rot (W, Neg) in
  r*s*s*s.

(*
 * 回転は4回で元に戻る
 *)
Lemma rotate4_unit :
  forall (W : id_t), let r := rotate W in
    r * r * r * r = op_id.
Proof.
  rewrite /rotate => W.
  set r := rot (W, Pos).
  set s := rot (W, Neg).
  move :(rotw_comm W Pos).
  rewrite /= -/r -/s => COM.
  set AS := op_assoc.
  rewrite op_assoc (_ : r*s*s*s*(r*s*s*s) = r*r*s*s).
  rewrite (_ : r*r*s*s*(r*r*s*s) = r*r*r*r*(s*s*s*s)).
    by rewrite -(rot_four_unit(W, Pos)) -(rot_four_unit(W, Neg)) (func_id_unitl op_id).
    (* = congruenceはもっと早くできるか？ *)
    congruence.
  rewrite (_ : r*s*s*s*(r*s*s*s) = r*r*s*s*(s*s*s*s)).
    by rewrite -(rot_four_unit(W, Neg)) (func_id_unitr (r*r*s*s)).
    congruence. Qed.

(*
 * 回転同値関係
 *)
Inductive rotate_eq (s : state_t) : state_t -> Prop :=
| rotate_refl : rotate_eq s s
| rotate_stepr : forall (t : state_t) (W : id_t),
                  rotate_eq s t -> rotate_eq s (rotate W t).

(*
 * 補題1 : s = rotate W (rotate W (rotate W (rotate W s)))
 *)
Lemma rotate_lemma1 :
  forall (s : state_t) (W : id_t),
    s = (rotate W (rotate W (rotate W (rotate W s)))).
Proof.
  move => s W.
  set (f := rotate W).
  rewrite (_ : s = op_id s).
  rewrite (_ : f (f (f (f s))) = (f * f * f * f) s).
  by rewrite rotate4_unit.
  by rewrite /combine.
  rewrite //=. Qed.

(*
 * 補題2 : rotate W s 〜 s
 *)
Lemma rotate_lemma2 :
  forall (s : state_t) (W : id_t), rotate_eq (rotate W s) s.
Proof. move => s W.
  rewrite {2} (rotate_lemma1 s W).
  set (f := rotate W).
  do 3 apply rotate_stepr.
  by apply rotate_refl. Qed.

(*
 * 左側回転補題 : s 〜 t ならば rotate W s 〜 t
 *)
Lemma rotate_stepl :
  forall (s t : state_t) (W : id_t),
    rotate_eq s t -> rotate_eq (rotate W s) t.
Proof.
  move => s t W.
  elim. by apply rotate_lemma2.
  move => t' W' Rst' Rrst'.
  by apply rotate_stepr. Qed.

(*
 * 対称律
 *)
Theorem rotate_symm :
  forall (s t : state_t),
    rotate_eq s t -> rotate_eq t s.
Proof.
  move => s t.
  elim.
  by apply rotate_refl.
  move => u W Rsu Rus.
  by apply rotate_stepl. Qed.

(*
 * 補題3 : rotate W s 〜 t ならば s 〜 t
 *)
Lemma rotate_lemma3 :
  forall (s t: state_t) (W : id_t),
    rotate_eq (rotate W s) t -> rotate_eq s t.
Proof.
  move => s t W Rrst.
  rewrite (rotate_lemma1 s W) (rotate_lemma1 t W).
  set (f := rotate W).
  do 3 apply rotate_stepl.
  by do 4 apply rotate_stepr. Qed.

(*
 * 推移律
 *)
Theorem rotate_trans :
  forall (s t u : state_t),
    rotate_eq s t -> rotate_eq t u -> rotate_eq s u.
Proof.
  move => s t u.
  elim. by [].
  move => v W Rsv Rvu_su Rrvu.
  apply Rvu_su.
  by apply (rotate_lemma3 v u W). Qed.
