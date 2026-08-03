(* The staircase variational step, certified at an explicit rational point. *)

Require Import Reals Lra.
From Interval Require Import Tactic.
Open Scope R_scope.

(* log binom(x,y) to exponential order, homogeneous of degree one *)
Definition fR (x y : R) : R := x * ln x - y * ln y - (x - y) * ln (x - y).

(* tau = ((27/4)^4/4)^(1/3), the tromino growth the Chebyshev step supplies *)
Definition ln_tau : R := (4 * ln (27 / 4) - ln 4) / 3.

Definition G3 (a b c : R) : R :=
  (3 * a * ln_tau + fR (2 * b - c) b + 2 * fR (a + c) a) / (3 * a + b).

Theorem staircase_certificate :
  G3 1 (69 / 125) (243 / 500) >= ln (10465416 / 1000000).
Proof.
  unfold G3, fR, ln_tau.
  interval with (i_prec 128).
Qed.

(* and in the exponentiated form the bound is quoted in *)
Theorem staircase_bound :
  exp (G3 1 (69 / 125) (243 / 500)) >= 10465416 / 1000000.
Proof.
  assert (H := staircase_certificate).
  assert (Hp : 0 < 10465416 / 1000000) by lra.
  apply Rle_ge. rewrite <- (exp_ln (10465416 / 1000000) Hp).
  destruct (Rle_lt_or_eq_dec _ _ (Rge_le _ _ H)) as [Hlt | Heq].
  - apply Rlt_le. apply exp_increasing. exact Hlt.
  - rewrite Heq. apply Rle_refl.
Qed.
