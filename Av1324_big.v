(* Certified computations too slow for the main file: m = 5, costing minutes,
   where the m <= 4 instances in Av1324.v cost seconds. *)

Require Import List ZArith Lia.
Import ListNotations.
Require Import Av1324.
Open Scope nat_scope.

Theorem domino_5 : Z.of_nat (Dcount 5 5) = 255642%Z.
Proof. rewrite <- Dcountf_eq. vm_compute. reflexivity. Qed.

(* Tcount at the balanced tromino of size 3, against the gridded permutations
   of [0,9) themselves: 36325 both ways. *)
Theorem tromino_count_3 : Tromino 3 = Tcount 3.
Proof. rewrite <- Trominof_eq. vm_compute. reflexivity. Qed.

Theorem tromino_3 : Z.of_nat (Tromino 3) = 36325%Z.
Proof. rewrite <- Trominof_eq. vm_compute. reflexivity. Qed.

Theorem tromino_5 : Tz 5 = 1615228302%Z.
Proof. rewrite <- Tzf_eq. vm_compute. reflexivity. Qed.

(* At m = 5: 255642^2 = 65352832164 against 42 * 1615228302 = 67839588684. *)
Theorem chebyshevZ_upto_5 : forall m, (m <= 5)%nat -> chebyshev_holdsZ m = true.
Proof.
  intros m Hm. rewrite <- chebyshev_holdsZf_eq.
  destruct m as [|[|[|[|[|[|m]]]]]]; try lia; vm_compute; reflexivity.
Qed.

Corollary chebyshev_le_5 : forall m, (m <= 5)%nat ->
  (Z.of_nat (Dcount m m) * Z.of_nat (Dcount m m)
   <= Z.of_nat (card132 m) * Z.of_nat (Tcount m))%Z.
Proof.
  intros m Hm. apply chebyshev_holds_spec.
  rewrite <- chebyshev_holdsZ_eq. apply chebyshevZ_upto_5. exact Hm.
Qed.
