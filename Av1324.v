(* Structure theory for the permutation class Av(1324).  Rocq 9.0.0. *)

Require Import List Arith Lia.
Import ListNotations.

(* Occurrence predicates for 132 and 1324, indexed by position. *)

Definition has_132_at (p : list nat) (i j k : nat) : Prop :=
  (i < j)%nat /\ (j < k)%nat /\ (k < length p)%nat /\
  let vi := nth i p 0%nat in
  let vj := nth j p 0%nat in
  let vk := nth k p 0%nat in
  (vi < vk)%nat /\ (vk < vj)%nat.

Definition has_1324_at (p : list nat) (i j k l : nat) : Prop :=
  (i < j)%nat /\ (j < k)%nat /\ (k < l)%nat /\ (l < length p)%nat /\
  let vi := nth i p 0%nat in
  let vj := nth j p 0%nat in
  let vk := nth k p 0%nat in
  let vl := nth l p 0%nat in
  (vi < vk)%nat /\ (vk < vj)%nat /\ (vj < vl)%nat.

Definition contains_132 (p : list nat) : Prop :=
  exists i j k, has_132_at p i j k.

Definition contains_1324 (p : list nat) : Prop :=
  exists i j k l, has_1324_at p i j k l.

(* Indexing, membership and duplication lemmas for lists. *)

Lemma len_app : forall (l1 l2 : list nat),
  length (l1 ++ l2) = (length l1 + length l2)%nat.
Proof. induction l1 as [|a l1 IH]; intro l2; simpl; auto. Qed.

Lemma nth_app1 : forall (l1 l2 : list nat) t d,
  (t < length l1)%nat -> nth t (l1 ++ l2) d = nth t l1 d.
Proof.
  induction l1 as [|a l1 IH]; intros l2 t d H; simpl in *; [lia|].
  destruct t as [|t]; simpl; [reflexivity|]. apply IH. lia.
Qed.

Lemma nth_app2 : forall (l1 l2 : list nat) t d,
  (length l1 <= t)%nat -> nth t (l1 ++ l2) d = nth (t - length l1) l2 d.
Proof.
  induction l1 as [|a l1 IH]; intros l2 t d H; simpl in *.
  - rewrite Nat.sub_0_r. reflexivity.
  - destruct t as [|t]; [lia|]. simpl. apply IH. lia.
Qed.

Lemma nth_in : forall (l : list nat) t d,
  (t < length l)%nat -> In (nth t l d) l.
Proof.
  induction l as [|a l IH]; intros t d H; simpl in *; [lia|].
  destruct t as [|t]; simpl; [left; reflexivity|]. right. apply IH. lia.
Qed.

Lemma nth_last : forall (u : list nat) y d,
  nth (length u) (u ++ [y]) d = y.
Proof.
  intros u y d. rewrite nth_app2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma nth_Forall : forall (P : nat -> Prop) l t,
  Forall P l -> (t < length l)%nat -> P (nth t l 0%nat).
Proof.
  intros P l t HF Ht. rewrite Forall_forall in HF. apply HF. apply nth_in. exact Ht.
Qed.

Lemma nodup_app_r : forall (A B : list nat), NoDup (A ++ B) -> NoDup B.
Proof.
  induction A as [|a A IH]; intros B H; simpl in H; [exact H|].
  inversion H as [|x l Hnin Hnd Heq]; subst. apply IH. exact Hnd.
Qed.

Lemma nodup_app_disjoint : forall (A B : list nat) x,
  NoDup (A ++ B) -> In x A -> In x B -> False.
Proof.
  induction A as [|a A IH]; intros B x Hnd HA HB; simpl in *; [contradiction|].
  inversion Hnd as [|y l Hnotin Hnd' Heq]; subst.
  destruct HA as [<- | HA].
  - apply Hnotin. apply in_or_app. right. exact HB.
  - apply (IH B x Hnd' HA HB).
Qed.

(* Every 1324 occurrence carries a 132 on its first three positions. *)

Lemma pattern_1324_contains_132 : forall p i j k l,
  has_1324_at p i j k l -> has_132_at p i j k.
Proof.
  intros p i j k l H. unfold has_1324_at in H. unfold has_132_at.
  destruct H as [Hij [Hjk [Hkl [Hlen [Hik [Hkj Hjl]]]]]].
  repeat split; try lia; assumption.
Qed.

Lemma sub_1324_132 : forall p, contains_1324 p -> contains_132 p.
Proof.
  intros p [i [j [k [l H]]]]. exists i, j, k.
  apply (pattern_1324_contains_132 p i j k l). exact H.
Qed.

Lemma short_avoids_132 : forall p, (length p <= 2)%nat -> ~ contains_132 p.
Proof.
  intros p Hlen [i [j [k H]]]. unfold has_132_at in H.
  destruct H as [Hij [Hjk [Hklen _]]]. lia.
Qed.

Lemma tail_1324_gives_132 : forall l v, contains_1324 (l ++ [v]) -> contains_132 l.
Proof.
  intros l v [i [j [k [l0 H]]]]. unfold has_1324_at in H.
  destruct H as [Hij [Hjk [Hkl [Hlen [Hik [Hkj Hjl]]]]]].
  rewrite len_app in Hlen. simpl in Hlen.
  exists i, j, k. unfold has_132_at.
  rewrite (nth_app1 l [v] i 0%nat) in Hik by lia.
  rewrite (nth_app1 l [v] k 0%nat) in Hik by lia.
  rewrite (nth_app1 l [v] k 0%nat) in Hkj by lia.
  rewrite (nth_app1 l [v] j 0%nat) in Hkj by lia.
  repeat split; try lia; try assumption.
Qed.

Lemma nil_bounded : forall n, forall x, In x ([] : list nat) -> (x < n)%nat.
Proof. intros n x Hx. destruct Hx. Qed.

Lemma one_bounded : forall v n, (v < n)%nat -> forall x, In x [v] -> (x < n)%nat.
Proof.
  intros v n Hv x Hx. simpl in Hx. destruct Hx as [Hx | Hx].
  - subst; assumption.
  - contradiction.
Qed.

(* Index maps across an inserted letter, in both directions. *)

Section Transport.

Variables pre suf : list nat.
Variable n : nat.

Notation P := (length pre).

Lemma nth_ins_at : forall d, nth P (pre ++ n :: suf) d = n.
Proof.
  intro d. rewrite nth_app2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma nth_ins_lt : forall t d,
  (t < P)%nat -> nth t (pre ++ n :: suf) d = nth t (pre ++ suf) d.
Proof. intros t d H. rewrite !nth_app1 by assumption. reflexivity. Qed.

Lemma nth_ins_ge : forall t d,
  (P <= t)%nat -> nth (S t) (pre ++ n :: suf) d = nth t (pre ++ suf) d.
Proof.
  intros t d H. rewrite nth_app2 by lia. rewrite nth_app2 by lia.
  replace (S t - P)%nat with (S (t - P))%nat by lia. reflexivity.
Qed.

Lemma nth_ins_gt : forall t d,
  (P < t)%nat -> nth t (pre ++ n :: suf) d = nth (pred t) (pre ++ suf) d.
Proof.
  intros t d H. rewrite nth_app2 by lia. rewrite nth_app2 by lia.
  replace (t - P)%nat with (S (pred t - P))%nat by lia. reflexivity.
Qed.

Definition up (t : nat) : nat := if t <? P then t else S t.
Definition dn (t : nat) : nat := if t <? P then t else pred t.

Lemma up_mono : forall a b, (a < b)%nat -> (up a < up b)%nat.
Proof.
  intros a b H. unfold up.
  destruct (Nat.ltb_spec a P); destruct (Nat.ltb_spec b P); lia.
Qed.

Lemma up_nth : forall t d, nth (up t) (pre ++ n :: suf) d = nth t (pre ++ suf) d.
Proof.
  intros t d. unfold up. destruct (Nat.ltb_spec t P).
  - apply nth_ins_lt; assumption.
  - apply nth_ins_ge; assumption.
Qed.

Lemma up_len : forall t,
  (t < length (pre ++ suf))%nat -> (up t < length (pre ++ n :: suf))%nat.
Proof.
  intros t H. rewrite len_app in H. rewrite len_app. simpl. unfold up.
  destruct (Nat.ltb_spec t P); lia.
Qed.

Lemma dn_mono : forall a b,
  a <> P -> b <> P -> (a < b)%nat -> (dn a < dn b)%nat.
Proof.
  intros a b Ha Hb H. unfold dn.
  destruct (Nat.ltb_spec a P); destruct (Nat.ltb_spec b P); lia.
Qed.

Lemma dn_nth : forall t d,
  t <> P -> nth t (pre ++ n :: suf) d = nth (dn t) (pre ++ suf) d.
Proof.
  intros t d H. unfold dn. destruct (Nat.ltb_spec t P).
  - apply nth_ins_lt; assumption.
  - apply nth_ins_gt. lia.
Qed.

Lemma dn_len : forall t,
  t <> P -> (t < P + S (length suf))%nat -> (dn t < length (pre ++ suf))%nat.
Proof.
  intros t Hne H. rewrite len_app. unfold dn.
  destruct (Nat.ltb_spec t P); lia.
Qed.

Lemma ins_len : length (pre ++ n :: suf) = (P + S (length suf))%nat.
Proof. rewrite len_app. reflexivity. Qed.

End Transport.

(* The maximum may be inserted exactly where the part before it avoids 132. *)

Theorem max_insertion : forall pre suf n,
  (forall x, In x pre -> (x < n)%nat) ->
  (forall x, In x suf -> (x < n)%nat) ->
  (contains_1324 (pre ++ n :: suf) <->
   (contains_1324 (pre ++ suf) \/ contains_132 pre)).
Proof.
  intros pre suf n Hpre Hsuf. split.
  - intros [i [j [k [l H]]]]. unfold has_1324_at in H.
    destruct H as [Hij [Hjk [Hkl [Hlen [Hik [Hkj Hjl]]]]]].
    rewrite ins_len in Hlen.
    assert (Hsmall : forall t, t <> length pre ->
              (t < length pre + S (length suf))%nat ->
              (nth t (pre ++ n :: suf) 0%nat < n)%nat).
    { intros t Hne Ht.
      rewrite (dn_nth pre suf n t 0%nat Hne).
      assert (Hd : (dn pre t < length (pre ++ suf))%nat)
        by (apply (dn_len pre suf t); assumption).
      assert (Hin : In (nth (dn pre t) (pre ++ suf) 0%nat) (pre ++ suf))
        by (apply nth_in; exact Hd).
      apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      + apply Hpre; exact Hin.
      + apply Hsuf; exact Hin. }
    assert (Hk : k <> length pre).
    { intro Hc. rewrite Hc in Hkj. rewrite nth_ins_at in Hkj.
      assert (nth j (pre ++ n :: suf) 0%nat < n)%nat by (apply Hsmall; lia). lia. }
    assert (Hj : j <> length pre).
    { intro Hc. rewrite Hc in Hjl. rewrite nth_ins_at in Hjl.
      assert (nth l (pre ++ n :: suf) 0%nat < n)%nat by (apply Hsmall; lia). lia. }
    assert (Hi : i <> length pre).
    { intro Hc. rewrite Hc in Hik. rewrite nth_ins_at in Hik.
      assert (nth k (pre ++ n :: suf) 0%nat < n)%nat by (apply Hsmall; lia). lia. }
    destruct (Nat.eq_dec l (length pre)) as [Hl | Hl].
    + right. exists i, j, k. unfold has_132_at.
      rewrite Hl in Hkl.
      rewrite (nth_ins_lt pre suf n i 0%nat) in Hik by lia.
      rewrite (nth_ins_lt pre suf n k 0%nat) in Hik by lia.
      rewrite (nth_ins_lt pre suf n k 0%nat) in Hkj by lia.
      rewrite (nth_ins_lt pre suf n j 0%nat) in Hkj by lia.
      rewrite (nth_app1 pre suf i 0%nat) in Hik by lia.
      rewrite (nth_app1 pre suf k 0%nat) in Hik by lia.
      rewrite (nth_app1 pre suf k 0%nat) in Hkj by lia.
      rewrite (nth_app1 pre suf j 0%nat) in Hkj by lia.
      repeat split; try lia; try assumption.
    + left. exists (dn pre i), (dn pre j), (dn pre k), (dn pre l).
      unfold has_1324_at.
      rewrite (dn_nth pre suf n i 0%nat Hi) in Hik.
      rewrite (dn_nth pre suf n k 0%nat Hk) in Hik.
      rewrite (dn_nth pre suf n k 0%nat Hk) in Hkj.
      rewrite (dn_nth pre suf n j 0%nat Hj) in Hkj.
      rewrite (dn_nth pre suf n j 0%nat Hj) in Hjl.
      rewrite (dn_nth pre suf n l 0%nat Hl) in Hjl.
      repeat split.
      * apply dn_mono; assumption.
      * apply dn_mono; assumption.
      * apply dn_mono; assumption.
      * apply (dn_len pre suf l); assumption.
      * exact Hik.
      * exact Hkj.
      * exact Hjl.
  - intros [H1324 | H132].
    + destruct H1324 as [i [j [k [l H]]]]. unfold has_1324_at in H.
      destruct H as [Hij [Hjk [Hkl [Hlen [Hik [Hkj Hjl]]]]]].
      exists (up pre i), (up pre j), (up pre k), (up pre l).
      unfold has_1324_at.
      rewrite (up_nth pre suf n i 0%nat).
      rewrite (up_nth pre suf n j 0%nat).
      rewrite (up_nth pre suf n k 0%nat).
      rewrite (up_nth pre suf n l 0%nat).
      repeat split; try assumption.
      * apply up_mono; assumption.
      * apply up_mono; assumption.
      * apply up_mono; assumption.
      * apply (up_len pre suf n l); assumption.
    + destruct H132 as [i [j [k H]]]. unfold has_132_at in H.
      destruct H as [Hij [Hjk [Hklen [Hik Hkj]]]].
      exists i, j, k, (length pre). unfold has_1324_at.
      rewrite (nth_ins_at pre suf n 0%nat).
      rewrite (nth_ins_lt pre suf n i 0%nat) by lia.
      rewrite (nth_ins_lt pre suf n j 0%nat) by lia.
      rewrite (nth_ins_lt pre suf n k 0%nat) by lia.
      rewrite (nth_app1 pre suf i 0%nat) by lia.
      rewrite (nth_app1 pre suf j 0%nat) by lia.
      rewrite (nth_app1 pre suf k 0%nat) by lia.
      repeat split; try lia; try assumption.
      * rewrite ins_len. lia.
      * apply Hpre. apply nth_in. lia.
Qed.

Corollary max_insertion_avoid : forall pre suf n,
  (forall x, In x pre -> (x < n)%nat) ->
  (forall x, In x suf -> (x < n)%nat) ->
  (~ contains_1324 (pre ++ n :: suf) <->
   (~ contains_1324 (pre ++ suf) /\ ~ contains_132 pre)).
Proof.
  intros pre suf n Hpre Hsuf.
  destruct (max_insertion pre suf n Hpre Hsuf) as [Hfwd Hbwd].
  split.
  - intro H. split; intro C; apply H; apply Hbwd; [left | right]; exact C.
  - intros [H1 H2] C. destruct (Hfwd C) as [C' | C']; [apply H1 | apply H2]; exact C'.
Qed.

(* A maximum in one of the first three positions joins no 1324 occurrence. *)
Corollary insertion_inert : forall pre suf n,
  (forall x, In x pre -> (x < n)%nat) ->
  (forall x, In x suf -> (x < n)%nat) ->
  (length pre <= 2)%nat ->
  (~ contains_1324 (pre ++ n :: suf) <-> ~ contains_1324 (pre ++ suf)).
Proof.
  intros pre suf n Hpre Hsuf Hlen.
  destruct (max_insertion_avoid pre suf n Hpre Hsuf) as [Hf Hb].
  split.
  - intro H. destruct (Hf H) as [H1 _]. exact H1.
  - intro H. apply Hb. split; [exact H | apply short_avoids_132; exact Hlen].
Qed.

Corollary insertion_at_end : forall pre n,
  (forall x, In x pre -> (x < n)%nat) ->
  (~ contains_1324 (pre ++ [n]) <-> ~ contains_132 pre).
Proof.
  intros pre n Hpre.
  destruct (max_insertion_avoid pre [] n Hpre (nil_bounded n)) as [Hf Hb].
  rewrite app_nil_r in Hf, Hb.
  split.
  - intro H. destruct (Hf H) as [_ H2]. exact H2.
  - intro H. apply Hb. split.
    + intro C. apply H. apply sub_1324_132. exact C.
    + exact H.
Qed.

Corollary insertion_second_last : forall pre v n,
  (forall x, In x pre -> (x < n)%nat) -> (v < n)%nat ->
  (~ contains_1324 (pre ++ [n; v]) <-> ~ contains_132 pre).
Proof.
  intros pre v n Hpre Hv.
  destruct (max_insertion_avoid pre [v] n Hpre (one_bounded v n Hv)) as [Hf Hb].
  split.
  - intro H. destruct (Hf H) as [_ H2]. exact H2.
  - intro H. apply Hb. split.
    + intro C. apply H. apply (tail_1324_gives_132 pre v). exact C.
    + exact H.
Qed.

(* With 1 first and n last the interior admits no inversion. *)
Theorem corner_rigidity : forall mid n,
  (forall x, In x mid -> (1 < x)%nat /\ (x < n)%nat) ->
  ~ contains_1324 (1%nat :: mid ++ [n]) ->
  forall i j, (i < j)%nat -> (j < length mid)%nat ->
    ~ (nth j mid 0%nat < nth i mid 0%nat)%nat.
Proof.
  intros mid n Hb Hav i j Hij Hj Hinv.
  assert (Hi : (i < length mid)%nat) by lia.
  destruct (Hb _ (nth_in mid i 0%nat Hi)) as [Hi1 Hin].
  destruct (Hb _ (nth_in mid j 0%nat Hj)) as [Hj1 Hjn].
  apply Hav. exists 0%nat, (S i), (S j), (S (length mid)).
  assert (E0 : nth 0%nat (1%nat :: mid ++ [n]) 0%nat = 1%nat) by reflexivity.
  assert (Ei : nth (S i) (1%nat :: mid ++ [n]) 0%nat = nth i mid 0%nat).
  { simpl. apply nth_app1. exact Hi. }
  assert (Ej : nth (S j) (1%nat :: mid ++ [n]) 0%nat = nth j mid 0%nat).
  { simpl. apply nth_app1. exact Hj. }
  assert (En : nth (S (length mid)) (1%nat :: mid ++ [n]) 0%nat = n).
  { simpl. rewrite nth_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
  assert (Elen : length (1%nat :: mid ++ [n]) = S (S (length mid))).
  { simpl. rewrite len_app. simpl. lia. }
  unfold has_1324_at. cbv zeta.
  rewrite E0, Ei, Ej, En, Elen.
  repeat split; lia.
Qed.

(* Appending y creates a 1324 exactly when some 132 has its '3' below y. *)

Theorem append_1324 : forall u y,
  contains_1324 (u ++ [y]) <->
  (contains_1324 u \/
   (exists i j k, has_132_at u i j k /\ (nth j u 0%nat < y)%nat)).
Proof.
  intros u y. split.
  - intros [i [j [k [l H]]]]. unfold has_1324_at in H.
    destruct H as [Hij [Hjk [Hkl [Hlen [Hik [Hkj Hjl]]]]]].
    rewrite len_app in Hlen. simpl in Hlen.
    destruct (Nat.eq_dec l (length u)) as [Hl | Hl].
    + right. exists i, j, k. unfold has_132_at.
      rewrite Hl in Hjl. rewrite nth_last in Hjl.
      rewrite (nth_app1 u [y] i 0%nat) in Hik by lia.
      rewrite (nth_app1 u [y] k 0%nat) in Hik by lia.
      rewrite (nth_app1 u [y] k 0%nat) in Hkj by lia.
      rewrite (nth_app1 u [y] j 0%nat) in Hkj by lia.
      rewrite (nth_app1 u [y] j 0%nat) in Hjl by lia.
      repeat split; try lia; try assumption.
    + left. exists i, j, k, l. unfold has_1324_at.
      rewrite (nth_app1 u [y] i 0%nat) in Hik by lia.
      rewrite (nth_app1 u [y] k 0%nat) in Hik by lia.
      rewrite (nth_app1 u [y] k 0%nat) in Hkj by lia.
      rewrite (nth_app1 u [y] j 0%nat) in Hkj by lia.
      rewrite (nth_app1 u [y] j 0%nat) in Hjl by lia.
      rewrite (nth_app1 u [y] l 0%nat) in Hjl by lia.
      repeat split; try lia; try assumption.
  - intros [H | H].
    + destruct H as [i [j [k [l H]]]]. unfold has_1324_at in H.
      destruct H as [Hij [Hjk [Hkl [Hlen [Hik [Hkj Hjl]]]]]].
      exists i, j, k, l. unfold has_1324_at.
      rewrite (nth_app1 u [y] i 0%nat) by lia.
      rewrite (nth_app1 u [y] j 0%nat) by lia.
      rewrite (nth_app1 u [y] k 0%nat) by lia.
      rewrite (nth_app1 u [y] l 0%nat) by lia.
      repeat split; try lia; try assumption.
      rewrite len_app. simpl. lia.
    + destruct H as [i [j [k [H132 Hy]]]]. unfold has_132_at in H132.
      destruct H132 as [Hij [Hjk [Hklen [Hik Hkj]]]].
      exists i, j, k, (length u). unfold has_1324_at.
      rewrite nth_last.
      rewrite (nth_app1 u [y] i 0%nat) by lia.
      rewrite (nth_app1 u [y] j 0%nat) by lia.
      rewrite (nth_app1 u [y] k 0%nat) by lia.
      repeat split; try lia; try assumption.
      rewrite len_app. simpl. lia.
Qed.

(* Legality of y, as a lower bound on the '3'-values of the prefix. *)
Corollary append_rule : forall u y,
  ~ contains_1324 u ->
  (~ contains_1324 (u ++ [y]) <->
   (forall i j k, has_132_at u i j k -> (y <= nth j u 0%nat)%nat)).
Proof.
  intros u y Hu. split.
  - intros H i j k H132.
    destruct (Nat.le_gt_cases y (nth j u 0%nat)) as [Hle | Hgt]; [exact Hle|].
    exfalso. apply H. apply append_1324. right.
    exists i, j, k. split; [exact H132 | lia].
  - intros H C. apply append_1324 in C. destruct C as [C | C].
    + apply Hu; exact C.
    + destruct C as [i [j [k [H132 Hy]]]]. specialize (H i j k H132). lia.
Qed.

Corollary av132_prefix_free : forall u y,
  ~ contains_132 u -> ~ contains_1324 (u ++ [y]).
Proof.
  intros u y H C. apply append_1324 in C. destruct C as [C | C].
  - apply H. apply sub_1324_132. exact C.
  - destruct C as [i [j [k [H132 _]]]]. apply H. exists i, j, k. exact H132.
Qed.

(* The letters legal after a fixed prefix form a down-set. *)

Theorem append_downward_closed : forall u y y',
  (y' <= y)%nat ->
  ~ contains_1324 (u ++ [y]) ->
  ~ contains_1324 (u ++ [y']).
Proof.
  intros u y y' Hle Hy C.
  apply append_1324 in C. apply Hy. apply append_1324.
  destruct C as [C | C]; [left; exact C|].
  right. destruct C as [i [j [k [H132 Hlt]]]].
  exists i, j, k. split; [exact H132 | lia].
Qed.

Corollary append_segment : forall u y y',
  (y' <= y)%nat ->
  contains_1324 (u ++ [y']) ->
  contains_1324 (u ++ [y]).
Proof.
  intros u y y' Hle C.
  apply append_1324 in C. apply append_1324.
  destruct C as [C | C]; [left; exact C|].
  right. destruct C as [i [j [k [H132 Hlt]]]].
  exists i, j, k. split; [exact H132 | lia].
Qed.

(* A letter below every entry of the prefix is legal. *)

Theorem append_new_minimum : forall u y,
  (forall x, In x u -> (y < x)%nat) ->
  ~ contains_1324 u ->
  ~ contains_1324 (u ++ [y]).
Proof.
  intros u y Hmin Hu C.
  apply append_1324 in C.
  destruct C as [C | C].
  - apply Hu; exact C.
  - destruct C as [i [j [k [H132 Hy]]]].
    unfold has_132_at in H132.
    destruct H132 as [Hij [Hjk [Hklen [_ _]]]].
    assert (Hin : In (nth j u 0%nat) u) by (apply nth_in; lia).
    specialize (Hmin _ Hin). lia.
Qed.

Fixpoint below (y : nat) (u : list nat) : Prop :=
  match u with
  | [] => True
  | x :: r => (y < x)%nat /\ below y r
  end.

Lemma below_In : forall y u x, below y u -> In x u -> (y < x)%nat.
Proof.
  induction u as [|a u IH]; intros x Hb Hin; simpl in *; [contradiction|].
  destruct Hb as [Ha Hb]. destruct Hin as [<- | Hin]; [exact Ha | apply IH; assumption].
Qed.

Corollary append_below : forall u y,
  below y u -> ~ contains_1324 u -> ~ contains_1324 (u ++ [y]).
Proof.
  intros u y Hb Hu.
  apply append_new_minimum; [intros x Hin; apply (below_In y u x); assumption | exact Hu].
Qed.

Fixpoint decreasing_below (y : nat) (l : list nat) : Prop :=
  match l with
  | [] => True
  | z :: r => (z < y)%nat /\ decreasing_below z r
  end.

Lemma below_app : forall u y z,
  below y u -> (z < y)%nat -> below z (u ++ [y]).
Proof.
  induction u as [|a u IH]; intros y z Hb Hz; simpl in *.
  - split; [lia | exact I].
  - destruct Hb as [Ha Hb]. split; [lia | apply IH; assumption].
Qed.

(* A decreasing tail below the current minimum is always legal. *)
Theorem append_decreasing_tail : forall l u y,
  below y u -> decreasing_below y l -> ~ contains_1324 u ->
  ~ contains_1324 (u ++ [y] ++ l).
Proof.
  induction l as [|z l IH]; intros u y Hb Hd Hu; simpl.
  - apply append_below; assumption.
  - destruct Hd as [Hz Hd].
    assert (Hnext : ~ contains_1324 (u ++ [y])) by (apply append_below; assumption).
    assert (Hb' : below z (u ++ [y])) by (apply below_app; assumption).
    specialize (IH (u ++ [y]) z Hb' Hd Hnext).
    rewrite <- app_assoc in IH. simpl in IH. exact IH.
Qed.

(* Safety at v is a split into a part at or above v followed by a part below. *)

(* v creates no 132-pattern in the '2' role. *)
Definition safe_at (u : list nat) (v : nat) : Prop :=
  ~ (exists i j, (i < j)%nat /\ (j < length u)%nat /\
                 (nth i u 0%nat < v)%nat /\ (v <= nth j u 0%nat)%nat).

(* Safety is exactly a block splitting at v. *)
Theorem safe_iff_split : forall p v,
  safe_at p v <->
  exists A B, p = A ++ B /\ Forall (fun x => (v <= x)%nat) A
                         /\ Forall (fun x => (x < v)%nat) B.
Proof.
  intros p v. split.
  - induction p as [|a p IH]; intro H.
    + exists [], []. simpl. repeat split; constructor.
    + destruct (Nat.le_gt_cases v a) as [Hva | Hav].
      * assert (Hp : safe_at p v).
        { intros [i [j [Hij [Hj [Hi Hjv]]]]].
          apply H. exists (S i), (S j). simpl. repeat split; try lia. }
        destruct (IH Hp) as [A [B [Heq [HA HB]]]].
        exists (a :: A), B. simpl. rewrite Heq.
        repeat split; [constructor; assumption | assumption].
      * exists [], (a :: p). simpl. repeat split; [constructor|].
        constructor; [exact Hav|].
        rewrite Forall_forall. intros x Hx.
        destruct (Nat.le_gt_cases v x) as [Hvx | Hxv]; [|exact Hxv].
        exfalso.
        apply In_nth with (d := 0%nat) in Hx.
        destruct Hx as [t [Ht Hnth]].
        apply H. exists 0%nat, (S t). simpl. rewrite Hnth.
        repeat split; try lia.
  - intros [A [B [Heq [HA HB]]]] [i [j [Hij [Hj [Hi Hjv]]]]].
    subst p. rewrite len_app in Hj.
    assert (HiA : (length A <= i)%nat).
    { destruct (Nat.le_gt_cases (length A) i) as [Hle | Hlt]; [exact Hle|].
      exfalso. rewrite (nth_app1 A B i 0%nat Hlt) in Hi.
      assert (v <= nth i A 0%nat)%nat by (apply nth_Forall; assumption). lia. }
    assert (HjA : (length A <= j)%nat) by lia.
    rewrite (nth_app2 A B j 0%nat HjA) in Hjv.
    assert (nth (j - length A) B 0%nat < v)%nat by (apply nth_Forall; [assumption | lia]).
    lia.
Qed.

(* In a 132-avoider the maximum separates. *)
Theorem split_132 : forall pre suf n,
  (forall x, In x pre -> (x < n)%nat) ->
  (forall x, In x suf -> (x < n)%nat) ->
  ~ contains_132 (pre ++ n :: suf) ->
  forall a b, In a pre -> In b suf -> ~ (a < b)%nat.
Proof.
  intros pre suf n Hpre Hsuf Hno a b Ha Hb Hab.
  apply In_nth with (d := 0%nat) in Ha. destruct Ha as [i [Hi Hai]].
  apply In_nth with (d := 0%nat) in Hb. destruct Hb as [t [Ht Hbt]].
  apply Hno.
  exists i, (length pre), (length pre + S t)%nat.
  unfold has_132_at.
  assert (Ei : nth i (pre ++ n :: suf) 0%nat = a).
  { rewrite (nth_app1 pre (n :: suf) i 0%nat Hi). exact Hai. }
  assert (En : nth (length pre) (pre ++ n :: suf) 0%nat = n).
  { rewrite nth_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
  assert (Eb : nth (length pre + S t) (pre ++ n :: suf) 0%nat = b).
  { rewrite nth_app2 by lia.
    replace (length pre + S t - length pre)%nat with (S t) by lia.
    simpl. exact Hbt. }
  rewrite Ei, En, Eb. rewrite len_app. simpl.
  assert (b < n)%nat by (apply Hsuf; rewrite <- Hbt; apply nth_in; exact Ht).
  repeat split; try lia.
Qed.

Corollary split_132_dominates : forall pre suf n,
  (forall x, In x pre -> (x < n)%nat) ->
  (forall x, In x suf -> (x < n)%nat) ->
  ~ contains_132 (pre ++ n :: suf) ->
  forall a b, In a pre -> In b suf -> (b <= a)%nat.
Proof.
  intros pre suf n Hpre Hsuf Hno a b Ha Hb.
  destruct (Nat.le_gt_cases b a) as [Hle | Hgt]; [exact Hle|].
  exfalso. apply (split_132 pre suf n Hpre Hsuf Hno a b Ha Hb). lia.
Qed.

(* Past a 132-free prefix the '2' of any occurrence lies in the tail. *)

Theorem tail_confinement : forall pre tail i j k l,
  ~ contains_132 pre ->
  has_1324_at (pre ++ tail) i j k l ->
  (length pre <= k)%nat.
Proof.
  intros pre tail i j k l Hpre H132.
  destruct (Nat.le_gt_cases (length pre) k) as [Hle | Hgt]; [exact Hle|].
  exfalso. apply Hpre.
  apply pattern_1324_contains_132 in H132.
  unfold has_132_at in H132.
  destruct H132 as [Hij [Hjk [Hklen [Hik Hkj]]]].
  exists i, j, k. unfold has_132_at.
  rewrite (nth_app1 pre tail i 0%nat) in Hik by lia.
  rewrite (nth_app1 pre tail k 0%nat) in Hik by lia.
  rewrite (nth_app1 pre tail k 0%nat) in Hkj by lia.
  rewrite (nth_app1 pre tail j 0%nat) in Hkj by lia.
  repeat split; try lia; assumption.
Qed.

Corollary tail_confinement_both : forall pre tail i j k l,
  ~ contains_132 pre ->
  has_1324_at (pre ++ tail) i j k l ->
  (length pre <= k)%nat /\ (length pre < l)%nat.
Proof.
  intros pre tail i j k l Hpre H.
  assert (Hk : (length pre <= k)%nat)
    by (apply (tail_confinement pre tail i j k l); assumption).
  split; [exact Hk|].
  unfold has_1324_at in H. destruct H as [_ [_ [Hkl _]]]. lia.
Qed.

Corollary empty_tail_avoids : forall pre,
  ~ contains_132 pre -> ~ contains_1324 pre.
Proof.
  intros pre Hpre [i [j [k [l H]]]].
  assert (Hc : has_1324_at (pre ++ []) i j k l) by (rewrite app_nil_r; exact H).
  apply (tail_confinement pre [] i j k l Hpre) in Hc.
  unfold has_1324_at in H. destruct H as [_ [_ [Hkl [Hlen _]]]]. lia.
Qed.

(* Occurrences past a 132-free prefix, located by tail offset. *)

Theorem localise : forall pre tail,
  ~ contains_132 pre ->
  (contains_1324 (pre ++ tail) <->
   exists t t' i j,
     (t < t')%nat /\ (t' < length tail)%nat /\
     (i < j)%nat /\ (j < length pre + t)%nat /\
     (nth i (pre ++ tail) 0%nat < nth (length pre + t) (pre ++ tail) 0%nat)%nat /\
     (nth (length pre + t) (pre ++ tail) 0%nat < nth j (pre ++ tail) 0%nat)%nat /\
     (nth j (pre ++ tail) 0%nat < nth (length pre + t') (pre ++ tail) 0%nat)%nat).
Proof.
  intros pre tail Hpre. split.
  - intros [i [j [k [l H]]]].
    assert (Hk : (length pre <= k)%nat)
      by (apply (tail_confinement pre tail i j k l); assumption).
    unfold has_1324_at in H.
    destruct H as [Hij [Hjk [Hkl [Hlen [Hik [Hkj Hjl]]]]]].
    rewrite len_app in Hlen.
    exists (k - length pre)%nat, (l - length pre)%nat, i, j.
    replace (length pre + (k - length pre))%nat with k by lia.
    replace (length pre + (l - length pre))%nat with l by lia.
    repeat split; try lia; assumption.
  - intros [t [t' [i [j [Htt' [Ht' [Hij [Hj [H1 [H2 H3]]]]]]]]]].
    exists i, j, (length pre + t)%nat, (length pre + t')%nat.
    unfold has_1324_at.
    rewrite len_app.
    repeat split; try lia; assumption.
Qed.

Corollary localise_avoid : forall pre tail,
  ~ contains_132 pre ->
  (~ contains_1324 (pre ++ tail) <->
   forall t t' i j,
     (t < t')%nat -> (t' < length tail)%nat ->
     (i < j)%nat -> (j < length pre + t)%nat ->
     (nth i (pre ++ tail) 0%nat < nth (length pre + t) (pre ++ tail) 0%nat)%nat ->
     (nth (length pre + t) (pre ++ tail) 0%nat < nth j (pre ++ tail) 0%nat)%nat ->
     ~ (nth j (pre ++ tail) 0%nat < nth (length pre + t') (pre ++ tail) 0%nat)%nat).
Proof.
  intros pre tail Hpre. split.
  - intros Hno t t' i j Ht Ht' Hij Hj H1 H2 H3.
    apply Hno. apply (localise pre tail Hpre).
    exists t, t', i, j. repeat split; assumption.
  - intros Hall C.
    apply (localise pre tail Hpre) in C.
    destruct C as [t [t' [i [j [Htt' [Ht' [Hij [Hj [H1 [H2 H3]]]]]]]]]].
    exact (Hall t t' i j Htt' Ht' Hij Hj H1 H2 H3).
Qed.

(* A safe value between two candidate positions separates them. *)

(* Position j would carry the '3' of a 132-pattern created by appending y. *)
Definition candidate (u : list nat) (y j : nat) : Prop :=
  (j < length u)%nat /\ (y <= nth j u 0%nat)%nat /\
  exists i, (i < j)%nat /\ (nth i u 0%nat < y)%nat.

Lemma candidate_ge : forall u y j,
  candidate u y j -> (y <= nth j u 0%nat)%nat.
Proof. intros u y j [_ [Hy _]]. exact Hy. Qed.

Theorem candidate_below_safe : forall u y v j,
  safe_at u v -> (y < v)%nat -> candidate u y j ->
  (nth j u 0%nat < v)%nat.
Proof.
  intros u y v j Hsafe Hyv [Hj [Hy [i [Hij Hi]]]].
  destruct (Nat.le_gt_cases v (nth j u 0%nat)) as [Hge | Hlt]; [|exact Hlt].
  exfalso. apply Hsafe. exists i, j. repeat split; try lia.
Qed.

Corollary no_safe_in_window : forall u y v j,
  candidate u y j -> (y < v)%nat -> (v <= nth j u 0%nat)%nat -> ~ safe_at u v.
Proof.
  intros u y v j Hc Hyv Hvj Hsafe.
  assert (Hlt : (nth j u 0%nat < v)%nat)
    by (apply (candidate_below_safe u y v j); assumption).
  lia.
Qed.

Corollary window_under_next_safe : forall u y v,
  (y < v)%nat -> safe_at u v ->
  forall j, candidate u y j -> (nth j u 0%nat < v)%nat.
Proof.
  intros u y v Hyv Hsafe j Hc.
  apply (candidate_below_safe u y v j); assumption.
Qed.

Theorem cross_block_lower : forall u y z j v,
  candidate u y j ->
  safe_at u v -> (z < v)%nat -> (v <= y)%nat ->
  (z < nth j u 0%nat)%nat.
Proof.
  intros u y z j v Hc Hsafe Hzv Hvy.
  assert (Hy : (y <= nth j u 0%nat)%nat) by (apply (candidate_ge u y j); exact Hc).
  lia.
Qed.

Theorem cross_block_upper : forall u y z j v,
  candidate u y j ->
  safe_at u v -> (y < v)%nat -> (v <= z)%nat ->
  (nth j u 0%nat < z)%nat.
Proof.
  intros u y z j v Hc Hsafe Hyv Hvz.
  assert (H : (nth j u 0%nat < v)%nat)
    by (apply (candidate_below_safe u y v j); assumption).
  lia.
Qed.

Corollary cross_block_decided : forall u y z j v,
  candidate u y j -> safe_at u v ->
  ((z < v)%nat /\ (v <= y)%nat -> (z < nth j u 0%nat)%nat) /\
  ((y < v)%nat /\ (v <= z)%nat -> ~ (z < nth j u 0%nat)%nat).
Proof.
  intros u y z j v Hc Hsafe. split.
  - intros [Hzv Hvy]. apply (cross_block_lower u y z j v); assumption.
  - intros [Hyv Hvz] Hcontra.
    assert (H : (nth j u 0%nat < z)%nat)
      by (apply (cross_block_upper u y z j v); assumption).
    lia.
Qed.

(* Across a dominating split a 1324 occurs on one side, never across. *)

Theorem block_split_1324 : forall A B,
  (forall a b, In a A -> In b B -> (b < a)%nat) ->
  (contains_1324 (A ++ B) <-> contains_1324 A \/ contains_1324 B).
Proof.
  intros A B Hdom. split.
  - intros [i [j [k [l H]]]]. unfold has_1324_at in H.
    destruct H as [Hij [Hjk [Hkl [Hlen [Hik [Hkj Hjl]]]]]].
    rewrite len_app in Hlen.
    destruct (Nat.lt_ge_cases l (length A)) as [Hl | Hl].
    + left. exists i, j, k, l. unfold has_1324_at.
      rewrite (nth_app1 A B i 0%nat) in Hik by lia.
      rewrite (nth_app1 A B k 0%nat) in Hik by lia.
      rewrite (nth_app1 A B k 0%nat) in Hkj by lia.
      rewrite (nth_app1 A B j 0%nat) in Hkj by lia.
      rewrite (nth_app1 A B j 0%nat) in Hjl by lia.
      rewrite (nth_app1 A B l 0%nat) in Hjl by lia.
      repeat split; try lia; try assumption.
    + assert (Hdrop : forall t, (t < length A)%nat ->
                (nth l (A ++ B) 0%nat < nth t (A ++ B) 0%nat)%nat).
      { intros t Ht.
        rewrite (nth_app1 A B t 0%nat Ht).
        rewrite (nth_app2 A B l 0%nat Hl).
        apply Hdom.
        - apply nth_in; exact Ht.
        - apply nth_in. lia. }
      assert (Hi : (length A <= i)%nat).
      { destruct (Nat.lt_ge_cases i (length A)) as [Hc | Hc]; [|exact Hc].
        specialize (Hdrop i Hc). lia. }
      assert (Hj : (length A <= j)%nat) by lia.
      assert (Hk : (length A <= k)%nat) by lia.
      right.
      exists (i - length A)%nat, (j - length A)%nat,
             (k - length A)%nat, (l - length A)%nat.
      unfold has_1324_at.
      rewrite (nth_app2 A B i 0%nat Hi) in Hik.
      rewrite (nth_app2 A B k 0%nat Hk) in Hik.
      rewrite (nth_app2 A B k 0%nat Hk) in Hkj.
      rewrite (nth_app2 A B j 0%nat Hj) in Hkj.
      rewrite (nth_app2 A B j 0%nat Hj) in Hjl.
      rewrite (nth_app2 A B l 0%nat Hl) in Hjl.
      repeat split; try lia; try assumption.
  - intros [HA | HB].
    + destruct HA as [i [j [k [l H]]]]. unfold has_1324_at in H.
      destruct H as [Hij [Hjk [Hkl [Hlen [Hik [Hkj Hjl]]]]]].
      exists i, j, k, l. unfold has_1324_at.
      rewrite (nth_app1 A B i 0%nat) by lia.
      rewrite (nth_app1 A B j 0%nat) by lia.
      rewrite (nth_app1 A B k 0%nat) by lia.
      rewrite (nth_app1 A B l 0%nat) by lia.
      rewrite len_app.
      repeat split; try lia; try assumption.
    + destruct HB as [i [j [k [l H]]]]. unfold has_1324_at in H.
      destruct H as [Hij [Hjk [Hkl [Hlen [Hik [Hkj Hjl]]]]]].
      exists (length A + i)%nat, (length A + j)%nat,
             (length A + k)%nat, (length A + l)%nat.
      unfold has_1324_at.
      rewrite (nth_app2 A B (length A + i) 0%nat) by lia.
      rewrite (nth_app2 A B (length A + j) 0%nat) by lia.
      rewrite (nth_app2 A B (length A + k) 0%nat) by lia.
      rewrite (nth_app2 A B (length A + l) 0%nat) by lia.
      replace (length A + i - length A)%nat with i by lia.
      replace (length A + j - length A)%nat with j by lia.
      replace (length A + k - length A)%nat with k by lia.
      replace (length A + l - length A)%nat with l by lia.
      rewrite len_app.
      repeat split; try lia; try assumption.
Qed.

Corollary block_split_avoid : forall A B,
  (forall a b, In a A -> In b B -> (b < a)%nat) ->
  (~ contains_1324 (A ++ B) <-> ~ contains_1324 A /\ ~ contains_1324 B).
Proof.
  intros A B Hdom.
  destruct (block_split_1324 A B Hdom) as [Hf Hb].
  split.
  - intro H. split; intro C; apply H; apply Hb; [left | right]; exact C.
  - intros [H1 H2] C. destruct (Hf C) as [C' | C']; [apply H1 | apply H2]; exact C'.
Qed.

(* Candidate positions transfer across a dominating split. *)

Theorem candidates_low : forall A B y j,
  (forall a, In a A -> (y <= a)%nat) ->
  (candidate (A ++ B) y j <->
   ((length A <= j)%nat /\ candidate B y (j - length A)%nat)).
Proof.
  intros A B y j HA. unfold candidate. split.
  - intros [Hj [Hy [i [Hij Hi]]]].
    rewrite len_app in Hj.
    assert (HiA : (length A <= i)%nat).
    { destruct (Nat.lt_ge_cases i (length A)) as [Hc | Hc]; [|exact Hc].
      exfalso. rewrite (nth_app1 A B i 0%nat Hc) in Hi.
      assert (y <= nth i A 0%nat)%nat by (apply HA; apply nth_in; exact Hc).
      lia. }
    assert (HjA : (length A <= j)%nat) by lia.
    rewrite (nth_app2 A B j 0%nat HjA) in Hy.
    rewrite (nth_app2 A B i 0%nat HiA) in Hi.
    split; [exact HjA|].
    repeat split; [lia | exact Hy |].
    exists (i - length A)%nat. split; [lia | exact Hi].
  - intros [HjA [Hj [Hy [i [Hij Hi]]]]].
    rewrite (nth_app2 A B j 0%nat HjA).
    repeat split; [rewrite len_app; lia | exact Hy |].
    exists (length A + i)%nat.
    rewrite (nth_app2 A B (length A + i) 0%nat) by lia.
    replace (length A + i - length A)%nat with i by lia.
    split; [lia | exact Hi].
Qed.

Theorem candidates_high : forall A B y j,
  (forall b, In b B -> (b < y)%nat) ->
  (candidate (A ++ B) y j <-> candidate A y j).
Proof.
  intros A B y j HB. unfold candidate. split.
  - intros [Hj [Hy [i [Hij Hi]]]].
    rewrite len_app in Hj.
    assert (HjA : (j < length A)%nat).
    { destruct (Nat.lt_ge_cases j (length A)) as [Hc | Hc]; [exact Hc|].
      exfalso. rewrite (nth_app2 A B j 0%nat Hc) in Hy.
      assert (nth (j - length A) B 0%nat < y)%nat
        by (apply HB; apply nth_in; lia).
      lia. }
    rewrite (nth_app1 A B j 0%nat HjA) in Hy.
    rewrite (nth_app1 A B i 0%nat) in Hi by lia.
    repeat split; [exact HjA | exact Hy |].
    exists i. split; [lia | exact Hi].
  - intros [Hj [Hy [i [Hij Hi]]]].
    rewrite (nth_app1 A B j 0%nat Hj).
    repeat split; [rewrite len_app; lia | exact Hy |].
    exists i. rewrite (nth_app1 A B i 0%nat) by lia.
    split; [lia | exact Hi].
Qed.

(* The profile of a word: the '3'-values of its 132 occurrences. *)

Definition three_value (u : list nat) (w : nat) : Prop :=
  exists i j k, has_132_at u i j k /\ nth j u 0%nat = w.

Definition candidate_strict (u : list nat) (y j : nat) : Prop :=
  (j < length u)%nat /\ (y < nth j u 0%nat)%nat /\
  exists i, (i < j)%nat /\ (nth i u 0%nat < y)%nat.

Lemma candidate_strict_weaken : forall u y j,
  candidate_strict u y j -> candidate u y j.
Proof.
  intros u y j [Hj [Hy [i [Hij Hi]]]].
  unfold candidate. repeat split; [exact Hj | lia |].
  exists i. split; [exact Hij | exact Hi].
Qed.

(* Legality is decided by the profile. *)
Theorem append_rule_profile : forall u y,
  ~ contains_1324 u ->
  (~ contains_1324 (u ++ [y]) <-> forall w, three_value u w -> (y <= w)%nat).
Proof.
  intros u y Hu. split.
  - intros H w [i [j [k [H132 Hw]]]].
    rewrite <- Hw. apply (append_rule u y Hu) with (i := i) (k := k); [exact H | exact H132].
  - intros H. apply (append_rule u y Hu).
    intros i j k H132. apply H. exists i, j, k. split; [exact H132 | reflexivity].
Qed.

Corollary profile_determines_legality : forall u u' y,
  ~ contains_1324 u -> ~ contains_1324 u' ->
  (forall w, three_value u w <-> three_value u' w) ->
  (~ contains_1324 (u ++ [y]) <-> ~ contains_1324 (u' ++ [y])).
Proof.
  intros u u' y Hu Hu' Hsame.
  rewrite (append_rule_profile u y Hu), (append_rule_profile u' y Hu').
  split; intros H w Hw; apply H; apply Hsame; exact Hw.
Qed.

(* The profile gains exactly the values at strict candidate positions. *)
Theorem three_values_append : forall u y w,
  three_value (u ++ [y]) w <->
  (three_value u w \/ exists j, candidate_strict u y j /\ nth j u 0%nat = w).
Proof.
  intros u y w. split.
  - intros [i [j [k [H132 Hw]]]].
    unfold has_132_at in H132.
    destruct H132 as [Hij [Hjk [Hklen [Hik Hkj]]]].
    rewrite len_app in Hklen. simpl in Hklen.
    destruct (Nat.eq_dec k (length u)) as [Hk | Hk].
    + right. exists j.
      rewrite Hk in Hik, Hkj.
      rewrite nth_last in Hik, Hkj.
      rewrite (nth_app1 u [y] i 0%nat) in Hik by lia.
      rewrite (nth_app1 u [y] j 0%nat) in Hkj by lia.
      rewrite (nth_app1 u [y] j 0%nat) in Hw by lia.
      split; [| exact Hw].
      unfold candidate_strict. repeat split; [lia | lia |].
      exists i. split; [lia | exact Hik].
    + left. exists i, j, k.
      rewrite (nth_app1 u [y] i 0%nat) in Hik by lia.
      rewrite (nth_app1 u [y] k 0%nat) in Hik by lia.
      rewrite (nth_app1 u [y] k 0%nat) in Hkj by lia.
      rewrite (nth_app1 u [y] j 0%nat) in Hkj by lia.
      rewrite (nth_app1 u [y] j 0%nat) in Hw by lia.
      split; [| exact Hw].
      unfold has_132_at. repeat split; try lia; assumption.
  - intros [H | [j [Hc Hw]]].
    + destruct H as [i [j [k [H132 Hw]]]].
      unfold has_132_at in H132.
      destruct H132 as [Hij [Hjk [Hklen [Hik Hkj]]]].
      exists i, j, k. split; [| rewrite (nth_app1 u [y] j 0%nat) by lia; exact Hw].
      unfold has_132_at.
      rewrite (nth_app1 u [y] i 0%nat) by lia.
      rewrite (nth_app1 u [y] j 0%nat) by lia.
      rewrite (nth_app1 u [y] k 0%nat) by lia.
      repeat split; try lia; try assumption.
      rewrite len_app. simpl. lia.
    + destruct Hc as [Hj [Hyj [i [Hij Hi]]]].
      exists i, j, (length u). split.
      * unfold has_132_at.
        rewrite nth_last.
        rewrite (nth_app1 u [y] i 0%nat) by lia.
        rewrite (nth_app1 u [y] j 0%nat) by lia.
        repeat split; try lia; try assumption.
        rewrite len_app. simpl. lia.
      * rewrite (nth_app1 u [y] j 0%nat) by lia. exact Hw.
Qed.

Theorem profile_transition_closed : forall u u' y,
  (forall w, three_value u w <-> three_value u' w) ->
  (forall w, (exists j, candidate_strict u y j /\ nth j u 0%nat = w) <->
             (exists j, candidate_strict u' y j /\ nth j u' 0%nat = w)) ->
  (forall w, three_value (u ++ [y]) w <-> three_value (u' ++ [y]) w).
Proof.
  intros u u' y Hprof Hcand w.
  rewrite (three_values_append u y w), (three_values_append u' y w).
  split; intros [H | H].
  - left. apply Hprof; exact H.
  - right. apply Hcand; exact H.
  - left. apply Hprof; exact H.
  - right. apply Hcand; exact H.
Qed.

Corollary profile_empty_iff : forall u,
  ~ contains_132 u <-> forall w, ~ three_value u w.
Proof.
  intros u. split.
  - intros H w [i [j [k [H132 _]]]]. apply H. exists i, j, k. exact H132.
  - intros H [i [j [k H132]]]. apply (H (nth j u 0%nat)).
    exists i, j, k. split; [exact H132 | reflexivity].
Qed.

Corollary profile_empty_all_legal : forall u y,
  ~ contains_132 u -> ~ contains_1324 (u ++ [y]).
Proof. intros u y H. apply av132_prefix_free. exact H. Qed.

(* A letter at or below K is decided by the profile below K alone. *)

Theorem legality_capped : forall u z K,
  ~ contains_1324 u -> (z <= K)%nat ->
  (~ contains_1324 (u ++ [z]) <->
   (forall w, three_value u w -> (w < K)%nat -> (z <= w)%nat)).
Proof.
  intros u z K Hu Hz.
  destruct (append_rule_profile u z Hu) as [Hf Hb].
  split.
  - intros H w Hw _. exact (Hf H w Hw).
  - intros H. apply Hb. intros w Hw.
    destruct (Nat.lt_ge_cases w K) as [Hlt | Hge].
    + exact (H w Hw Hlt).
    + lia.
Qed.

Corollary capped_profile_determines_legality : forall u u' z K,
  ~ contains_1324 u -> ~ contains_1324 u' -> (z <= K)%nat ->
  (forall w, (w < K)%nat -> (three_value u w <-> three_value u' w)) ->
  (~ contains_1324 (u ++ [z]) <-> ~ contains_1324 (u' ++ [z])).
Proof.
  intros u u' z K Hu Hu' Hz Hsame.
  destruct (legality_capped u z K Hu Hz) as [Hf Hb].
  destruct (legality_capped u' z K Hu' Hz) as [Hf' Hb'].
  split.
  - intro H. apply Hb'. intros w Hw Hlt.
    apply (Hf H w); [apply (proj2 (Hsame w Hlt)); exact Hw | exact Hlt].
  - intro H. apply Hb. intros w Hw Hlt.
    apply (Hf' H w); [apply (proj1 (Hsame w Hlt)); exact Hw | exact Hlt].
Qed.

Theorem capped_profile_closed : forall u u' z K,
  (forall w, (w < K)%nat -> (three_value u w <-> three_value u' w)) ->
  (forall w, (w < K)%nat ->
     ((exists j, candidate_strict u z j /\ nth j u 0%nat = w) <->
      (exists j, candidate_strict u' z j /\ nth j u' 0%nat = w))) ->
  (forall w, (w < K)%nat ->
     (three_value (u ++ [z]) w <-> three_value (u' ++ [z]) w)).
Proof.
  intros u u' z K Hp Hc w Hw.
  rewrite (three_values_append u z w), (three_values_append u' z w).
  split; intros [H | H].
  - left. apply (Hp w Hw); exact H.
  - right. apply (Hc w Hw); exact H.
  - left. apply (Hp w Hw); exact H.
  - right. apply (Hc w Hw); exact H.
Qed.

Theorem capped_legal_avoids : forall u y K,
  ~ contains_1324 u -> (y <= K)%nat ->
  (forall w, three_value u w -> (w < K)%nat -> (y <= w)%nat) ->
  ~ contains_1324 (u ++ [y]).
Proof.
  intros u y K Hu Hy H.
  apply (legality_capped u y K Hu Hy). exact H.
Qed.

Corollary capped_from_132_free : forall u y K,
  ~ contains_132 u -> (y <= K)%nat -> ~ contains_1324 (u ++ [y]).
Proof. intros u y K H _. apply av132_prefix_free. exact H. Qed.

Theorem capped_monotone : forall u y K K',
  (K <= K')%nat -> (y <= K)%nat ->
  (forall w, three_value u w -> (w < K')%nat -> (y <= w)%nat) ->
  (forall w, three_value u w -> (w < K)%nat -> (y <= w)%nat).
Proof.
  intros u y K K' HK Hy H w Hw Hlt.
  apply H; [exact Hw | lia].
Qed.

(* Occurrence, profile membership and least elements are decidable. *)

Lemma has_132_at_dec : forall u i j k, {has_132_at u i j k} + {~ has_132_at u i j k}.
Proof.
  intros u i j k. unfold has_132_at. cbv zeta.
  destruct (lt_dec i j) as [H1|H1]; [|right; tauto].
  destruct (lt_dec j k) as [H2|H2]; [|right; tauto].
  destruct (lt_dec k (length u)) as [H3|H3]; [|right; tauto].
  destruct (lt_dec (nth i u 0%nat) (nth k u 0%nat)) as [H4|H4]; [|right; tauto].
  destruct (lt_dec (nth k u 0%nat) (nth j u 0%nat)) as [H5|H5]; [|right; tauto].
  left. repeat split; assumption.
Defined.

Lemma bounded_ex_dec : forall (P : nat -> Prop) n,
  (forall i, {P i} + {~ P i}) ->
  {exists i, (i < n)%nat /\ P i} + {~ exists i, (i < n)%nat /\ P i}.
Proof.
  intros P n Hdec. induction n as [|n IH].
  - right. intros [i [Hi _]]. lia.
  - destruct IH as [Hex | Hno].
    + left. destruct Hex as [i [Hi HP]]. exists i. split; [lia | exact HP].
    + destruct (Hdec n) as [HP | HP].
      * left. exists n. split; [lia | exact HP].
      * right. intros [i [Hi HPi]].
        destruct (Nat.eq_dec i n) as [Heq | Hne]; [subst; contradiction|].
        apply Hno. exists i. split; [lia | exact HPi].
Defined.

Lemma three_value_dec : forall u w, {three_value u w} + {~ three_value u w}.
Proof.
  intros u w.
  assert (Hd : {exists i, (i < length u)%nat /\
                 exists j, (j < length u)%nat /\
                 exists k, (k < length u)%nat /\
                   (has_132_at u i j k /\ nth j u 0%nat = w)}
             + {~ exists i, (i < length u)%nat /\
                 exists j, (j < length u)%nat /\
                 exists k, (k < length u)%nat /\
                   (has_132_at u i j k /\ nth j u 0%nat = w)}).
  { apply bounded_ex_dec. intro i.
    apply bounded_ex_dec. intro j.
    apply bounded_ex_dec. intro k.
    destruct (has_132_at_dec u i j k) as [H | H]; [|right; tauto].
    destruct (Nat.eq_dec (nth j u 0%nat) w) as [He | He]; [|right; tauto].
    left. split; assumption. }
  destruct Hd as [H | H].
  - left. destruct H as [i [_ [j [_ [k [_ [H132 Hw]]]]]]].
    exists i, j, k. split; assumption.
  - right. intros [i [j [k [H132 Hw]]]].
    apply H. unfold has_132_at in H132.
    destruct H132 as [Hij [Hjk [Hklen [Hik Hkj]]]].
    exists i. split; [lia|]. exists j. split; [lia|]. exists k. split; [lia|].
    split; [unfold has_132_at; repeat split; assumption | exact Hw].
Qed.

Lemma least_dec : forall (P : nat -> Prop),
  (forall n, {P n} + {~ P n}) ->
  forall n, P n -> exists m, P m /\ forall k, P k -> (m <= k)%nat.
Proof.
  intros P Hdec.
  assert (Haux : forall b, (exists i, (i < b)%nat /\ P i) ->
                 exists m, P m /\ forall k, P k -> (m <= k)%nat).
  { induction b as [|b IH]; intros Hex.
    - exfalso. destruct Hex as [i [Hi _]]. lia.
    - destruct (bounded_ex_dec P b Hdec) as [Hex' | Hno].
      + apply IH. exact Hex'.
      + destruct Hex as [i [Hi HPi]].
        assert (Hib : i = b).
        { destruct (Nat.lt_ge_cases i b) as [Hlt | Hge]; [|lia].
          exfalso. apply Hno. exists i. split; [exact Hlt | exact HPi]. }
        subst i. exists b. split; [exact HPi|].
        intros k Hk. destruct (Nat.lt_ge_cases k b) as [Hlt | Hge]; [|lia].
        exfalso. apply Hno. exists k. split; [exact Hlt | exact Hk]. }
  intros n Hn. apply (Haux (S n)). exists n. split; [lia | exact Hn].
Qed.

(* The legal letters are those at or below mu, the least profile element. *)

Definition is_mu (u : list nat) (m : nat) : Prop :=
  three_value u m /\ forall w, three_value u w -> (m <= w)%nat.

Theorem mu_exists : forall u,
  contains_132 u -> exists m, is_mu u m.
Proof.
  intros u [i [j [k H132]]].
  assert (Hw : three_value u (nth j u 0%nat))
    by (exists i, j, k; split; [exact H132 | reflexivity]).
  destruct (least_dec (three_value u) (three_value_dec u) _ Hw) as [m [Hm Hleast]].
  exists m. split; assumption.
Qed.

Definition legal (u : list nat) (y : nat) : Prop := ~ contains_1324 (u ++ [y]).

(* The legal letters are the initial segment cut at mu. *)
Theorem legal_iff_le_mu : forall u m,
  ~ contains_1324 u -> is_mu u m ->
  forall y, legal u y <-> (y <= m)%nat.
Proof.
  intros u m Hu [Hm Hleast] y. unfold legal.
  rewrite (append_rule_profile u y Hu). split.
  - intro H. apply H. exact Hm.
  - intros Hy w Hw. specialize (Hleast w Hw). lia.
Qed.

Theorem legal_all_when_132_free : forall u,
  ~ contains_132 u -> forall y, legal u y.
Proof. intros u H y. unfold legal. apply av132_prefix_free. exact H. Qed.

Lemma in_seq_le : forall N y, In y (seq 0 (S N)) <-> (y <= N)%nat.
Proof. intros N y. rewrite in_seq. lia. Qed.

Theorem legal_enumeration : forall u m N,
  ~ contains_1324 u -> is_mu u m ->
  forall y, (legal u y /\ (y <= N)%nat) <-> In y (seq 0 (S (Nat.min m N))).
Proof.
  intros u m N Hu Hmu y.
  rewrite in_seq_le.
  destruct (legal_iff_le_mu u m Hu Hmu y) as [Hf Hb].
  split.
  - intros [Hl Hy]. specialize (Hf Hl). lia.
  - intro H. split; [apply Hb; lia | lia].
Qed.

(* min(mu,N)+1 legal letters at or below N. *)
Corollary legal_count : forall u m N,
  ~ contains_1324 u -> is_mu u m ->
  length (seq 0 (S (Nat.min m N))) = S (Nat.min m N).
Proof. intros. apply length_seq. Qed.

Corollary legal_count_free : forall u N,
  ~ contains_132 u ->
  forall y, (legal u y /\ (y <= N)%nat) <-> In y (seq 0 (S N)).
Proof.
  intros u N H y. rewrite in_seq_le. split.
  - intros [_ Hy]. exact Hy.
  - intro Hy. split; [apply legal_all_when_132_free; exact H | exact Hy].
Qed.

(* A 132-free word is indecomposable exactly when its maximum is last. *)

Definition dominates (A B : list nat) : Prop :=
  forall a b, In a A -> In b B -> (b < a)%nat.

Definition decomposable (u : list nat) : Prop :=
  exists A B, u = A ++ B /\ A <> [] /\ B <> [] /\ dominates A B.

Definition indecomposable (u : list nat) : Prop := ~ decomposable u.

Theorem max_not_last_decomposable : forall pre suf n,
  (forall x, In x pre -> (x < n)%nat) ->
  (forall x, In x suf -> (x < n)%nat) ->
  NoDup (pre ++ n :: suf) ->
  ~ contains_132 (pre ++ n :: suf) ->
  suf <> [] ->
  decomposable (pre ++ n :: suf).
Proof.
  intros pre suf n Hpre Hsuf Hnd Hno Hsuf_ne.
  exists (pre ++ [n]), suf.
  repeat split.
  - rewrite <- app_assoc. reflexivity.
  - intro Hc. apply (app_eq_nil pre [n]) in Hc. destruct Hc as [_ Hc]. discriminate.
  - exact Hsuf_ne.
  - intros a b Ha Hb.
    apply in_app_or in Ha. destruct Ha as [Ha | Ha].
    + assert (Hle : (b <= a)%nat)
        by (apply (split_132_dominates pre suf n Hpre Hsuf Hno a b Ha Hb)).
      destruct (Nat.eq_dec b a) as [Heq | Hne]; [|lia].
      exfalso. subst b.
      apply (nodup_app_disjoint pre (n :: suf) a Hnd Ha).
      right. exact Hb.
    + simpl in Ha. destruct Ha as [<- | []].
      apply Hsuf. exact Hb.
Qed.

Theorem max_last_indecomposable : forall v n,
  (forall x, In x v -> (x < n)%nat) ->
  NoDup (v ++ [n]) ->
  indecomposable (v ++ [n]).
Proof.
  intros v n Hv Hnd [A [B [Heq [HA [HB Hdom]]]]].
  assert (HnB : In n B).
  { destruct (exists_last HB) as [B' [b Hb]].
    assert (Hlast : v ++ [n] = (A ++ B') ++ [b]).
    { rewrite Heq, Hb, app_assoc. reflexivity. }
    apply app_inj_tail in Hlast. destruct Hlast as [_ Hbn].
    subst b. rewrite Hb. apply in_or_app. right. left. reflexivity. }
  destruct A as [|a A]; [contradiction HA; reflexivity|].
  assert (HaA : In a (a :: A)) by (left; reflexivity).
  specialize (Hdom a n HaA HnB).
  assert (Hin : In a (v ++ [n])) by (rewrite Heq; apply in_or_app; left; exact HaA).
  apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - specialize (Hv a Hin). lia.
  - simpl in Hin. destruct Hin as [<- | []]. lia.
Qed.

Corollary indecomposable_iff_max_last : forall pre suf n,
  (forall x, In x pre -> (x < n)%nat) ->
  (forall x, In x suf -> (x < n)%nat) ->
  NoDup (pre ++ n :: suf) ->
  ~ contains_132 (pre ++ n :: suf) ->
  (indecomposable (pre ++ n :: suf) <-> suf = []).
Proof.
  intros pre suf n Hpre Hsuf Hnd Hno. split.
  - intro Hind. destruct suf as [|s suf]; [reflexivity|].
    exfalso. apply Hind.
    apply (max_not_last_decomposable pre (s :: suf) n Hpre Hsuf Hnd Hno).
    discriminate.
  - intro Hs. subst suf.
    apply (max_last_indecomposable pre n Hpre Hnd).
Qed.

Corollary block_body_free : forall v n,
  ~ contains_132 v -> ~ contains_1324 (v ++ [n]).
Proof. intros v n H. apply av132_prefix_free. exact H. Qed.

(* A block avoids 132 exactly when its body does. *)

Lemma prefix_132_lifts : forall v w,
  contains_132 v -> contains_132 (v ++ w).
Proof.
  intros v w [i [j [k H]]]. unfold has_132_at in H.
  destruct H as [Hij [Hjk [Hklen [Hik Hkj]]]].
  exists i, j, k. unfold has_132_at.
  rewrite (nth_app1 v w i 0%nat) by lia.
  rewrite (nth_app1 v w j 0%nat) by lia.
  rewrite (nth_app1 v w k 0%nat) by lia.
  rewrite len_app.
  repeat split; try lia; assumption.
Qed.

Corollary prefix_avoids_132 : forall v w,
  ~ contains_132 (v ++ w) -> ~ contains_132 v.
Proof. intros v w H Hc. apply H. apply prefix_132_lifts. exact Hc. Qed.

(* A new maximum can be neither the middle nor the last entry of a 132. *)
Lemma append_max_avoids_132 : forall v n,
  (forall x, In x v -> (x < n)%nat) ->
  ~ contains_132 v ->
  ~ contains_132 (v ++ [n]).
Proof.
  intros v n Hmax Hv [i [j [k H]]]. unfold has_132_at in H.
  destruct H as [Hij [Hjk [Hklen [Hik Hkj]]]].
  rewrite len_app in Hklen. simpl in Hklen.
  destruct (Nat.eq_dec k (length v)) as [Hk | Hk].
  - exfalso. rewrite Hk in Hik, Hkj. rewrite nth_last in Hik, Hkj.
    rewrite (nth_app1 v [n] j 0%nat) in Hkj by lia.
    assert (Hin : In (nth j v 0%nat) v) by (apply nth_in; lia).
    specialize (Hmax _ Hin). lia.
  - apply Hv. exists i, j, k. unfold has_132_at.
    rewrite (nth_app1 v [n] i 0%nat) in Hik by lia.
    rewrite (nth_app1 v [n] k 0%nat) in Hik by lia.
    rewrite (nth_app1 v [n] k 0%nat) in Hkj by lia.
    rewrite (nth_app1 v [n] j 0%nat) in Hkj by lia.
    repeat split; try lia; assumption.
Qed.

(* Blocks with maximum n are exactly the 132-avoiders with n appended. *)
Theorem block_iff_body : forall v n,
  (forall x, In x v -> (x < n)%nat) ->
  NoDup (v ++ [n]) ->
  ((~ contains_132 (v ++ [n]) /\ indecomposable (v ++ [n])) <-> ~ contains_132 v).
Proof.
  intros v n Hmax Hnd. split.
  - intros [H132 _]. apply (prefix_avoids_132 v [n]). exact H132.
  - intro Hv. split.
    + apply append_max_avoids_132; assumption.
    + apply max_last_indecomposable; assumption.
Qed.

Corollary block_body_unique : forall (v v' : list nat) (n : nat),
  v ++ [n] = v' ++ [n] -> v = v'.
Proof.
  intros v v' n H. apply app_inj_tail in H. destruct H as [H _]. exact H.
Qed.

(* Splitting a repetition-free word at its maximum. *)

Lemma in_pre_max : forall (pre suf : list nat) n x,
  In x (pre ++ [n]) -> In x (pre ++ n :: suf).
Proof.
  intros pre suf n x H. apply in_app_or in H. apply in_or_app.
  destruct H as [H | H]; [left; exact H|].
  right. simpl in H. destruct H as [<- | []]. left. reflexivity.
Qed.

Lemma nodup_pre_max : forall (pre suf : list nat) n,
  NoDup (pre ++ n :: suf) -> NoDup (pre ++ [n]).
Proof.
  induction pre as [|a pre IH]; intros suf n H; simpl in *.
  - constructor; [intros []| constructor].
  - inversion H as [|x l Hnin Hnd Heq]; subst.
    constructor.
    + intro Hc. apply Hnin. apply (in_pre_max pre suf n a). exact Hc.
    + apply (IH suf n). exact Hnd.
Qed.

Lemma exists_max_split : forall u, NoDup u -> u <> [] ->
  exists pre n suf, u = pre ++ n :: suf /\
    (forall x, In x pre -> (x < n)%nat) /\ (forall x, In x suf -> (x < n)%nat).
Proof.
  induction u as [|a u IH]; intros Hnd Hne; [contradiction Hne; reflexivity|].
  destruct u as [|b u'].
  - exists [], a, []. simpl. repeat split; intros x []; contradiction.
  - inversion Hnd as [|x l Hnin Hnd' Heq]; subst.
    destruct (IH Hnd' ltac:(discriminate)) as [pre [m [suf [Heq' [Hpre Hsuf]]]]].
    assert (Hle : forall x, In x (b :: u') -> (x <= m)%nat).
    { intros x Hx. rewrite Heq' in Hx. apply in_app_or in Hx.
      destruct Hx as [Hx | Hx]; [apply Nat.lt_le_incl; apply Hpre; exact Hx|].
      simpl in Hx. destruct Hx as [<- | Hx]; [lia|].
      apply Nat.lt_le_incl; apply Hsuf; exact Hx. }
    destruct (Nat.lt_ge_cases a m) as [Ham | Hma].
    + exists (a :: pre), m, suf. simpl. rewrite Heq'. repeat split.
      * intros x Hx. destruct Hx as [<- | Hx]; [exact Ham | apply Hpre; exact Hx].
      * exact Hsuf.
    + assert (Hne' : a <> m).
      { intro Hc. apply Hnin. rewrite Heq', Hc. apply in_or_app. right. left. reflexivity. }
      exists [], a, (b :: u'). simpl. repeat split.
      * intros x []; contradiction.
      * intros x Hx. specialize (Hle x Hx). lia.
Qed.

Lemma suffix_avoids_132 : forall pre suf,
  ~ contains_132 (pre ++ suf) -> ~ contains_132 suf.
Proof.
  intros pre suf H [i [j [k H132]]]. unfold has_132_at in H132.
  destruct H132 as [Hij [Hjk [Hklen [Hik Hkj]]]].
  apply H. exists (length pre + i)%nat, (length pre + j)%nat, (length pre + k)%nat.
  unfold has_132_at.
  rewrite (nth_app2 pre suf (length pre + i) 0%nat) by lia.
  rewrite (nth_app2 pre suf (length pre + j) 0%nat) by lia.
  rewrite (nth_app2 pre suf (length pre + k) 0%nat) by lia.
  replace (length pre + i - length pre)%nat with i by lia.
  replace (length pre + j - length pre)%nat with j by lia.
  replace (length pre + k - length pre)%nat with k by lia.
  rewrite len_app.
  repeat split; try lia; assumption.
Qed.

(* Every 132-free word factors uniquely into dominating indecomposable blocks. *)

Inductive block_factor : list nat -> list (list nat) -> Prop :=
| bf_nil  : block_factor [] []
| bf_cons : forall u B rest bs,
    u = B ++ rest ->
    B <> [] -> indecomposable B -> dominates B rest ->
    block_factor rest bs ->
    block_factor u (B :: bs).

Lemma dominates_app_r : forall A B C,
  dominates A B -> dominates A C -> dominates A (B ++ C).
Proof.
  intros A B C HB HC a b Ha Hb. apply in_app_or in Hb.
  destruct Hb as [Hb | Hb]; [apply HB | apply HC]; assumption.
Qed.

Lemma dominates_sub_l : forall A A' B,
  (forall x, In x A' -> In x A) -> dominates A B -> dominates A' B.
Proof. intros A A' B Hsub H a b Ha Hb. apply H; [apply Hsub|]; assumption. Qed.

Lemma factor_cons_inv : forall u B bs,
  block_factor u (B :: bs) ->
  exists rest, u = B ++ rest /\ B <> [] /\ indecomposable B /\
               dominates B rest /\ block_factor rest bs.
Proof.
  intros u B bs H. remember (B :: bs) as l eqn:Hl.
  destruct H as [| u0 B0 rest bs0 Heq Hne Hind Hdom Hrest].
  - discriminate Hl.
  - injection Hl as HB Hbs. subst B0 bs0.
    exists rest. repeat split; assumption.
Qed.

Lemma factor_concat : forall u bs, block_factor u bs -> concat bs = u.
Proof.
  induction 1 as [| u0 B rest bs Heq HBne HBind HBdom Hrest IH]; simpl;
    [reflexivity | rewrite IH; symmetry; exact Heq].
Qed.

Lemma factor_blocks_ne : forall u bs,
  block_factor u bs -> Forall (fun B => B <> []) bs.
Proof.
  induction 1 as [| u0 B rest bs Heq HBne HBind HBdom Hrest IH];
    [constructor | constructor; assumption].
Qed.

Lemma factor_nil : forall bs, block_factor [] bs -> bs = [].
Proof.
  intros bs H. destruct bs as [|B bs']; [reflexivity|].
  exfalso.
  assert (Hc : concat (B :: bs') = []) by (apply factor_concat; exact H).
  simpl in Hc. apply app_eq_nil in Hc. destruct Hc as [HB _].
  assert (HF : Forall (fun B => B <> []) (B :: bs'))
    by (apply (factor_blocks_ne [] (B :: bs')); exact H).
  apply (Forall_inv HF). exact HB.
Qed.

Lemma factor_app : forall A bsA B bsB,
  dominates A B -> block_factor A bsA -> block_factor B bsB ->
  block_factor (A ++ B) (bsA ++ bsB).
Proof.
  intros A bsA B bsB Hdom HA. revert B bsB Hdom.
  induction HA as [| u0 B1 restA bsA0 Heq HB1ne HB1ind HB1dom HrestA IH];
    intros C bsC Hdom HC; simpl.
  - simpl. exact HC.
  - subst u0.
    apply (bf_cons ((B1 ++ restA) ++ C) B1 (restA ++ C) (bsA0 ++ bsC)).
    + rewrite <- app_assoc. reflexivity.
    + exact HB1ne.
    + exact HB1ind.
    + apply dominates_app_r; [exact HB1dom|].
      apply (dominates_sub_l (B1 ++ restA) B1 C);
        [intros x Hx; apply in_or_app; left; exact Hx | exact Hdom].
    + apply IH; [| exact HC].
      apply (dominates_sub_l (B1 ++ restA) restA C);
        [intros x Hx; apply in_or_app; right; exact Hx | exact Hdom].
Qed.

Lemma factor_exists_k : forall k u,
  (length u <= k)%nat -> NoDup u -> ~ contains_132 u ->
  exists bs, block_factor u bs.
Proof.
  induction k as [|k IH]; intros u Hk Hnd H132.
  - destruct u as [|a u]; [exists []; constructor | simpl in Hk; lia].
  - destruct u as [|a u]; [exists []; constructor|].
    destruct (exists_max_split (a :: u) Hnd ltac:(discriminate))
      as [pre [n [suf [Heq [Hpre Hsuf]]]]].
    rewrite Heq in Hnd, H132, Hk |- *.
    assert (Hdom : dominates (pre ++ [n]) suf).
    { intros x b Hx Hb. apply in_app_or in Hx. destruct Hx as [Hx | Hx].
      - assert (Hle : (b <= x)%nat)
          by (apply (split_132_dominates pre suf n Hpre Hsuf H132 x b Hx Hb)).
        destruct (Nat.eq_dec b x) as [Hc | Hc]; [|lia].
        exfalso. subst b.
        apply (nodup_app_disjoint pre (n :: suf) x Hnd Hx). right. exact Hb.
      - simpl in Hx. destruct Hx as [<- | []]. apply Hsuf. exact Hb. }
    assert (Hsufnd : NoDup suf).
    { assert (H1 : NoDup (n :: suf)) by (apply (nodup_app_r pre); exact Hnd).
      inversion H1; assumption. }
    assert (Hsuf132 : ~ contains_132 suf).
    { apply (suffix_avoids_132 (pre ++ [n])). rewrite <- app_assoc. exact H132. }
    assert (Hlen : (length suf <= k)%nat)
      by (rewrite len_app in Hk; simpl in Hk; lia).
    destruct (IH suf Hlen Hsufnd Hsuf132) as [bs Hbs].
    exists ((pre ++ [n]) :: bs).
    apply (bf_cons (pre ++ n :: suf) (pre ++ [n]) suf bs).
    + rewrite <- app_assoc. reflexivity.
    + intro Hc. apply (app_eq_nil pre [n]) in Hc.
      destruct Hc as [_ Hc]. discriminate.
    + apply (max_last_indecomposable pre n Hpre).
      apply (nodup_pre_max pre suf n). exact Hnd.
    + exact Hdom.
    + exact Hbs.
Qed.

Theorem factor_exists : forall u,
  NoDup u -> ~ contains_132 u -> exists bs, block_factor u bs.
Proof.
  intros u Hnd H. apply (factor_exists_k (length u) u); [lia | assumption | assumption].
Qed.

Lemma prefix_compare : forall (A1 r1 A2 r2 : list nat),
  A1 ++ r1 = A2 ++ r2 ->
  (exists C, A2 = A1 ++ C) \/ (exists C, A1 = A2 ++ C).
Proof.
  induction A1 as [|a A1 IH]; intros r1 A2 r2 H; simpl in *.
  - left. exists A2. reflexivity.
  - destruct A2 as [|b A2]; simpl in *.
    + right. exists (a :: A1). reflexivity.
    + injection H as Hab H. subst b.
      destruct (IH r1 A2 r2 H) as [[C HC] | [C HC]].
      * left. exists C. simpl. rewrite HC. reflexivity.
      * right. exists C. simpl. rewrite HC. reflexivity.
Qed.

(* Disagreeing leading blocks make the longer one decomposable. *)
Theorem factor_unique : forall u bs bs',
  block_factor u bs -> block_factor u bs' -> bs = bs'.
Proof.
  intros u bs bs' H. revert bs'.
  induction H as [| u0 B rest bs Heq HBne HBind HBdom Hrest IH]; intros bs' H'.
  - symmetry. apply (factor_nil bs' H').
  - subst u0. destruct bs' as [|B' bs''].
    + exfalso.
      assert (Hc : concat (@nil (list nat)) = B ++ rest)
        by (apply factor_concat; exact H').
      simpl in Hc. symmetry in Hc.
      apply app_eq_nil in Hc. destruct Hc as [Hc _]. contradiction.
    + destruct (factor_cons_inv (B ++ rest) B' bs'' H')
        as [rest' [Heq' [HB'ne [HB'ind [HB'dom Hrest']]]]].
      assert (HBB : B = B').
      { destruct (prefix_compare B rest B' rest' Heq') as [[C HC] | [C HC]].
        - destruct C as [|c C]; [rewrite app_nil_r in HC; symmetry; exact HC|].
          exfalso. apply HB'ind. exists B, (c :: C).
          assert (Hrestc : rest = (c :: C) ++ rest').
          { rewrite HC in Heq'. rewrite <- app_assoc in Heq'.
            apply app_inv_head in Heq'. exact Heq'. }
          repeat split; [exact HC | exact HBne | discriminate |].
          intros x y Hx Hy. apply HBdom; [exact Hx|].
          rewrite Hrestc. apply in_or_app. left. exact Hy.
        - destruct C as [|c C]; [rewrite app_nil_r in HC; exact HC|].
          exfalso. apply HBind. exists B', (c :: C).
          assert (Hrestc : rest' = (c :: C) ++ rest).
          { rewrite HC in Heq'. rewrite <- app_assoc in Heq'.
            symmetry in Heq'. apply app_inv_head in Heq'. exact Heq'. }
          repeat split; [exact HC | exact HB'ne | discriminate |].
          intros x y Hx Hy. apply HB'dom; [exact Hx|].
          rewrite Hrestc. apply in_or_app. left. exact Hy. }
      subst B'.
      apply app_inv_head in Heq'. subst rest'.
      f_equal. apply IH. exact Hrest'.
Qed.

(* 1324-avoidance is decided block by block. *)
Theorem factor_avoids : forall u bs,
  block_factor u bs ->
  (~ contains_1324 u <-> Forall (fun B => ~ contains_1324 B) bs).
Proof.
  intros u bs H.
  induction H as [| u0 B rest bs Heq HBne HBind HBdom Hrest IH].
  - split; [intros _; constructor|].
    intros _ [i [j [k [l Hc]]]]. unfold has_1324_at in Hc. simpl in Hc. lia.
  - subst u0. split.
    + intro Hno.
      destruct (block_split_avoid B rest HBdom) as [Hf _].
      destruct (Hf Hno) as [HB Hrestno].
      constructor; [exact HB | apply IH; exact Hrestno].
    + intro HF.
      apply (block_split_avoid B rest HBdom).
      split; [apply (Forall_inv HF) | apply IH; apply (Forall_inv_tail HF)].
Qed.

(* Opening a value gap at v. *)

Definition bump (v x : nat) : nat := if v <=? x then S x else x.
Definition unbump (v x : nat) : nat := if v <? x then pred x else x.

Lemma bump_lt_iff : forall v x y, (bump v x < bump v y)%nat <-> (x < y)%nat.
Proof.
  intros v x y. unfold bump.
  destruct (Nat.leb_spec v x); destruct (Nat.leb_spec v y); lia.
Qed.

Lemma bump_mono : forall v x y, (x < y)%nat -> (bump v x < bump v y)%nat.
Proof. intros v x y H. apply bump_lt_iff. exact H. Qed.

Lemma bump_inj : forall v x y, bump v x = bump v y -> x = y.
Proof.
  intros v x y H. unfold bump in H.
  destruct (Nat.leb_spec v x); destruct (Nat.leb_spec v y); lia.
Qed.

Lemma bump_ne : forall v x, bump v x <> v.
Proof.
  intros v x. unfold bump. destruct (Nat.leb_spec v x); lia.
Qed.

Lemma unbump_bump : forall v x, unbump v (bump v x) = x.
Proof.
  intros v x. unfold unbump, bump.
  destruct (Nat.leb_spec v x) as [H|H].
  - destruct (Nat.ltb_spec v (S x)); lia.
  - destruct (Nat.ltb_spec v x); lia.
Qed.

(* A bumped value never equals v and lies below v exactly when it did before. *)
Lemma bump_lt_v : forall v x, (bump v x < v)%nat <-> (x < v)%nat.
Proof.
  intros v x. unfold bump. destruct (Nat.leb_spec v x); lia.
Qed.

Lemma bump_le : forall v x m, (x < m)%nat -> (v <= m)%nat -> (bump v x < S m)%nat.
Proof. intros v x m Hx Hv. unfold bump. destruct (Nat.leb_spec v x); lia. Qed.

(* Lists under a bump. *)

Lemma len_map : forall (A B : Type) (f : A -> B) (l : list A),
  length (map f l) = length l.
Proof. induction l as [|a l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma nth_map_in : forall (f : nat -> nat) u t,
  (t < length u)%nat -> nth t (map f u) 0%nat = f (nth t u 0%nat).
Proof.
  induction u as [|a u IH]; intros t Ht; simpl in *; [lia|].
  destruct t as [|t]; simpl; [reflexivity|]. apply IH. lia.
Qed.

Lemma in_map_bump : forall v u x, In x (map (bump v) u) -> exists y, In y u /\ x = bump v y.
Proof.
  induction u as [|a u IH]; intros x H; simpl in *; [contradiction|].
  destruct H as [<- | H].
  - exists a. split; [left; reflexivity | reflexivity].
  - destruct (IH x H) as [y [Hy Hx]]. exists y. split; [right; exact Hy | exact Hx].
Qed.

Lemma nodup_map_inj : forall (A B : Type) (f : A -> B) (l : list A),
  (forall x y, f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l Hinj. induction l as [|a l IH]; intro H; simpl; [constructor|].
  inversion H as [|x r Hnin Hnd Heq]; subst.
  constructor; [| apply IH; exact Hnd].
  intro Hc. apply in_map_iff in Hc. destruct Hc as [y [Hy Hin]].
  apply Hinj in Hy. subst y. contradiction.
Qed.

Lemma nodup_app_single : forall (A : list nat) v,
  NoDup A -> ~ In v A -> NoDup (A ++ [v]).
Proof.
  induction A as [|a A IH]; intros v Hnd Hnin; simpl.
  - constructor; [intros [] | constructor].
  - inversion Hnd as [|x r Hna Hnd' Heq]; subst.
    constructor.
    + intro Hc. apply in_app_or in Hc. destruct Hc as [Hc | Hc].
      * contradiction.
      * simpl in Hc. destruct Hc as [<- | []]. apply Hnin. left. reflexivity.
    + apply IH; [exact Hnd' | intro Hc; apply Hnin; right; exact Hc].
Qed.

(* Occurrence predicates are invariant under a bump. *)

Lemma has_132_map : forall v u i j k,
  has_132_at (map (bump v) u) i j k <-> has_132_at u i j k.
Proof.
  intros v u i j k. unfold has_132_at. cbv zeta. rewrite len_map.
  split; intros [Hij [Hjk [Hk [H1 H2]]]]; repeat split; try assumption.
  - rewrite (nth_map_in (bump v) u i) in H1 by lia.
    rewrite (nth_map_in (bump v) u k) in H1 by lia.
    apply bump_lt_iff in H1. exact H1.
  - rewrite (nth_map_in (bump v) u k) in H2 by lia.
    rewrite (nth_map_in (bump v) u j) in H2 by lia.
    apply bump_lt_iff in H2. exact H2.
  - rewrite (nth_map_in (bump v) u i) by lia.
    rewrite (nth_map_in (bump v) u k) by lia.
    apply bump_lt_iff. exact H1.
  - rewrite (nth_map_in (bump v) u k) by lia.
    rewrite (nth_map_in (bump v) u j) by lia.
    apply bump_lt_iff. exact H2.
Qed.

Lemma has_1324_map : forall v u i j k l,
  has_1324_at (map (bump v) u) i j k l <-> has_1324_at u i j k l.
Proof.
  intros v u i j k l. unfold has_1324_at. cbv zeta. rewrite len_map.
  split; intros [Hij [Hjk [Hkl [Hl [H1 [H2 H3]]]]]]; repeat split; try assumption.
  - rewrite (nth_map_in (bump v) u i) in H1 by lia.
    rewrite (nth_map_in (bump v) u k) in H1 by lia.
    apply bump_lt_iff in H1. exact H1.
  - rewrite (nth_map_in (bump v) u k) in H2 by lia.
    rewrite (nth_map_in (bump v) u j) in H2 by lia.
    apply bump_lt_iff in H2. exact H2.
  - rewrite (nth_map_in (bump v) u j) in H3 by lia.
    rewrite (nth_map_in (bump v) u l) in H3 by lia.
    apply bump_lt_iff in H3. exact H3.
  - rewrite (nth_map_in (bump v) u i) by lia.
    rewrite (nth_map_in (bump v) u k) by lia.
    apply bump_lt_iff. exact H1.
  - rewrite (nth_map_in (bump v) u k) by lia.
    rewrite (nth_map_in (bump v) u j) by lia.
    apply bump_lt_iff. exact H2.
  - rewrite (nth_map_in (bump v) u j) by lia.
    rewrite (nth_map_in (bump v) u l) by lia.
    apply bump_lt_iff. exact H3.
Qed.

Lemma contains_132_map : forall v u,
  contains_132 (map (bump v) u) <-> contains_132 u.
Proof.
  intros v u. split; intros [i [j [k H]]]; exists i, j, k;
    apply (has_132_map v u i j k); exact H.
Qed.

Lemma contains_1324_map : forall v u,
  contains_1324 (map (bump v) u) <-> contains_1324 u.
Proof.
  intros v u. split; intros [i [j [k [l H]]]]; exists i, j, k, l;
    apply (has_1324_map v u i j k l); exact H.
Qed.

(* The renormalising append ext u v. *)

Definition ext (u : list nat) (v : nat) : list nat := map (bump v) u ++ [v].

Lemma ext_length : forall u v, length (ext u v) = S (length u).
Proof. intros u v. unfold ext. rewrite len_app, len_map. simpl. lia. Qed.

(* Renormalising does not change 1324-status. *)
Theorem ext_iff_append : forall u v,
  contains_1324 (ext u v) <-> contains_1324 (u ++ [v]).
Proof.
  intros u v. unfold ext.
  rewrite (append_1324 (map (bump v) u) v), (append_1324 u v).
  split; intros [H | [i [j [k [H132 Hlt]]]]].
  - left. apply (contains_1324_map v u). exact H.
  - right. exists i, j, k.
    assert (Hj : (j < length u)%nat).
    { unfold has_132_at in H132. rewrite len_map in H132.
      destruct H132 as [_ [Hjk [Hk _]]]. lia. }
    rewrite (nth_map_in (bump v) u j Hj) in Hlt.
    split; [apply (has_132_map v u i j k); exact H132 |].
    apply (bump_lt_v v (nth j u 0%nat)). exact Hlt.
  - left. apply (contains_1324_map v u). exact H.
  - right. exists i, j, k.
    assert (Hj : (j < length u)%nat).
    { unfold has_132_at in H132. destruct H132 as [_ [Hjk [Hk _]]]. lia. }
    rewrite (nth_map_in (bump v) u j Hj).
    split; [apply (has_132_map v u i j k); exact H132 |].
    apply (bump_lt_v v (nth j u 0%nat)). exact Hlt.
Qed.

(* Legality for ext coincides with legality for a raw append. *)
Corollary ext_legal_iff : forall u v,
  ~ contains_1324 (ext u v) <-> legal u v.
Proof.
  intros u v. unfold legal. split; intros H C; apply H;
    apply ext_iff_append; exact C.
Qed.

(* The branching bound transfers to ext. *)
Corollary ext_legal_iff_le_mu : forall u m,
  ~ contains_1324 u -> is_mu u m ->
  forall v, ~ contains_1324 (ext u v) <-> (v <= m)%nat.
Proof.
  intros u m Hu Hmu v.
  rewrite ext_legal_iff. apply (legal_iff_le_mu u m Hu Hmu).
Qed.

Corollary ext_all_legal_when_132_free : forall u,
  ~ contains_132 u -> forall v, ~ contains_1324 (ext u v).
Proof.
  intros u H v. apply ext_legal_iff. apply legal_all_when_132_free. exact H.
Qed.

(* ext carries a permutation of [0,m) to a permutation of [0,m]. *)

Definition is_perm (u : list nat) (m : nat) : Prop :=
  length u = m /\ NoDup u /\ forall x, In x u -> (x < m)%nat.

(* The projections of is_perm, and the hint database from which the structural
   side conditions of the proofs below are discharged. *)

Lemma perm_len : forall u m, is_perm u m -> length u = m.
Proof. intros u m [H _]. exact H. Qed.

Lemma perm_nodup : forall u m, is_perm u m -> NoDup u.
Proof. intros u m [_ [H _]]. exact H. Qed.

Lemma perm_bound : forall u m, is_perm u m -> forall x, In x u -> (x < m)%nat.
Proof. intros u m [_ [_ H]]. exact H. Qed.

Create HintDb av1324.
#[export] Hint Resolve perm_len perm_nodup perm_bound : av1324.

(* enumerator membership, the shape of a permutation, duplicate-freeness *)
Ltac av := eauto with av1324.

Lemma ext_not_in : forall u v, ~ In v (map (bump v) u).
Proof.
  intros u v H. destruct (in_map_bump v u v H) as [y [_ Hy]].
  symmetry in Hy. exact (bump_ne v y Hy).
Qed.

Theorem ext_perm : forall u m v,
  is_perm u m -> (v <= m)%nat -> is_perm (ext u v) (S m).
Proof.
  intros u m v [Hlen [Hnd Hb]] Hv. unfold ext. repeat split.
  - rewrite len_app, len_map. simpl. lia.
  - apply nodup_app_single.
    + apply nodup_map_inj; [apply bump_inj | exact Hnd].
    + apply ext_not_in.
  - intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx | Hx].
    + destruct (in_map_bump v u x Hx) as [y [Hy Hxy]]. subst x.
      apply bump_le; [apply Hb; exact Hy | lia].
    + simpl in Hx. destruct Hx as [<- | []]. lia.
Qed.

(* Inverting a bump on values that avoid the gap. *)

Lemma bump_unbump : forall v x, x <> v -> bump v (unbump v x) = x.
Proof.
  intros v x Hne. unfold bump, unbump.
  destruct (Nat.ltb_spec v x) as [H|H].
  - destruct (Nat.leb_spec v (pred x)); lia.
  - destruct (Nat.leb_spec v x); lia.
Qed.

Lemma map_bump_unbump : forall v A,
  ~ In v A -> map (bump v) (map (unbump v) A) = A.
Proof.
  induction A as [|a A IH]; intro H; simpl; [reflexivity|].
  rewrite bump_unbump by (intro Hc; apply H; left; exact Hc).
  rewrite IH by (intro Hc; apply H; right; exact Hc). reflexivity.
Qed.

Lemma map_inj : forall (f : nat -> nat) l l',
  (forall x y, f x = f y -> x = y) -> map f l = map f l' -> l = l'.
Proof.
  intros f l. induction l as [|a l IH]; intros l' Hinj H; destruct l' as [|b l'];
    simpl in H; try discriminate; [reflexivity|].
  injection H as Hab Hl. apply Hinj in Hab. subst b.
  f_equal. apply IH; assumption.
Qed.

Lemma nodup_map_rev : forall (f : nat -> nat) l, NoDup (map f l) -> NoDup l.
Proof.
  induction l as [|a l IH]; intro H; simpl in *; [constructor|].
  inversion H as [|x r Hnin Hnd Heq]; subst.
  constructor; [| apply IH; exact Hnd].
  intro Hc. apply Hnin. apply in_map. exact Hc.
Qed.

(* Every repetition-free nonempty word is an ext. *)

Theorem ext_surj_split : forall A v,
  ~ In v A -> A ++ [v] = ext (map (unbump v) A) v.
Proof.
  intros A v H. unfold ext. rewrite map_bump_unbump by exact H. reflexivity.
Qed.

Theorem ext_surj : forall w,
  w <> [] -> NoDup w ->
  exists u v, w = ext u v /\ length u = pred (length w).
Proof.
  intros w Hne Hnd.
  destruct (exists_last Hne) as [A [v Hw]].
  assert (HnA : ~ In v A).
  { intro Hc. rewrite Hw in Hnd.
    apply (nodup_app_disjoint A [v] v Hnd Hc). left. reflexivity. }
  exists (map (unbump v) A), v. split.
  - rewrite Hw. apply ext_surj_split. exact HnA.
  - rewrite Hw, len_app, len_map. simpl. lia.
Qed.

(* ext is injective in both arguments. *)

Theorem ext_inj : forall u u' v v',
  ext u v = ext u' v' -> u = u' /\ v = v'.
Proof.
  intros u u' v v' H. unfold ext in H.
  apply app_inj_tail in H. destruct H as [Hm Hv]. subst v'.
  split; [| reflexivity].
  apply (map_inj (bump v)); [apply bump_inj | exact Hm].
Qed.

(* Deleting the last letter returns a permutation one size down. *)

Lemma perm_last_le : forall A v m, is_perm (A ++ [v]) (S m) -> (v <= m)%nat.
Proof.
  intros A v m [_ [_ Hb]].
  assert (Hin : In v (A ++ [v])) by (apply in_or_app; right; left; reflexivity).
  specialize (Hb v Hin). lia.
Qed.

Theorem shrink_perm : forall A v m,
  is_perm (A ++ [v]) (S m) -> is_perm (map (unbump v) A) m.
Proof.
  intros A v m Hp.
  assert (Hvm : (v <= m)%nat) by (apply (perm_last_le A v m); exact Hp).
  destruct Hp as [Hlen [Hnd Hb]].
  assert (HnA : ~ In v A).
  { intro Hc. apply (nodup_app_disjoint A [v] v Hnd Hc). left. reflexivity. }
  assert (HA : map (bump v) (map (unbump v) A) = A)
    by (apply map_bump_unbump; exact HnA).
  rewrite len_app in Hlen. simpl in Hlen.
  repeat split.
  - rewrite len_map. lia.
  - apply (nodup_map_rev (bump v)). rewrite HA.
    apply (nodup_app_r [] A). simpl.
    (* NoDup A from NoDup (A ++ [v]) *)
    clear -Hnd. induction A as [|a A IH]; [constructor|].
    inversion Hnd as [|x r Hnin Hnd' Heq]; subst.
    constructor; [intro Hc; apply Hnin; apply in_or_app; left; exact Hc
                 | apply IH; exact Hnd'].
  - intros x Hx.
    assert (Hbx : In (bump v x) A).
    { rewrite <- HA. apply in_map. exact Hx. }
    assert (Hlt : (bump v x < S m)%nat)
      by (apply Hb; apply in_or_app; left; exact Hbx).
    unfold bump in Hlt. destruct (Nat.leb_spec v x); lia.
Qed.

(* Each 1324-avoider of [0,m] is ext u v for a unique legal pair. *)

(* The correspondence with its uniqueness and legality clauses. *)
Theorem ext_bijection : forall w m,
  is_perm w (S m) ->
  exists u v,
    w = ext u v /\ is_perm u m /\ (v <= m)%nat /\
    (~ contains_1324 w <-> (~ contains_1324 u /\ legal u v)) /\
    (forall u' v', w = ext u' v' -> u' = u /\ v' = v).
Proof.
  intros w m Hp.
  assert (Hne : w <> []).
  { destruct Hp as [Hlen _]. intro Hc. subst w. simpl in Hlen. lia. }
  destruct (exists_last Hne) as [A [v Hw]].
  subst w.
  assert (HnA : ~ In v A).
  { destruct Hp as [_ [Hnd _]].
    intro Hc. apply (nodup_app_disjoint A [v] v Hnd Hc). left. reflexivity. }
  assert (Hvm : (v <= m)%nat) by (apply (perm_last_le A v m); exact Hp).
  assert (Hext : A ++ [v] = ext (map (unbump v) A) v)
    by (apply ext_surj_split; exact HnA).
  exists (map (unbump v) A), v.
  split; [exact Hext |].
  split; [apply (shrink_perm A v m); exact Hp |].
  split; [exact Hvm |].
  split.
  - split.
    + intro H. rewrite Hext in H. split.
      * intro C. apply H. apply ext_iff_append. apply append_1324. left. exact C.
      * apply ext_legal_iff. exact H.
    + intros [_ H2]. rewrite Hext. apply ext_legal_iff. exact H2.
  - intros u' v' Heq. rewrite Hext in Heq.
    symmetry in Heq. apply ext_inj in Heq. destruct Heq as [Hu Hv].
    split; [exact Hu | exact Hv].
Qed.

(* 1324-containment is decidable, transparently enough for legalb to compute. *)

Lemma has_1324_at_dec : forall u i j k l,
  {has_1324_at u i j k l} + {~ has_1324_at u i j k l}.
Proof.
  intros u i j k l. unfold has_1324_at. cbv zeta.
  destruct (lt_dec i j) as [H1|H1]; [|right; tauto].
  destruct (lt_dec j k) as [H2|H2]; [|right; tauto].
  destruct (lt_dec k l) as [H3|H3]; [|right; tauto].
  destruct (lt_dec l (length u)) as [H4|H4]; [|right; tauto].
  destruct (lt_dec (nth i u 0%nat) (nth k u 0%nat)) as [H5|H5]; [|right; tauto].
  destruct (lt_dec (nth k u 0%nat) (nth j u 0%nat)) as [H6|H6]; [|right; tauto].
  destruct (lt_dec (nth j u 0%nat) (nth l u 0%nat)) as [H7|H7]; [|right; tauto].
  left. repeat split; assumption.
Defined.

Lemma contains_1324_dec : forall u, {contains_1324 u} + {~ contains_1324 u}.
Proof.
  intro u.
  assert (Hd : {exists i, (i < length u)%nat /\
                 exists j, (j < length u)%nat /\
                 exists k, (k < length u)%nat /\
                 exists l, (l < length u)%nat /\ has_1324_at u i j k l}
             + {~ exists i, (i < length u)%nat /\
                 exists j, (j < length u)%nat /\
                 exists k, (k < length u)%nat /\
                 exists l, (l < length u)%nat /\ has_1324_at u i j k l}).
  { apply bounded_ex_dec. intro i.
    apply bounded_ex_dec. intro j.
    apply bounded_ex_dec. intro k.
    apply bounded_ex_dec. intro l.
    apply has_1324_at_dec. }
  destruct Hd as [H | H].
  - left. destruct H as [i [_ [j [_ [k [_ [l [_ H1324]]]]]]]].
    exists i, j, k, l. exact H1324.
  - right. intros [i [j [k [l H1324]]]].
    apply H. assert (Hc := H1324). unfold has_1324_at in Hc.
    destruct Hc as [Hij [Hjk [Hkl [Hl _]]]].
    exists i. split; [lia|]. exists j. split; [lia|].
    exists k. split; [lia|]. exists l. split; [lia | exact H1324].
Defined.

Definition legalb (u : list nat) (y : nat) : bool :=
  if contains_1324_dec (u ++ [y]) then false else true.

Lemma legalb_spec : forall u y, legalb u y = true <-> legal u y.
Proof.
  intros u y. unfold legalb, legal.
  destruct (contains_1324_dec (u ++ [y])) as [H | H].
  - split; [intro Hc; discriminate | intro Hc; contradiction].
  - split; [intros _; exact H | intros _; reflexivity].
Qed.

(* Sequence, filter and flat_map arithmetic. *)

Lemma seq_snoc : forall n s, seq s (S n) = seq s n ++ [(s + n)%nat].
Proof.
  induction n as [|n IH]; intro s.
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - replace (seq s (S (S n))) with (s :: seq (S s) (S n)) by reflexivity.
    replace (seq s (S n)) with (s :: seq (S s) n) by reflexivity.
    rewrite (IH (S s)).
    replace (S s + n)%nat with (s + S n)%nat by lia.
    reflexivity.
Qed.

Lemma filter_app_l : forall (P : nat -> bool) A B,
  filter P (A ++ B) = filter P A ++ filter P B.
Proof.
  induction A as [|a A IH]; intro B; simpl; [reflexivity|].
  destruct (P a); simpl; rewrite IH; reflexivity.
Qed.

(* len_app is at list nat; flat_map needs it one type up. *)
Lemma len_app_gen : forall (A : Type) (l1 l2 : list A),
  length (l1 ++ l2) = (length l1 + length l2)%nat.
Proof.
  induction l1 as [|a l1 IH]; intro l2; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma filter_all : forall (P : nat -> bool) l,
  (forall y, In y l -> P y = true) -> filter P l = l.
Proof.
  induction l as [|a l IH]; intro H; simpl; [reflexivity|].
  rewrite (H a (or_introl eq_refl)).
  f_equal. apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma fold_right_pointwise : forall (f g : list nat -> nat -> nat) l,
  (forall x a, f x a = g x a) -> fold_right f 0%nat l = fold_right g 0%nat l.
Proof.
  intros f g l H. induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite H, IH. reflexivity.
Qed.

Lemma nodup_app_both : forall (A B : list (list nat)),
  NoDup A -> NoDup B -> (forall a, In a A -> In a B -> False) -> NoDup (A ++ B).
Proof.
  induction A as [|a A IH]; intros B HA HB Hdis; simpl; [exact HB|].
  inversion HA as [|x r Hnin HA' Heq]; subst.
  constructor.
  - intro Hc. apply in_app_or in Hc. destruct Hc as [Hc | Hc].
    + contradiction.
    + apply (Hdis a); [left; reflexivity | exact Hc].
  - apply IH; [exact HA' | exact HB |].
    intros z Hz Hz'. apply (Hdis z); [right; exact Hz | exact Hz'].
Qed.

Lemma nodup_flat_map : forall (f : list nat -> list (list nat)) l,
  NoDup l ->
  (forall x, In x l -> NoDup (f x)) ->
  (forall x y a, In x l -> In y l -> In a (f x) -> In a (f y) -> x = y) ->
  NoDup (flat_map f l).
Proof.
  induction l as [|x l IH]; intros Hnd Hin Hdisj; simpl; [constructor|].
  inversion Hnd as [|z r Hnx Hnd' Heq]; subst.
  apply nodup_app_both.
  - apply Hin. left. reflexivity.
  - apply IH; [exact Hnd' | intros y Hy; apply Hin; right; exact Hy |].
    intros y z a Hy Hz Ha Ha'.
    apply (Hdisj y z a); [right; exact Hy | right; exact Hz | exact Ha | exact Ha'].
  - intros a Ha Ha'. apply in_flat_map in Ha'. destruct Ha' as [y [Hy Hay]].
    assert (Hxy : x = y)
      by (apply (Hdisj x y a); [left; reflexivity | right; exact Hy | exact Ha | exact Hay]).
    subst y. contradiction.
Qed.

Lemma length_flat_map : forall (f : list nat -> list (list nat)) l,
  length (flat_map f l) = fold_right (fun x acc => (length (f x) + acc)%nat) 0%nat l.
Proof.
  induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite len_app_gen, IH. reflexivity.
Qed.

Lemma length_filter_seq : forall (P : nat -> bool) N K,
  (forall y, P y = true <-> (y <= K)%nat) ->
  length (filter P (seq 0 N)) = Nat.min N (S K).
Proof.
  intros P N K HP. induction N as [|N IH].
  - reflexivity.
  - rewrite seq_snoc, filter_app_l, len_app, IH, Nat.add_0_l.
    destruct (P N) eqn:E.
    + assert (HN : (N <= K)%nat) by (apply HP; exact E).
      replace (length (filter P [N])) with 1%nat
        by (simpl; rewrite E; reflexivity).
      lia.
    + assert (HN : ~ (N <= K)%nat).
      { intro Hc. assert (Hc2 : P N = true) by (apply HP; exact Hc).
        rewrite E in Hc2. discriminate. }
      replace (length (filter P [N])) with 0%nat
        by (simpl; rewrite E; reflexivity).
      lia.
Qed.

(* gen m lists the 1324-avoiding permutations of [0,m) without repetition. *)

Fixpoint gen (m : nat) : list (list nat) :=
  match m with
  | 0 => [[]]
  | S m' => flat_map (fun u => map (ext u) (filter (legalb u) (seq 0 (S m')))) (gen m')
  end.

(* gen (S m) unfolded once; simpl would reduce the filter past filter_In. *)
Lemma gen_S : forall m,
  gen (S m) =
  flat_map (fun u => map (ext u) (filter (legalb u) (seq 0 (S m)))) (gen m).
Proof. intro m. reflexivity. Qed.

Lemma nil_avoids_1324 : ~ contains_1324 [].
Proof. intros [i [j [k [l H]]]]. unfold has_1324_at in H. simpl in H. lia. Qed.

Lemma perm_nil : is_perm [] 0.
Proof. repeat split; [constructor | intros x []]. Qed.

Theorem gen_sound : forall m w,
  In w (gen m) -> is_perm w m /\ ~ contains_1324 w.
Proof.
  induction m as [|m IH]; intros w Hw.
  - simpl in Hw. destruct Hw as [<- | []].
    split; [apply perm_nil | apply nil_avoids_1324].
  - rewrite gen_S in Hw.
    apply in_flat_map in Hw. destruct Hw as [u [Hu Hw]].
    apply in_map_iff in Hw. destruct Hw as [v [Hv Hvin]].
    apply filter_In in Hvin. destruct Hvin as [Hseq Hleg].
    apply in_seq in Hseq.
    destruct (IH u Hu) as [Hpu Hau]. subst w.
    split.
    + apply ext_perm; [exact Hpu | lia].
    + apply ext_legal_iff. apply legalb_spec. exact Hleg.
Qed.

Theorem gen_complete : forall m w,
  is_perm w m -> ~ contains_1324 w -> In w (gen m).
Proof.
  induction m as [|m IH]; intros w Hp Hav.
  - simpl. destruct Hp as [Hlen _]. destruct w as [|a w]; [left; reflexivity|].
    simpl in Hlen. discriminate.
  - rewrite gen_S.
    destruct (ext_bijection w m Hp) as [u [v [Hw [Hpu [Hvm [Hiff _]]]]]].
    destruct (proj1 Hiff Hav) as [Hau Hleg].
    apply in_flat_map. exists u. split.
    + apply IH; [exact Hpu | exact Hau].
    + apply in_map_iff. exists v. split; [symmetry; exact Hw|].
      apply filter_In. split.
      * apply in_seq. lia.
      * apply legalb_spec. exact Hleg.
Qed.

Corollary gen_spec : forall m w,
  In w (gen m) <-> (is_perm w m /\ ~ contains_1324 w).
Proof.
  intros m w. split.
  - apply gen_sound.
  - intros [H1 H2]. apply gen_complete; assumption.
Qed.

Theorem gen_nodup : forall m, NoDup (gen m).
Proof.
  induction m as [|m IH].
  - simpl. constructor; [intros [] | constructor].
  - rewrite gen_S. apply nodup_flat_map; [exact IH | |].
    + intros u Hu. apply nodup_map_inj.
      * intros a b Hab. apply ext_inj in Hab. destruct Hab as [_ Hv]. exact Hv.
      * apply NoDup_filter. apply seq_NoDup.
    + intros u u' w Hu Hu' Hw Hw'.
      apply in_map_iff in Hw. destruct Hw as [v [Hv _]].
      apply in_map_iff in Hw'. destruct Hw' as [v' [Hv' _]].
      rewrite <- Hv in Hv'. apply ext_inj in Hv'.
      destruct Hv' as [Hu2 _]. symmetry. exact Hu2.
Qed.

Lemma gen_perm : forall m w, In w (gen m) -> is_perm w m.
Proof. intros m w H. exact (proj1 (gen_sound m w H)). Qed.

Lemma gen_av : forall m w, In w (gen m) -> ~ contains_1324 w.
Proof. intros m w H. exact (proj2 (gen_sound m w H)). Qed.

#[export] Hint Resolve gen_perm gen_av gen_nodup : av1324.

(* card m is the cardinality of the class, with its branching recurrence. *)

Definition card (m : nat) : nat := length (gen m).

(* card counts the class: no repetitions, exactly the right members. *)
Theorem card_is_cardinality : forall m,
  NoDup (gen m) /\ forall w, In w (gen m) <-> (is_perm w m /\ ~ contains_1324 w).
Proof.
  intro m. split; [apply gen_nodup | apply gen_spec].
Qed.

(* The fibre over u has mu(u)+1 members, capped at the alphabet. *)
Theorem fibre_count : forall u m d,
  ~ contains_1324 u -> is_mu u d ->
  length (filter (legalb u) (seq 0 (S m))) = S (Nat.min d m).
Proof.
  intros u m d Hu Hmu.
  rewrite (length_filter_seq (legalb u) (S m) d).
  - lia.
  - intro y. rewrite legalb_spec. apply (legal_iff_le_mu u d Hu Hmu).
Qed.

(* A 132-free word admits every letter. *)
Theorem fibre_count_free : forall u m,
  ~ contains_132 u -> length (filter (legalb u) (seq 0 (S m))) = S m.
Proof.
  intros u m H.
  rewrite (filter_all (legalb u) (seq 0 (S m))).
  - apply length_seq.
  - intros y _. apply legalb_spec. apply legal_all_when_132_free. exact H.
Qed.

(* The branching recurrence. *)
Theorem card_succ : forall m,
  card (S m) =
  fold_right (fun u acc =>
     (length (filter (legalb u) (seq 0 (S m))) + acc)%nat) 0%nat (gen m).
Proof.
  intro m. unfold card. rewrite gen_S, length_flat_map.
  apply fold_right_pointwise. intros x a.
  rewrite len_map. reflexivity.
Qed.

(* A first letter serves only as the '1', so it forbids a 213 above itself. *)

Definition has_213_at (u : list nat) (p q r : nat) : Prop :=
  (p < q)%nat /\ (q < r)%nat /\ (r < length u)%nat /\
  let vp := nth p u 0%nat in
  let vq := nth q u 0%nat in
  let vr := nth r u 0%nat in
  (vq < vp)%nat /\ (vp < vr)%nat.

Definition contains_213 (u : list nat) : Prop :=
  exists p q r, has_213_at u p q r.

(* The last three entries of a 1324 occurrence form a 213. *)
Lemma pattern_1324_contains_213 : forall p i j k l,
  has_1324_at p i j k l -> has_213_at p j k l.
Proof.
  intros p i j k l H. unfold has_1324_at in H. unfold has_213_at.
  destruct H as [Hij [Hjk [Hkl [Hlen [Hik [Hkj Hjl]]]]]].
  repeat split; try lia; assumption.
Qed.

Lemma sub_1324_213 : forall p, contains_1324 p -> contains_213 p.
Proof.
  intros p [i [j [k [l H]]]]. exists j, k, l.
  apply (pattern_1324_contains_213 p i j k l). exact H.
Qed.

(* A 213 all of whose entries lie above j. *)
Definition has_213_above (u : list nat) (j p q r : nat) : Prop :=
  has_213_at u p q r /\ (j < nth q u 0%nat)%nat.

Lemma above_is_213 : forall u j p q r,
  has_213_above u j p q r -> has_213_at u p q r.
Proof. intros u j p q r [H _]. exact H. Qed.

(* All three entries of such a pattern exceed j. *)
Lemma above_all_gt : forall u j p q r,
  has_213_above u j p q r ->
  (j < nth p u 0%nat)%nat /\ (j < nth q u 0%nat)%nat /\ (j < nth r u 0%nat)%nat.
Proof.
  intros u j p q r [[_ [_ [_ [Hqp Hpr]]]] Hj]. repeat split; lia.
Qed.

(* The rule for a first letter. *)
Theorem cons_1324 : forall j u,
  contains_1324 (j :: u) <->
  (contains_1324 u \/ exists p q r, has_213_above u j p q r).
Proof.
  intros j u. split.
  - intros [i [a [b [c H]]]]. unfold has_1324_at in H.
    destruct H as [Hia [Hab [Hbc [Hc [H1 [H2 H3]]]]]].
    simpl in Hc.
    destruct i as [|i].
    + (* j is the '1' of the occurrence *)
      right.
      destruct a as [|a]; [lia|]. destruct b as [|b]; [lia|].
      destruct c as [|c]; [lia|].
      simpl in H1, H2, H3.
      exists a, b, c. split.
      * unfold has_213_at. repeat split; try lia.
      * exact H1.
    + (* the occurrence misses the head *)
      left.
      destruct a as [|a]; [lia|]. destruct b as [|b]; [lia|].
      destruct c as [|c]; [lia|].
      simpl in H1, H2, H3.
      exists i, a, b, c. unfold has_1324_at.
      repeat split; try lia; assumption.
  - intros [H | [p [q [r [H213 Hj]]]]].
    + destruct H as [i [a [b [c H]]]]. unfold has_1324_at in H.
      destruct H as [Hia [Hab [Hbc [Hc [H1 [H2 H3]]]]]].
      exists (S i), (S a), (S b), (S c). unfold has_1324_at.
      simpl. repeat split; try lia; assumption.
    + unfold has_213_at in H213.
      destruct H213 as [Hpq [Hqr [Hr [Hqp Hpr]]]].
      exists 0%nat, (S p), (S q), (S r). unfold has_1324_at.
      simpl. repeat split; try lia; assumption.
Qed.

Corollary cons_1324_avoid : forall j u,
  ~ contains_1324 (j :: u) <->
  (~ contains_1324 u /\ forall p q r, ~ has_213_above u j p q r).
Proof.
  intros j u. split.
  - intro H. split.
    + intro C. apply H. apply cons_1324. left. exact C.
    + intros p q r C. apply H. apply cons_1324. right. exists p, q, r. exact C.
  - intros [H1 H2] C. apply cons_1324 in C. destruct C as [C | [p [q [r C]]]].
    + apply H1; exact C.
    + apply (H2 p q r); exact C.
Qed.

(* Subsequences carry a value-preserving increasing index map. *)

Inductive subseq : list nat -> list nat -> Prop :=
| ss_nil  : forall l, subseq [] l
| ss_skip : forall x v l, subseq v l -> subseq v (x :: l)
| ss_keep : forall x v l, subseq v l -> subseq (x :: v) (x :: l).

(* The index map itself. *)
Theorem subseq_index : forall v u, subseq v u ->
  exists f,
    (forall a b, (a < b)%nat -> (b < length v)%nat -> (f a < f b)%nat) /\
    (forall a, (a < length v)%nat ->
       (f a < length u)%nat /\ nth a v 0%nat = nth (f a) u 0%nat).
Proof.
  intros v u H. induction H as [l | x v l H IH | x v l H IH].
  - exists (fun _ => 0%nat). split.
    + intros a b _ Hb. simpl in Hb. lia.
    + intros a Ha. simpl in Ha. lia.
  - destruct IH as [f [Hmono Hval]].
    exists (fun a => S (f a)). split.
    + intros a b Hab Hb. simpl.
      assert (H' : (f a < f b)%nat) by (apply Hmono; assumption). lia.
    + intros a Ha. destruct (Hval a Ha) as [Hlt Hnth].
      split; [simpl; lia | simpl; exact Hnth].
  - destruct IH as [f [Hmono Hval]].
    exists (fun a => match a with O => O | S a' => S (f a') end). split.
    + intros a b Hab Hb. simpl in Hb.
      destruct a as [|a]; destruct b as [|b]; simpl; try lia.
      assert (H' : (f a < f b)%nat) by (apply Hmono; lia). lia.
    + intros a Ha. simpl in Ha.
      destruct a as [|a].
      * split; [simpl; lia | reflexivity].
      * destruct (Hval a ltac:(lia)) as [Hlt Hnth].
        split; [simpl; lia | simpl; exact Hnth].
Qed.

Theorem subseq_213 : forall v u,
  subseq v u -> contains_213 v -> contains_213 u.
Proof.
  intros v u Hss [p [q [r H]]].
  destruct (subseq_index v u Hss) as [f [Hmono Hval]].
  unfold has_213_at in H. destruct H as [Hpq [Hqr [Hr [Hqp Hpr]]]].
  destruct (Hval p ltac:(lia)) as [Hfp Ep].
  destruct (Hval q ltac:(lia)) as [Hfq Eq].
  destruct (Hval r Hr) as [Hfr Er].
  exists (f p), (f q), (f r). unfold has_213_at.
  rewrite <- Ep, <- Eq, <- Er.
  repeat split; try assumption.
  - apply Hmono; lia.
  - apply Hmono; lia.
Qed.

Lemma filter_subseq : forall (P : nat -> bool) u, subseq (filter P u) u.
Proof.
  intros P u. induction u as [|x u IH]; simpl; [constructor|].
  destruct (P x); [apply ss_keep | apply ss_skip]; exact IH.
Qed.

(* The obstruction as a statement about the subword of entries exceeding j. *)

Definition above (j : nat) (u : list nat) : list nat :=
  filter (fun x => j <? x) u.

Lemma above_gt : forall j u x, In x (above j u) -> (j < x)%nat.
Proof.
  intros j u x H. unfold above in H. apply filter_In in H.
  destruct H as [_ Hb]. apply Nat.ltb_lt. exact Hb.
Qed.

(* One direction is transport along the subsequence. *)
Theorem above_213_gives_above : forall j u,
  contains_213 (above j u) -> exists p q r, has_213_above u j p q r.
Proof.
  intros j u H.
  assert (Hgt : forall p q r, has_213_at (above j u) p q r ->
                 (j < nth q (above j u) 0%nat)%nat).
  { intros p' q' r' [_ [Hq'r' [Hr' _]]].
    apply above_gt with (u := u). apply nth_in. lia. }
  destruct H as [p [q [r Hpat]]].
  assert (Hj := Hgt p q r Hpat).
  destruct (subseq_index (above j u) u (filter_subseq _ u)) as [f [Hmono Hval]].
  unfold has_213_at in Hpat. destruct Hpat as [Hpq [Hqr [Hr [Hqp Hpr]]]].
  destruct (Hval p ltac:(lia)) as [Hfp Ep].
  destruct (Hval q ltac:(lia)) as [Hfq Eq].
  destruct (Hval r Hr) as [Hfr Er].
  exists (f p), (f q), (f r). split.
  - unfold has_213_at. rewrite <- Ep, <- Eq, <- Er.
    repeat split; try assumption; [apply Hmono; lia | apply Hmono; lia].
  - rewrite <- Eq. exact Hj.
Qed.

(* rank P u a counts the kept entries strictly before position a. *)
Definition rank (P : nat -> bool) (u : list nat) (a : nat) : nat :=
  length (filter P (firstn a u)).

Lemma filter_cons : forall (P : nat -> bool) x u,
  filter P (x :: u) = (if P x then x :: filter P u else filter P u).
Proof. intros P x u. reflexivity. Qed.

Lemma rank_nil : forall P a, rank P [] a = 0%nat.
Proof. intros P a. unfold rank. destruct a; reflexivity. Qed.

Lemma rank_0 : forall P u, rank P u 0 = 0%nat.
Proof. intros P u. unfold rank. destruct u; reflexivity. Qed.

Lemma rank_cons : forall P x u a,
  rank P (x :: u) (S a) = (if P x then S (rank P u a) else rank P u a).
Proof.
  intros P x u a. unfold rank. simpl. destruct (P x); simpl; reflexivity.
Qed.

(* Opaque: simpl would unfold firstn (S a) u into a match on u. *)
Opaque rank.

Lemma rank_spec : forall (P : nat -> bool) u a,
  (a < length u)%nat -> P (nth a u 0%nat) = true ->
  (rank P u a < length (filter P u))%nat /\
  nth (rank P u a) (filter P u) 0%nat = nth a u 0%nat.
Proof.
  intros P u. induction u as [|x u IH]; intros a Ha HP; simpl in Ha; [lia|].
  rewrite filter_cons.
  destruct a as [|a].
  - simpl in HP. rewrite rank_0, HP. split; [simpl; lia | reflexivity].
  - simpl in HP. destruct (IH a ltac:(lia) HP) as [H1 H2].
    rewrite rank_cons. destruct (P x).
    + split; [simpl; lia | simpl; exact H2].
    + split; [exact H1 | exact H2].
Qed.

Lemma rank_le : forall (P : nat -> bool) u a b,
  (a <= b)%nat -> (rank P u a <= rank P u b)%nat.
Proof.
  intros P u. induction u as [|x u IH]; intros a b Hab.
  - rewrite !rank_nil. lia.
  - destruct a as [|a]; destruct b as [|b].
    + lia.
    + rewrite rank_0. lia.
    + lia.
    + rewrite !rank_cons. assert (H := IH a b ltac:(lia)).
      destruct (P x); lia.
Qed.

Lemma rank_step : forall (P : nat -> bool) u a,
  (a < length u)%nat -> P (nth a u 0%nat) = true ->
  (rank P u a < rank P u (S a))%nat.
Proof.
  intros P u. induction u as [|x u IH]; intros a Ha HP; simpl in Ha; [lia|].
  destruct a as [|a].
  - simpl in HP. rewrite rank_0, rank_cons, rank_0, HP. lia.
  - simpl in HP. assert (H := IH a ltac:(lia) HP).
    rewrite !rank_cons. destruct (P x); lia.
Qed.

Lemma rank_mono : forall (P : nat -> bool) u a b,
  (a < b)%nat -> (b < length u)%nat -> P (nth a u 0%nat) = true ->
  (rank P u a < rank P u b)%nat.
Proof.
  intros P u a b Hab Hb HP.
  assert (H1 : (rank P u a < rank P u (S a))%nat)
    by (apply rank_step; [lia | exact HP]).
  assert (H2 : (rank P u (S a) <= rank P u b)%nat) by (apply rank_le; lia).
  lia.
Qed.

(* Rank transport.  A position kept by a boolean test moves to its rank in the
   filtered word with its value and its order intact, so an occurrence all of
   whose points are kept is an occurrence of the filtered word.  Every value cut
   below is an instance of one of the three transports. *)

Definition keeps (P : nat -> bool) (w : list nat) (p : nat) : Prop :=
  (p < length w)%nat /\ P (nth p w 0%nat) = true.

(* the two side conditions of keeps, from a length bound and a value bound *)
Ltac keep :=
  split; [ lia
         | cbn beta; first [ apply Nat.ltb_lt | apply Nat.leb_le ]; lia ].

(* case-split every boolean comparison in sight, then decide by arithmetic *)
Ltac natb :=
  repeat match goal with
         | [ |- context [Nat.leb ?a ?b] ] => destruct (Nat.leb_spec a b)
         | [ |- context [Nat.ltb ?a ?b] ] => destruct (Nat.ltb_spec a b)
         | [ _ : context [Nat.leb ?a ?b] |- _ ] => destruct (Nat.leb_spec a b)
         | [ _ : context [Nat.ltb ?a ?b] |- _ ] => destruct (Nat.ltb_spec a b)
         end;
  solve [ reflexivity | discriminate | exfalso; lia | lia | congruence ].

Lemma rank_val : forall P w p, keeps P w p ->
  nth (rank P w p) (filter P w) 0%nat = nth p w 0%nat.
Proof. intros P w p [H1 H2]. exact (proj2 (rank_spec P w p H1 H2)). Qed.

Lemma rank_bound : forall P w p, keeps P w p ->
  (rank P w p < length (filter P w))%nat.
Proof. intros P w p [H1 H2]. exact (proj1 (rank_spec P w p H1 H2)). Qed.

Lemma rank_ord : forall P w p q, (p < q)%nat -> keeps P w p -> keeps P w q ->
  (rank P w p < rank P w q)%nat.
Proof. intros P w p q Hpq [H1 H2] [H3 _]. apply rank_mono; assumption. Qed.

Theorem filter_132 : forall P w i j k,
  keeps P w i -> keeps P w j -> keeps P w k ->
  has_132_at w i j k -> contains_132 (filter P w).
Proof.
  intros P w i j k Ki Kj Kk H.
  destruct H as [Hij [Hjk [Hk [H1 H2]]]].
  exists (rank P w i), (rank P w j), (rank P w k). unfold has_132_at.
  rewrite (rank_val P w i Ki), (rank_val P w j Kj), (rank_val P w k Kk).
  repeat split; try assumption.
  - apply (rank_ord P w i j); [lia | exact Ki | exact Kj].
  - apply (rank_ord P w j k); [lia | exact Kj | exact Kk].
  - apply (rank_bound P w k Kk).
Qed.

Theorem filter_213 : forall P w p q r,
  keeps P w p -> keeps P w q -> keeps P w r ->
  has_213_at w p q r -> contains_213 (filter P w).
Proof.
  intros P w p q r Kp Kq Kr H.
  destruct H as [Hpq [Hqr [Hr [H1 H2]]]].
  exists (rank P w p), (rank P w q), (rank P w r). unfold has_213_at.
  rewrite (rank_val P w p Kp), (rank_val P w q Kq), (rank_val P w r Kr).
  repeat split; try assumption.
  - apply (rank_ord P w p q); [lia | exact Kp | exact Kq].
  - apply (rank_ord P w q r); [lia | exact Kq | exact Kr].
  - apply (rank_bound P w r Kr).
Qed.

Theorem filter_1324 : forall P w i j k l,
  keeps P w i -> keeps P w j -> keeps P w k -> keeps P w l ->
  has_1324_at w i j k l -> contains_1324 (filter P w).
Proof.
  intros P w i j k l Ki Kj Kk Kl H.
  destruct H as [Hij [Hjk [Hkl [Hl [H1 [H2 H3]]]]]].
  exists (rank P w i), (rank P w j), (rank P w k), (rank P w l).
  unfold has_1324_at.
  rewrite (rank_val P w i Ki), (rank_val P w j Kj),
          (rank_val P w k Kk), (rank_val P w l Kl).
  repeat split; try assumption.
  - apply (rank_ord P w i j); [lia | exact Ki | exact Kj].
  - apply (rank_ord P w j k); [lia | exact Kj | exact Kk].
  - apply (rank_ord P w k l); [lia | exact Kk | exact Kl].
  - apply (rank_bound P w l Kl).
Qed.

Theorem above_gives_above_213 : forall j u p q r,
  has_213_above u j p q r -> contains_213 (above j u).
Proof.
  intros j u p q r Hab.
  destruct (above_all_gt u j p q r Hab) as [Gp [Gq Gr]].
  destruct Hab as [H213 _].
  assert (Hpq : (p < q)%nat) by (destruct H213 as [K _]; exact K).
  assert (Hqr : (q < r)%nat) by (destruct H213 as [_ [K _]]; exact K).
  assert (Hr : (r < length u)%nat)
    by (destruct H213 as [_ [_ [K _]]]; exact K).
  unfold above.
  apply (filter_213 (fun x => Nat.ltb j x) u p q r);
    [ keep | keep | keep | exact H213 ].
Qed.

Corollary above_213_iff : forall j u,
  contains_213 (above j u) <-> exists p q r, has_213_above u j p q r.
Proof.
  intros j u. split.
  - apply above_213_gives_above.
  - intros [p [q [r H]]]. apply (above_gives_above_213 j u p q r). exact H.
Qed.

(* The first-letter rule, as a statement about words rather than indices. *)
Theorem cons_1324_above : forall j u,
  contains_1324 (j :: u) <->
  (contains_1324 u \/ contains_213 (above j u)).
Proof.
  intros j u. rewrite cons_1324, above_213_iff. reflexivity.
Qed.

Corollary cons_1324_above_avoid : forall j u,
  ~ contains_1324 (j :: u) <->
  (~ contains_1324 u /\ ~ contains_213 (above j u)).
Proof.
  intros j u. split.
  - intro H. split; intro C; apply H; apply cons_1324_above;
      [left | right]; exact C.
  - intros [H1 H2] C. apply cons_1324_above in C.
    destruct C as [C | C]; [apply H1 | apply H2]; exact C.
Qed.

(* A word led by its minimum avoids 1324 exactly when its tail avoids 213. *)
Corollary cons_min_1324 : forall j u,
  (forall x, In x u -> (j < x)%nat) ->
  (~ contains_1324 (j :: u) <-> ~ contains_213 u).
Proof.
  intros j u Hmin.
  assert (Heq : above j u = u).
  { unfold above. apply filter_all. intros y Hy.
    apply Nat.ltb_lt. apply Hmin. exact Hy. }
  rewrite cons_1324_above_avoid, Heq. split.
  - intros [_ H]. exact H.
  - intro H. split; [intro C; apply H; apply sub_1324_213; exact C | exact H].
Qed.

(* Avoidance says every point sees a 213-avoider in its upper-right quadrant. *)

Definition quadrant (w : list nat) (i : nat) : list nat :=
  above (nth i w 0%nat) (skipn (S i) w).

Lemma quadrant_cons_0 : forall j u, quadrant (j :: u) 0 = above j u.
Proof. intros j u. reflexivity. Qed.

Lemma quadrant_cons_S : forall j u i, quadrant (j :: u) (S i) = quadrant u i.
Proof. intros j u i. reflexivity. Qed.

Theorem avoid_1324_quadrant : forall w,
  ~ contains_1324 w <->
  (forall i, (i < length w)%nat -> ~ contains_213 (quadrant w i)).
Proof.
  induction w as [|j u IH].
  - split.
    + intros _ i Hi. simpl in Hi. lia.
    + intros _ [i [a [b [c H]]]]. unfold has_1324_at in H. simpl in H. lia.
  - rewrite cons_1324_above_avoid, IH. split.
    + intros [Hq Hab] i Hi.
      destruct i as [|i]; [rewrite quadrant_cons_0; exact Hab|].
      rewrite quadrant_cons_S. apply Hq. simpl in Hi. lia.
    + intro H. split.
      * intros i Hi. rewrite <- quadrant_cons_S with (j := j).
        apply H. simpl. lia.
      * rewrite <- quadrant_cons_0 with (u := u). apply H. simpl. lia.
Qed.

(* The criterion, spelled out with the quadrant unfolded. *)
Corollary avoid_1324_ne : forall w,
  ~ contains_1324 w <->
  (forall i, (i < length w)%nat ->
     ~ contains_213 (above (nth i w 0%nat) (skipn (S i) w))).
Proof. exact avoid_1324_quadrant. Qed.

(* Reverse-complement, an involution on [0,m) preserving 1324-avoidance. *)

Definition compl (m : nat) (u : list nat) : list nat := map (fun x => m - S x) u.

Definition rc (m : nat) (u : list nat) : list nat := rev (compl m u).

Lemma compl_length : forall m u, length (compl m u) = length u.
Proof. intros m u. unfold compl. apply len_map. Qed.

Lemma rc_length : forall m u, length (rc m u) = length u.
Proof. intros m u. unfold rc. rewrite length_rev. apply compl_length. Qed.

Lemma compl_bound : forall m u,
  (forall x, In x u -> (x < m)%nat) ->
  forall y, In y (compl m u) -> (y < m)%nat.
Proof.
  intros m u Hb y Hy. unfold compl in Hy. apply in_map_iff in Hy.
  destruct Hy as [x [Hxy Hin]]. specialize (Hb _ Hin). lia.
Qed.

Lemma rc_bound : forall m u,
  (forall x, In x u -> (x < m)%nat) ->
  forall y, In y (rc m u) -> (y < m)%nat.
Proof.
  intros m u Hb y Hy. unfold rc in Hy. apply in_rev in Hy.
  apply (compl_bound m u Hb). exact Hy.
Qed.

Lemma compl_compl : forall m u,
  (forall x, In x u -> (x < m)%nat) -> map (fun x => m - S (m - S x)) u = u.
Proof.
  intros m u. induction u as [|a u IH]; intro Hb; simpl; [reflexivity|].
  assert (Ha : (a < m)%nat) by (apply Hb; left; reflexivity).
  rewrite IH by (intros x Hx; apply Hb; right; exact Hx).
  f_equal. lia.
Qed.

Theorem rc_involutive : forall m u,
  (forall x, In x u -> (x < m)%nat) -> rc m (rc m u) = u.
Proof.
  intros m u Hb. unfold rc, compl.
  rewrite map_rev, rev_involutive, map_map.
  apply compl_compl. exact Hb.
Qed.

Lemma rc_nth : forall m u i, (i < length u)%nat ->
  nth i (rc m u) 0%nat = (m - S (nth (length u - S i) u 0%nat))%nat.
Proof.
  intros m u i Hi. unfold rc, compl.
  rewrite rev_nth by (rewrite len_map; lia).
  rewrite len_map.
  rewrite nth_map_in by lia.
  reflexivity.
Qed.

(* rev of 1324 is 4231 and its complement is 1324 again. *)
Lemma rc_1324 : forall m u,
  (forall x, In x u -> (x < m)%nat) ->
  contains_1324 u -> contains_1324 (rc m u).
Proof.
  intros m u Hb [i [j [k [l H]]]]. unfold has_1324_at in H.
  destruct H as [Hij [Hjk [Hkl [Hlen [Hik [Hkj Hjl]]]]]].
  assert (Bi : (nth i u 0%nat < m)%nat) by (apply Hb; apply nth_in; lia).
  assert (Bj : (nth j u 0%nat < m)%nat) by (apply Hb; apply nth_in; lia).
  assert (Bk : (nth k u 0%nat < m)%nat) by (apply Hb; apply nth_in; lia).
  assert (Bl : (nth l u 0%nat < m)%nat) by (apply Hb; apply nth_in; lia).
  exists (length u - S l)%nat, (length u - S k)%nat,
         (length u - S j)%nat, (length u - S i)%nat.
  unfold has_1324_at. rewrite rc_length.
  rewrite (rc_nth m u (length u - S l)) by lia.
  rewrite (rc_nth m u (length u - S k)) by lia.
  rewrite (rc_nth m u (length u - S j)) by lia.
  rewrite (rc_nth m u (length u - S i)) by lia.
  replace (length u - S (length u - S l))%nat with l by lia.
  replace (length u - S (length u - S k))%nat with k by lia.
  replace (length u - S (length u - S j))%nat with j by lia.
  replace (length u - S (length u - S i))%nat with i by lia.
  repeat split; lia.
Qed.

Theorem rc_avoid_1324 : forall m u,
  (forall x, In x u -> (x < m)%nat) ->
  (~ contains_1324 u <-> ~ contains_1324 (rc m u)).
Proof.
  intros m u Hb. split.
  - intros Hno C.
    apply Hno. rewrite <- (rc_involutive m u Hb).
    apply (rc_1324 m (rc m u) (rc_bound m u Hb)). exact C.
  - intros Hno C. apply Hno. apply (rc_1324 m u Hb). exact C.
Qed.

Lemma in_rev_iff : forall (l : list nat) x, In x (rev l) <-> In x l.
Proof.
  induction l as [|a l IH]; intro x; simpl; [reflexivity|].
  split.
  - intro H. apply in_app_or in H. destruct H as [H | H].
    + right. apply IH. exact H.
    + simpl in H. destruct H as [<- | []]. left. reflexivity.
  - intro H. apply in_or_app. destruct H as [<- | H].
    + right. left. reflexivity.
    + left. apply IH. exact H.
Qed.

Lemma nodup_rev : forall (l : list nat), NoDup l -> NoDup (rev l).
Proof.
  induction l as [|a l IH]; intro H; simpl; [constructor|].
  inversion H as [|x r Hnin Hnd Heq]; subst.
  apply nodup_app_single; [apply IH; exact Hnd|].
  intro Hc. apply Hnin. apply in_rev_iff. exact Hc.
Qed.

Lemma nodup_map_inj_in : forall (f : nat -> nat) (l : list nat),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup l -> NoDup (map f l).
Proof.
  intros f l. induction l as [|a l IH]; intros Hinj H; simpl; [constructor|].
  inversion H as [|x r Hnin Hnd Heq]; subst.
  constructor.
  - intro Hc. apply in_map_iff in Hc. destruct Hc as [y [Hy Hin]].
    apply Hinj in Hy; [subst y; contradiction | right; exact Hin | left; reflexivity].
  - apply IH; [| exact Hnd].
    intros x y Hx Hy. apply Hinj; right; assumption.
Qed.

Theorem rc_perm : forall m u, is_perm u m -> is_perm (rc m u) m.
Proof.
  intros m u [Hlen [Hnd Hb]]. repeat split.
  - rewrite rc_length. exact Hlen.
  - unfold rc. apply nodup_rev. apply nodup_map_inj_in; [| exact Hnd].
    intros x y Hx Hy Heq.
    assert (Bx : (x < m)%nat) by (apply Hb; exact Hx).
    assert (By : (y < m)%nat) by (apply Hb; exact Hy).
    lia.
  - apply rc_bound. exact Hb.
Qed.

(* rc is an involution on the set gen m enumerates. *)
Corollary rc_gen : forall m w, In w (gen m) -> In (rc m w) (gen m).
Proof.
  intros m w Hw. apply gen_spec in Hw. destruct Hw as [Hp Hav].
  apply gen_spec. split.
  - apply rc_perm. exact Hp.
  - apply (rc_avoid_1324 m w (proj2 (proj2 Hp))). exact Hav.
Qed.

(* rc exchanges the two cell classes of the staircase.  Reversing positions and
   complementing values reverses both coordinates, so it carries the pattern 132
   to 213 and back; the transport is the same index arithmetic as rc_1324. *)

Theorem rc_132 : forall m u,
  (forall x, In x u -> (x < m)%nat) ->
  contains_132 u -> contains_213 (rc m u).
Proof.
  intros m u Hb [i [j [k H]]]. unfold has_132_at in H.
  destruct H as [Hij [Hjk [Hk [Hik Hkj]]]].
  assert (Bi : (nth i u 0%nat < m)%nat) by (apply Hb; apply nth_in; lia).
  assert (Bj : (nth j u 0%nat < m)%nat) by (apply Hb; apply nth_in; lia).
  assert (Bk : (nth k u 0%nat < m)%nat) by (apply Hb; apply nth_in; lia).
  exists (length u - S k)%nat, (length u - S j)%nat, (length u - S i)%nat.
  unfold has_213_at. rewrite rc_length.
  rewrite (rc_nth m u (length u - S k)%nat) by lia.
  rewrite (rc_nth m u (length u - S j)%nat) by lia.
  rewrite (rc_nth m u (length u - S i)%nat) by lia.
  replace (length u - S (length u - S k))%nat with k by lia.
  replace (length u - S (length u - S j))%nat with j by lia.
  replace (length u - S (length u - S i))%nat with i by lia.
  repeat split; lia.
Qed.

Theorem rc_213 : forall m u,
  (forall x, In x u -> (x < m)%nat) ->
  contains_213 u -> contains_132 (rc m u).
Proof.
  intros m u Hb [p [q [r H]]]. unfold has_213_at in H.
  destruct H as [Hpq [Hqr [Hr [Hqp Hpr]]]].
  assert (Bp : (nth p u 0%nat < m)%nat) by (apply Hb; apply nth_in; lia).
  assert (Bq : (nth q u 0%nat < m)%nat) by (apply Hb; apply nth_in; lia).
  assert (Br : (nth r u 0%nat < m)%nat) by (apply Hb; apply nth_in; lia).
  exists (length u - S r)%nat, (length u - S q)%nat, (length u - S p)%nat.
  unfold has_132_at. rewrite rc_length.
  rewrite (rc_nth m u (length u - S r)%nat) by lia.
  rewrite (rc_nth m u (length u - S q)%nat) by lia.
  rewrite (rc_nth m u (length u - S p)%nat) by lia.
  replace (length u - S (length u - S r))%nat with r by lia.
  replace (length u - S (length u - S q))%nat with q by lia.
  replace (length u - S (length u - S p))%nat with p by lia.
  repeat split; lia.
Qed.

Corollary rc_avoid_213 : forall m u,
  (forall x, In x u -> (x < m)%nat) ->
  (~ contains_132 u <-> ~ contains_213 (rc m u)).
Proof.
  intros m u Hb. split; intros H C.
  - apply H. rewrite <- (rc_involutive m u Hb).
    apply (rc_213 m (rc m u) (rc_bound m u Hb)). exact C.
  - apply H. apply (rc_132 m u Hb). exact C.
Qed.

(* The transfer statistic: mu gives legality, mfun the next mu. *)

(* The '3'-values the profile gains when y is appended. *)
Definition new_three (u : list nat) (y w : nat) : Prop :=
  exists j, candidate_strict u y j /\ nth j u 0%nat = w.

(* mfun u y is the least of them. *)
Definition is_mfun (u : list nat) (y f : nat) : Prop :=
  new_three u y f /\ forall w, new_three u y w -> (f <= w)%nat.

Lemma profile_append : forall u y w,
  three_value (u ++ [y]) w <-> (three_value u w \/ new_three u y w).
Proof. intros u y w. apply three_values_append. Qed.

Lemma candidate_strict_dec : forall u y j,
  {candidate_strict u y j} + {~ candidate_strict u y j}.
Proof.
  intros u y j. unfold candidate_strict.
  destruct (lt_dec j (length u)) as [H1|H1]; [|right; tauto].
  destruct (lt_dec y (nth j u 0%nat)) as [H2|H2]; [|right; tauto].
  destruct (bounded_ex_dec (fun i => (nth i u 0%nat < y)%nat) j
              (fun i => lt_dec (nth i u 0%nat) y)) as [H3|H3].
  - left. repeat split; assumption.
  - right. intros [_ [_ H]]. contradiction.
Qed.

Lemma new_three_dec : forall u y w, {new_three u y w} + {~ new_three u y w}.
Proof.
  intros u y w. unfold new_three.
  destruct (bounded_ex_dec
              (fun j => candidate_strict u y j /\ nth j u 0%nat = w)
              (length u)) as [H|H].
  - intro j. destruct (candidate_strict_dec u y j) as [Hc|Hc]; [|right; tauto].
    destruct (Nat.eq_dec (nth j u 0%nat) w) as [He|He]; [|right; tauto].
    left. split; assumption.
  - left. destruct H as [j [_ Hj]]. exists j. exact Hj.
  - right. intros [j [Hc Hw]]. apply H. exists j. split.
    + destruct Hc as [Hj _]. exact Hj.
    + split; assumption.
Qed.

Theorem mfun_exists : forall u y,
  (exists w, new_three u y w) -> exists f, is_mfun u y f.
Proof.
  intros u y [w Hw].
  destruct (least_dec (new_three u y) (new_three_dec u y) w Hw)
    as [f [Hf Hleast]].
  exists f. split; assumption.
Qed.

(* The new least profile element is the smaller of the old one and mfun. *)
Theorem mu_append : forall u y m f,
  is_mu u m -> is_mfun u y f -> is_mu (u ++ [y]) (Nat.min m f).
Proof.
  intros u y m f [Hm Hml] [Hf Hfl]. split.
  - apply profile_append.
    destruct (Nat.min_dec m f) as [E|E]; rewrite E;
      [left; exact Hm | right; exact Hf].
  - intros w Hw. apply profile_append in Hw. destruct Hw as [Hw | Hw].
    + specialize (Hml w Hw). lia.
    + specialize (Hfl w Hw). lia.
Qed.

(* From a 132-free word the new mu is mfun outright. *)
Theorem mu_append_free : forall u y f,
  ~ contains_132 u -> is_mfun u y f -> is_mu (u ++ [y]) f.
Proof.
  intros u y f H132 [Hf Hfl]. split.
  - apply profile_append. right. exact Hf.
  - intros w Hw. apply profile_append in Hw. destruct Hw as [Hw | Hw].
    + exfalso. apply (proj1 (profile_empty_iff u) H132 w). exact Hw.
    + apply Hfl. exact Hw.
Qed.

Theorem mu_append_none : forall u y m,
  is_mu u m -> (forall w, ~ new_three u y w) -> is_mu (u ++ [y]) m.
Proof.
  intros u y m [Hm Hml] Hno. split.
  - apply profile_append. left. exact Hm.
  - intros w Hw. apply profile_append in Hw. destruct Hw as [Hw | Hw].
    + apply Hml. exact Hw.
    + exfalso. apply (Hno w). exact Hw.
Qed.

(* mfun is undefined exactly at a safe value. *)
Theorem no_new_three_iff_safe : forall u y,
  ~ In y u -> ((forall w, ~ new_three u y w) <-> safe_at u y).
Proof.
  intros u y Hy. split.
  - intros Hno [i [j [Hij [Hj [Hi Hjy]]]]].
    assert (Hne : nth j u 0%nat <> y).
    { intro Hc. apply Hy. rewrite <- Hc. apply nth_in. exact Hj. }
    apply (Hno (nth j u 0%nat)). exists j. split; [| reflexivity].
    unfold candidate_strict. repeat split; [exact Hj | lia |].
    exists i. split; [exact Hij | exact Hi].
  - intros Hsafe w [j [Hc Hw]].
    destruct Hc as [Hj [Hyj [i [Hij Hi]]]].
    apply Hsafe. exists i, j. repeat split; try assumption. lia.
Qed.

(* One transfer step: legality from mu alone, the next mu from mu and mfun. *)
Corollary transfer_step : forall u y m f,
  ~ contains_1324 u -> is_mu u m -> is_mfun u y f ->
  (legal u y <-> (y <= m)%nat) /\ is_mu (u ++ [y]) (Nat.min m f).
Proof.
  intros u y m f Hav Hmu Hmf. split.
  - apply (legal_iff_le_mu u m Hav Hmu).
  - apply (mu_append u y m f Hmu Hmf).
Qed.

Definition has_below (u : list nat) (z : nat) : Prop :=
  exists i, (i < length u)%nat /\ (nth i u 0%nat < z)%nat.

(* Appending y can add only y itself to the candidates at any threshold. *)
Theorem new_three_append : forall u y z w,
  new_three (u ++ [y]) z w <->
  (new_three u z w \/ (w = y /\ (z < y)%nat /\ has_below u z)).
Proof.
  intros u y z w. unfold new_three, has_below. split.
  - intros [j [Hc Hw]].
    destruct Hc as [Hj [Hzj [i [Hij Hi]]]].
    rewrite len_app in Hj. simpl in Hj.
    destruct (Nat.eq_dec j (length u)) as [He | Hne].
    + right. subst j. rewrite nth_last in Hzj, Hw.
      rewrite (nth_app1 u [y] i 0%nat) in Hi by lia.
      split; [symmetry; exact Hw | split; [exact Hzj |]].
      exists i. split; [lia | exact Hi].
    + left. exists j.
      rewrite (nth_app1 u [y] j 0%nat) in Hzj, Hw by lia.
      rewrite (nth_app1 u [y] i 0%nat) in Hi by lia.
      split; [| exact Hw].
      unfold candidate_strict. repeat split; [lia | exact Hzj |].
      exists i. split; [exact Hij | exact Hi].
  - intros [[j [Hc Hw]] | [Hw [Hzy [i [Hi Hiz]]]]].
    + destruct Hc as [Hj [Hzj [i [Hij Hi]]]].
      exists j. split.
      * unfold candidate_strict.
        rewrite (nth_app1 u [y] j 0%nat) by lia.
        repeat split; [rewrite len_app; simpl; lia | exact Hzj |].
        exists i. rewrite (nth_app1 u [y] i 0%nat) by lia.
        split; [exact Hij | exact Hi].
      * rewrite (nth_app1 u [y] j 0%nat) by lia. exact Hw.
    + exists (length u). split.
      * unfold candidate_strict. rewrite nth_last.
        repeat split; [rewrite len_app; simpl; lia | exact Hzy |].
        exists i. rewrite (nth_app1 u [y] i 0%nat) by lia.
        split; [lia | exact Hiz].
      * rewrite nth_last. symmetry. exact Hw.
Qed.

(* Hence the mfun transition, in the two cases the transfer distinguishes. *)
Theorem mfun_append_low : forall u y z f,
  is_mfun u z f -> (z < y)%nat -> has_below u z ->
  is_mfun (u ++ [y]) z (Nat.min f y).
Proof.
  intros u y z f [Hf Hfl] Hzy Hb. split.
  - apply new_three_append.
    destruct (Nat.min_dec f y) as [E|E]; rewrite E.
    + left. exact Hf.
    + right. split; [reflexivity | split; assumption].
  - intros w Hw. apply new_three_append in Hw. destruct Hw as [Hw | [Hw _]].
    + specialize (Hfl w Hw). lia.
    + subst w. lia.
Qed.

Theorem mfun_append_high : forall u y z f,
  is_mfun u z f -> ~ (z < y)%nat -> is_mfun (u ++ [y]) z f.
Proof.
  intros u y z f [Hf Hfl] Hzy. split.
  - apply new_three_append. left. exact Hf.
  - intros w Hw. apply new_three_append in Hw.
    destruct Hw as [Hw | [_ [Hc _]]]; [apply Hfl; exact Hw | lia].
Qed.

(* Counting by truncation: a level total is the sum of per-word extension counts. *)

Lemma flat_map_singleton : forall (A : Type) (l : list A),
  flat_map (fun x => [x]) l = l.
Proof.
  intros A. induction l as [|a l IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma flat_map_app_gen : forall (A B : Type) (f : A -> list B) l1 l2,
  flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof.
  intros A B f. induction l1 as [|a l1 IH]; intro l2; simpl; [reflexivity|].
  rewrite IH, app_assoc. reflexivity.
Qed.

Lemma flat_map_assoc : forall (A B C : Type) (f : A -> list B) (g : B -> list C) l,
  flat_map g (flat_map f l) = flat_map (fun x => flat_map g (f x)) l.
Proof.
  intros A B C f g. induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite flat_map_app_gen, IH. reflexivity.
Qed.

(* every legal k-letter extension of u, as words over [0, m+k) *)
Fixpoint extend (u : list nat) (m k : nat) : list (list nat) :=
  match k with
  | 0%nat => [u]
  | S k' => flat_map (fun v => map (ext v) (filter (legalb v) (seq 0 (S (m + k')))))
                     (extend u m k')
  end.

Theorem gen_extend : forall k m,
  gen (m + k) = flat_map (fun u => extend u m k) (gen m).
Proof.
  induction k as [|k IH]; intro m.
  - rewrite Nat.add_0_r. simpl. rewrite flat_map_singleton. reflexivity.
  - rewrite Nat.add_succ_r, gen_S, (IH m), flat_map_assoc. reflexivity.
Qed.

(* Extension lists are disjoint, so the cardinality is the plain sum. *)
Corollary card_extend : forall k m,
  card (m + k) =
  fold_right (fun u acc => (length (extend u m k) + acc)%nat) 0%nat (gen m).
Proof.
  intros k m. unfold card. rewrite gen_extend. apply length_flat_map.
Qed.

(* k = 1 recovers the branching recurrence. *)
Corollary card_extend_one : forall m,
  card (m + 1) =
  fold_right (fun u acc =>
    (length (map (ext u) (filter (legalb u) (seq 0 (S m)))) + acc)%nat) 0%nat (gen m).
Proof.
  intro m. rewrite card_extend. apply fold_right_pointwise.
  intros x a. simpl. rewrite Nat.add_0_r, app_nil_r. reflexivity.
Qed.

Theorem mfun_append_new : forall u y z,
  (forall w, ~ new_three u z w) -> (z < y)%nat -> has_below u z ->
  is_mfun (u ++ [y]) z y.
Proof.
  intros u y z Hno Hzy Hb. split.
  - apply new_three_append. right. split; [reflexivity | split; assumption].
  - intros w Hw. apply new_three_append in Hw.
    destruct Hw as [Hw | [Hw _]]; [exfalso; apply (Hno w); exact Hw | lia].
Qed.

(* Theta-calculus coefficients: the two generating functions expanded binomially
   and cleared of 2^j. *)

Require Import ZArith.
Open Scope Z_scope.

Fixpoint binomZ (n k : nat) {struct n} : Z :=
  match n, k with
  | _, O => 1
  | O, S _ => 0
  | S n', S k' => binomZ n' k' + binomZ n' (S k')
  end.

(* binomZ recurses on n, so these two do not hold by conversion alone *)
Lemma binomZ_0 : forall n, binomZ n 0 = 1.
Proof. destruct n; reflexivity. Qed.

Lemma binomZ_pascal : forall n k,
  binomZ (S n) (S k) = binomZ n k + binomZ n (S k).
Proof. intros n k. reflexivity. Qed.

Lemma binomZ_zero_above : forall n k, (n < k)%nat -> binomZ n k = 0.
Proof.
  induction n as [|n IH]; intros k H.
  - destruct k; [lia | reflexivity].
  - destruct k as [|k]; [lia|].
    rewrite binomZ_pascal, (IH k) by lia. rewrite (IH (S k)) by lia. lia.
Qed.

Lemma binomZ_one : forall n, binomZ n 1 = Z.of_nat n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  rewrite binomZ_pascal, binomZ_0, IH. lia.
Qed.

(* (n - k) C(n,k) = (k+1) C(n,k+1) *)
Lemma binomZ_step : forall n k, (k <= n)%nat ->
  (Z.of_nat n - Z.of_nat k) * binomZ n k = Z.of_nat (S k) * binomZ n (S k).
Proof.
  induction n as [|n IH]; intros k Hk.
  - assert (k = 0)%nat by lia. subst. simpl binomZ. lia.
  - destruct k as [|k].
    + rewrite binomZ_0, binomZ_pascal, binomZ_0, binomZ_one. lia.
    + destruct (le_lt_dec (S k) n) as [Hle | Hlt].
      * assert (E1 := IH k ltac:(lia)). assert (E2 := IH (S k) ltac:(lia)).
        rewrite !binomZ_pascal. rewrite Nat2Z.inj_succ in *. nia.
      * assert (Hnk : (n = k)%nat) by lia. subst n.
        rewrite (binomZ_zero_above (S k) (S (S k))) by lia. lia.
Qed.

(* (n+1 - k) C(n+1,k) = (n+1) C(n,k), the pivot both recursions turn on *)
Lemma binomZ_pivot : forall n k, (k <= S n)%nat ->
  (Z.of_nat (S n) - Z.of_nat k) * binomZ (S n) k = Z.of_nat (S n) * binomZ n k.
Proof.
  intros n k Hk. destruct k as [|k].
  - rewrite !binomZ_0. lia.
  - rewrite binomZ_pascal.
    destruct (le_lt_dec (S k) n) as [Hle | Hlt].
    + assert (E := binomZ_step n k ltac:(lia)).
      rewrite Nat2Z.inj_succ in *. nia.
    + assert (Hnk : (n = k)%nat) by lia. subst n.
      rewrite (binomZ_zero_above k (S k)) by lia. lia.
Qed.

Fixpoint sumZ (n : nat) (f : nat -> Z) : Z :=
  match n with O => f O | S m => sumZ m f + f (S m) end.

Lemma sumZ_ext : forall n f g,
  (forall k, (k <= n)%nat -> f k = g k) -> sumZ n f = sumZ n g.
Proof.
  induction n as [|n IH]; intros f g H; simpl.
  - apply H. lia.
  - rewrite (IH f g) by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma sumZ_comb : forall n a b f g,
  sumZ n (fun k => a * f k - b * g k) = a * sumZ n f - b * sumZ n g.
Proof.
  induction n as [|n IH]; intros a b f g; simpl; [lia|].
  rewrite IH. lia.
Qed.

Fixpoint zpow (b : Z) (e : nat) : Z :=
  match e with O => 1 | S e' => b * zpow b e' end.

(* 2^j times the C(2M,M)-side coefficient, and the 4^M-side coefficient *)
Definition Sat (j i n : nat) : Z :=
  sumZ n (fun k => zpow (-1) k * binomZ i k * zpow (Z.of_nat (2*k+1)) j).
Definition Tat (j i n : nat) : Z :=
  sumZ n (fun k => zpow (-1) k * binomZ i k * zpow (Z.of_nat (k+1)) j).
Definition Ssum (j i : nat) : Z := Sat j i i.
Definition Tsum (j i : nat) : Z := Tat j i i.

Lemma Sat_extend : forall j i, Sat j i (S i) = Sat j i i.
Proof.
  intros j i. unfold Sat. simpl sumZ.
  rewrite (binomZ_zero_above i (S i)) by lia. lia.
Qed.

Lemma Tat_extend : forall j i, Tat j i (S i) = Tat j i i.
Proof.
  intros j i. unfold Tat. simpl sumZ.
  rewrite (binomZ_zero_above i (S i)) by lia. lia.
Qed.

Theorem Ssum_rec : forall j i,
  Ssum (S j) (S i) =
  (2 * Z.of_nat (S i) + 1) * Ssum j (S i) - 2 * Z.of_nat (S i) * Ssum j i.
Proof.
  intros j i. unfold Ssum. rewrite <- (Sat_extend j i). unfold Sat.
  rewrite <- sumZ_comb.
  apply sumZ_ext. intros k Hk.
  assert (P := binomZ_pivot i k Hk).
  cbn [zpow].
  assert (H1 : Z.of_nat (2*k+1) = 2 * Z.of_nat k + 1) by lia.
  rewrite H1.
  set (X := zpow (2 * Z.of_nat k + 1) j). set (Y := zpow (-1) k).
  assert (Q : binomZ (S i) k * (2 * Z.of_nat k + 1)
            = (2 * Z.of_nat (S i) + 1) * binomZ (S i) k
            - 2 * Z.of_nat (S i) * binomZ i k) by nia.
  transitivity (Y * X * (binomZ (S i) k * (2 * Z.of_nat k + 1)));
    [ring | rewrite Q; ring].
Qed.

Theorem Tsum_rec : forall j i,
  Tsum (S j) (S i) =
  (Z.of_nat (S i) + 1) * Tsum j (S i) - Z.of_nat (S i) * Tsum j i.
Proof.
  intros j i. unfold Tsum. rewrite <- (Tat_extend j i). unfold Tat.
  rewrite <- sumZ_comb.
  apply sumZ_ext. intros k Hk.
  assert (P := binomZ_pivot i k Hk).
  cbn [zpow].
  assert (H1 : Z.of_nat (k+1) = Z.of_nat k + 1) by lia.
  rewrite H1.
  set (X := zpow (Z.of_nat k + 1) j). set (Y := zpow (-1) k).
  assert (Q : binomZ (S i) k * (Z.of_nat k + 1)
            = (Z.of_nat (S i) + 1) * binomZ (S i) k
            - Z.of_nat (S i) * binomZ i k) by nia.
  transitivity (Y * X * (binomZ (S i) k * (Z.of_nat k + 1)));
    [ring | rewrite Q; ring].
Qed.

(* With the corner cell empty, an occurrence lies wholly in one domino of the L. *)
Theorem tromino_fibre : forall w P R,
  (forall t, (P <= t)%nat -> (t < length w)%nat -> (nth t w 0%nat < R)%nat) ->
  forall i j k l, has_1324_at w i j k l ->
  (l < P)%nat \/
  ((nth i w 0%nat < R)%nat /\ (nth j w 0%nat < R)%nat /\
   (nth k w 0%nat < R)%nat /\ (nth l w 0%nat < R)%nat).
Proof.
  intros w P R Hempty i j k l H.
  destruct H as [Hij [Hjk [Hkl [Hlen [Hik [Hkj Hjl]]]]]].
  destruct (Nat.lt_ge_cases l P) as [Hl | Hl]; [left; exact Hl | right].
  assert (Hlr : (nth l w 0%nat < R)%nat)
    by (apply Hempty; [exact Hl | exact Hlen]).
  repeat split; lia.
Qed.

(* Cut by value at S: with the low cell 132-free and the high cell 213-free, an
   occurrence is an ascent of each interleaved as p1 < q1 < p2 < q2. *)
Theorem domino_criterion : forall w S,
  (forall i j k, (i < j)%nat -> (j < k)%nat -> (k < length w)%nat ->
     (nth i w 0%nat < S)%nat -> (nth j w 0%nat < S)%nat -> (nth k w 0%nat < S)%nat ->
     ~ ((nth i w 0%nat < nth k w 0%nat)%nat /\ (nth k w 0%nat < nth j w 0%nat)%nat)) ->
  (forall i j k, (i < j)%nat -> (j < k)%nat -> (k < length w)%nat ->
     (S <= nth i w 0%nat)%nat -> (S <= nth j w 0%nat)%nat -> (S <= nth k w 0%nat)%nat ->
     ~ ((nth j w 0%nat < nth i w 0%nat)%nat /\ (nth i w 0%nat < nth k w 0%nat)%nat)) ->
  contains_1324 w ->
  exists p1 q1 p2 q2,
    (p1 < q1)%nat /\ (q1 < p2)%nat /\ (p2 < q2)%nat /\ (q2 < length w)%nat /\
    (nth p1 w 0%nat < S)%nat /\ (nth p2 w 0%nat < S)%nat /\
    (S <= nth q1 w 0%nat)%nat /\ (S <= nth q2 w 0%nat)%nat /\
    (nth p1 w 0%nat < nth p2 w 0%nat)%nat /\
    (nth q1 w 0%nat < nth q2 w 0%nat)%nat.
Proof.
  intros w S H132 H213 [i [j [k [l H]]]].
  destruct H as [Hij [Hjk [Hkl [Hlen [Hik [Hkj Hjl]]]]]].
  destruct (Nat.lt_ge_cases (nth j w 0%nat) S) as [Hj | Hj].
  - exfalso. apply (H132 i j k); lia.
  - destruct (Nat.lt_ge_cases (nth k w 0%nat) S) as [Hk | Hk].
    + exists i, j, k, l. repeat split; lia.
    + exfalso. apply (H213 j k l); lia.
Qed.

(* Shuffling a top block into a 132-free word puts every 132's '3' in that block. *)
Theorem high_block_criterion : forall w S,
  (forall i j k, (i < j)%nat -> (j < k)%nat -> (k < length w)%nat ->
     (nth i w 0%nat < S)%nat -> (nth j w 0%nat < S)%nat ->
     (nth k w 0%nat < S)%nat ->
     ~ ((nth i w 0%nat < nth k w 0%nat)%nat /\
        (nth k w 0%nat < nth j w 0%nat)%nat)) ->
  contains_132 w ->
  exists i j k, (i < j)%nat /\ (j < k)%nat /\ (k < length w)%nat /\
    (S <= nth j w 0%nat)%nat /\
    (nth i w 0%nat < nth k w 0%nat)%nat /\
    (nth k w 0%nat < nth j w 0%nat)%nat.
Proof.
  intros w S Hlow [i [j [k H]]].
  destruct H as [Hij [Hjk [Hlen [Hik Hkj]]]].
  exists i, j, k.
  assert (HS : (S <= nth j w 0%nat)%nat).
  { destruct (Nat.le_gt_cases S (nth j w 0%nat)) as [H1|H1]; [exact H1|].
    exfalso. apply (Hlow i j k); lia. }
  repeat split; assumption.
Qed.

Theorem high_block_criterion_conv : forall w i j k,
  (i < j)%nat -> (j < k)%nat -> (k < length w)%nat ->
  (nth i w 0%nat < nth k w 0%nat)%nat ->
  (nth k w 0%nat < nth j w 0%nat)%nat ->
  contains_132 w.
Proof.
  intros w i j k H1 H2 H3 H4 H5.
  exists i, j, k. unfold has_132_at. repeat split; lia.
Qed.

(* The converse: an interleaved pair of ascents produces an occurrence. *)
Theorem domino_criterion_conv : forall w S p1 q1 p2 q2,
  (p1 < q1)%nat -> (q1 < p2)%nat -> (p2 < q2)%nat -> (q2 < length w)%nat ->
  (nth p1 w 0%nat < S)%nat -> (nth p2 w 0%nat < S)%nat ->
  (S <= nth q1 w 0%nat)%nat -> (S <= nth q2 w 0%nat)%nat ->
  (nth p1 w 0%nat < nth p2 w 0%nat)%nat ->
  (nth q1 w 0%nat < nth q2 w 0%nat)%nat ->
  contains_1324 w.
Proof.
  intros w S p1 q1 p2 q2 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
  exists p1, q1, p2, q2. unfold has_1324_at. repeat split; lia.
Qed.

(* A 1324 carries a 132 on its first three letters and a 213 on its last three. *)
Theorem c1324_c132 : forall w, contains_1324 w -> contains_132 w.
Proof.
  intros w [i [j [k [l H]]]].
  destruct H as [Hij [Hjk [Hkl [Hlen [Hik [Hkj Hjl]]]]]].
  exists i, j, k. unfold has_132_at. repeat split; lia.
Qed.

(* Closure under skew sums, hence supermultiplicativity of the counting sequence. *)

Definition skew (u v : list nat) : list nat :=
  map (fun x => (x + length v)%nat) u ++ v.

Lemma len_map_add : forall c (u : list nat),
  length (map (fun x => (x + c)%nat) u) = length u.
Proof. intros c u. induction u as [|a u IH]; simpl; auto. Qed.

Lemma skew_length : forall u v,
  length (skew u v) = (length u + length v)%nat.
Proof.
  intros u v. unfold skew. rewrite len_app, len_map_add. reflexivity.
Qed.

Lemma skew_nth_lo : forall u v t, (t < length u)%nat ->
  nth t (skew u v) 0%nat = (nth t u 0%nat + length v)%nat.
Proof.
  intros u v t H. unfold skew.
  assert (Hm : (t < length (map (fun x => (x + length v)%nat) u))%nat)
    by (rewrite len_map_add; exact H).
  rewrite nth_app1 by exact Hm.
  erewrite nth_indep by exact Hm.
  rewrite map_nth. reflexivity.
Qed.

Lemma skew_nth_hi : forall u v t, (length u <= t)%nat ->
  nth t (skew u v) 0%nat = nth (t - length u)%nat v 0%nat.
Proof.
  intros u v t H. unfold skew.
  rewrite nth_app2 by (rewrite len_map_add; exact H).
  rewrite len_map_add. reflexivity.
Qed.

Lemma skew_val_lo : forall u v t, (t < length u)%nat ->
  (length v <= nth t (skew u v) 0%nat)%nat.
Proof. intros u v t H. rewrite skew_nth_lo by exact H. lia. Qed.

Lemma skew_val_hi : forall u v n t, is_perm v n ->
  (length u <= t)%nat -> (t < length u + length v)%nat ->
  (nth t (skew u v) 0%nat < length v)%nat.
Proof.
  intros u v n t Hp H1 H2. destruct Hp as [Hlen [_ Hlt]].
  rewrite skew_nth_hi by exact H1.
  rewrite Hlen. apply Hlt. apply nth_In. lia.
Qed.

(* An occurrence cannot straddle the blocks: its '1' would be earliest and smallest. *)
Theorem skew_avoids : forall u v m n,
  is_perm u m -> is_perm v n ->
  ~ contains_1324 u -> ~ contains_1324 v ->
  ~ contains_1324 (skew u v).
Proof.
  intros u v m n Hu Hv Nu Nv [i [j [k [l H]]]].
  destruct H as [Hij [Hjk [Hkl [Hlen [Hik [Hkj Hjl]]]]]].
  rewrite skew_length in Hlen.
  destruct (Nat.lt_ge_cases i (length u)) as [Hi | Hi].
  - assert (Hk : (k < length u)%nat).
    { destruct (Nat.lt_ge_cases k (length u)) as [Hk1|Hk2]; [exact Hk1|].
      exfalso.
      assert (A1 : (length v <= nth i (skew u v) 0%nat)%nat)
        by (apply skew_val_lo; exact Hi).
      assert (A2 : (nth k (skew u v) 0%nat < length v)%nat)
        by (apply (skew_val_hi u v n); [exact Hv | exact Hk2 | lia]).
      lia. }
    assert (Hj : (j < length u)%nat) by lia.
    assert (Hl : (l < length u)%nat).
    { destruct (Nat.lt_ge_cases l (length u)) as [Hl1|Hl2]; [exact Hl1|].
      exfalso.
      assert (A1 : (length v <= nth j (skew u v) 0%nat)%nat)
        by (apply skew_val_lo; exact Hj).
      assert (A2 : (nth l (skew u v) 0%nat < length v)%nat)
        by (apply (skew_val_hi u v n); [exact Hv | exact Hl2 | lia]).
      lia. }
    rewrite (skew_nth_lo u v i Hi) in Hik.
    rewrite (skew_nth_lo u v k Hk) in Hik, Hkj.
    rewrite (skew_nth_lo u v j Hj) in Hkj, Hjl.
    rewrite (skew_nth_lo u v l Hl) in Hjl.
    apply Nu. exists i, j, k, l. unfold has_1324_at. repeat split; lia.
  - assert (Hj : (length u <= j)%nat) by lia.
    assert (Hk : (length u <= k)%nat) by lia.
    assert (Hl : (length u <= l)%nat) by lia.
    rewrite (skew_nth_hi u v i Hi) in Hik.
    rewrite (skew_nth_hi u v k Hk) in Hik, Hkj.
    rewrite (skew_nth_hi u v j Hj) in Hkj, Hjl.
    rewrite (skew_nth_hi u v l Hl) in Hjl.
    apply Nv. exists (i - length u)%nat, (j - length u)%nat,
                     (k - length u)%nat, (l - length u)%nat.
    unfold has_1324_at. repeat split; lia.
Qed.

Lemma NoDup_map_add : forall c (u : list nat),
  NoDup u -> NoDup (map (fun x => (x + c)%nat) u).
Proof.
  intros c u H. induction H as [|a u Ha Hu IH]; simpl; constructor; [|exact IH].
  intro Hin. apply Ha. apply in_map_iff in Hin.
  destruct Hin as [y [Hy Hin]].
  assert (Ey : y = a) by lia. subst y. exact Hin.
Qed.

Lemma NoDup_app_disj : forall (A : Type) (l1 l2 : list A),
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> In x l2 -> False) ->
  NoDup (l1 ++ l2).
Proof.
  intros A. induction l1 as [|a l1 IH]; intros l2 H1 H2 Hd; simpl; [exact H2|].
  inversion H1 as [|x xs Ha Hrest]; subst. constructor.
  - intro Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + exact (Ha Hin).
    + exact (Hd a (or_introl eq_refl) Hin).
  - apply IH; [exact Hrest | exact H2 |].
    intros x Hx Hy. exact (Hd x (or_intror Hx) Hy).
Qed.

Theorem skew_perm : forall u v m n,
  is_perm u m -> is_perm v n -> is_perm (skew u v) (m + n)%nat.
Proof.
  intros u v m n [Hlu [Hnu Hbu]] [Hlv [Hnv Hbv]]. unfold skew.
  split; [|split].
  - rewrite len_app, len_map_add. lia.
  - apply NoDup_app_disj; [apply NoDup_map_add; exact Hnu | exact Hnv |].
    intros x Hx Hy. apply in_map_iff in Hx. destruct Hx as [y [Hy2 _]].
    apply Hbv in Hy. lia.
  - intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx|Hx].
    + apply in_map_iff in Hx. destruct Hx as [y [Hy Hin]].
      apply Hbu in Hin. lia.
    + apply Hbv in Hx. lia.
Qed.

(* The skew sum injects gen m x gen n into gen (m+n). *)

Lemma len_map_gen : forall (A B : Type) (f : A -> B) (l : list A),
  length (map f l) = length l.
Proof. intros A B f l. induction l as [|a l IH]; simpl; auto. Qed.

Lemma len_flat_map_const :
  forall (A B : Type) (f : A -> list B) (l : list A) c,
  (forall x, In x l -> length (f x) = c) ->
  length (flat_map f l) = (length l * c)%nat.
Proof.
  intros A B f. induction l as [|a l IH]; intros c H; simpl; [reflexivity|].
  rewrite len_app_gen, (H a (or_introl eq_refl)), (IH c); [lia|].
  intros x Hx. apply H. right. exact Hx.
Qed.

Lemma NoDup_map_inj : forall (A B : Type) (f : A -> B) (l : list A),
  NoDup l -> (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup (map f l).
Proof.
  intros A B f. induction l as [|a l IH]; intros Hl Hinj; simpl; [constructor|].
  inversion Hl as [|x xs Ha Hrest]; subst. constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Hy Hiny]].
    assert (Ea : a = y)
      by (apply Hinj; [left; reflexivity | right; exact Hiny | symmetry; exact Hy]).
    subst y. exact (Ha Hiny).
  - apply IH; [exact Hrest|].
    intros x y Hx Hy He.
    apply Hinj; [right; exact Hx | right; exact Hy | exact He].
Qed.

Lemma NoDup_flat_map_inj :
  forall (A B : Type) (f : A -> list B) (l : list A),
  NoDup l -> (forall x, In x l -> NoDup (f x)) ->
  (forall x y w, In x l -> In y l -> In w (f x) -> In w (f y) -> x = y) ->
  NoDup (flat_map f l).
Proof.
  intros A B f. induction l as [|a l IH]; intros Hl Hf Hd; simpl; [constructor|].
  inversion Hl as [|x xs Ha Hrest]; subst.
  apply NoDup_app_disj.
  - apply Hf. left. reflexivity.
  - apply IH; [exact Hrest | intros x Hx; apply Hf; right; exact Hx |].
    intros x y w Hx Hy; apply Hd; right; assumption.
  - intros w Hw1 Hw2. apply in_flat_map in Hw2. destruct Hw2 as [y [Hy Hwy]].
    assert (Ea : a = y)
      by (apply (Hd a y w); [left; reflexivity | right; exact Hy | exact Hw1 | exact Hwy]).
    subst y. exact (Ha Hy).
Qed.

Lemma app_split_eq : forall (a b c d : list nat),
  length a = length c -> a ++ b = c ++ d -> a = c /\ b = d.
Proof.
  induction a as [|x a IH]; intros b c d Hl He.
  - destruct c as [|y c]; [simpl in He; split; [reflexivity | exact He]
                          | simpl in Hl; discriminate].
  - destruct c as [|y c]; [simpl in Hl; discriminate|].
    simpl in He. injection He as He1 He2. simpl in Hl. injection Hl as Hl.
    destruct (IH b c d Hl He2) as [H1 H2].
    split; [f_equal; assumption | exact H2].
Qed.

Lemma map_add_inj : forall c (u u' : list nat),
  map (fun x => (x + c)%nat) u = map (fun x => (x + c)%nat) u' -> u = u'.
Proof.
  induction u as [|x u IH]; intros u' H.
  - destruct u'; [reflexivity | simpl in H; discriminate].
  - destruct u' as [|y u']; [simpl in H; discriminate|].
    simpl in H. injection H as H1 H2.
    f_equal; [lia | apply IH; exact H2].
Qed.

Lemma skew_inj : forall u v u' v' n,
  length v = n -> length v' = n -> skew u v = skew u' v' -> u = u' /\ v = v'.
Proof.
  intros u v u' v' n Hv Hv' He.
  assert (Htot : (length u + length v = length u' + length v')%nat)
    by (rewrite <- (skew_length u v), <- (skew_length u' v'), He; reflexivity).
  assert (Hlu : length u = length u') by lia.
  unfold skew in He.
  assert (Hml : length (map (fun x => (x + length v)%nat) u)
              = length (map (fun x => (x + length v')%nat) u'))
    by (rewrite !len_map_add; exact Hlu).
  destruct (app_split_eq _ _ _ _ Hml He) as [H1 H2].
  split; [| exact H2].
  rewrite Hv, Hv' in H1. exact (map_add_inj n u u' H1).
Qed.

Theorem card_supermult : forall m n, (card m * card n <= card (m + n))%nat.
Proof.
  intros m n.
  destruct (card_is_cardinality m) as [Hnm Hsm].
  destruct (card_is_cardinality n) as [Hnn Hsn].
  destruct (card_is_cardinality (m + n)) as [Hnmn Hsmn].
  assert (Hlv : forall v, In v (gen n) -> length v = n)
    by (intros v Hv; apply Hsn in Hv; destruct Hv as [[Hl _] _]; exact Hl).
  set (F := fun u => map (fun v => skew u v) (gen n)).
  assert (HL : length (flat_map F (gen m)) = (card m * card n)%nat).
  { rewrite (len_flat_map_const _ _ F (gen m) (card n)).
    - unfold card. reflexivity.
    - intros x _. unfold F, card. apply len_map_gen. }
  rewrite <- HL. unfold card.
  apply NoDup_incl_length.
  - apply NoDup_flat_map_inj; [exact Hnm | |].
    + intros u Hu. unfold F. apply NoDup_map_inj; [exact Hnn|].
      intros v v' Hv Hv' He.
      exact (proj2 (skew_inj u v u v' n (Hlv v Hv) (Hlv v' Hv') He)).
    + intros u u' w Hu Hu' Hw Hw'.
      unfold F in Hw, Hw'.
      apply in_map_iff in Hw. destruct Hw as [v [Hv Hinv]].
      apply in_map_iff in Hw'. destruct Hw' as [v' [Hv' Hinv']].
      subst w. symmetry in Hv'.
      exact (proj1 (skew_inj u v u' v' n (Hlv v Hinv) (Hlv v' Hinv') Hv')).
  - intros w Hw. apply in_flat_map in Hw. destruct Hw as [u [Hu Hw]].
    unfold F in Hw. apply in_map_iff in Hw. destruct Hw as [v [Hv Hinv]].
    subst w. apply Hsmn.
    apply Hsm in Hu. destruct Hu as [Hpu Hau].
    apply Hsn in Hinv. destruct Hinv as [Hpv Hav].
    split.
    + exact (skew_perm u v m n Hpu Hpv).
    + exact (skew_avoids u v m n Hpu Hpv Hau Hav).
Qed.

(* Direct sums do not preserve the class; the obstruction is a 132 in u or a 213
   in v, which is what the two one-sided cell restrictions remove. *)

Definition dsum (u v : list nat) : list nat :=
  u ++ map (fun x => (x + length u)%nat) v.

Lemma dsum_length : forall u v,
  length (dsum u v) = (length u + length v)%nat.
Proof. intros u v. unfold dsum. rewrite len_app, len_map_add. reflexivity. Qed.

Lemma dsum_nth_lo : forall u v t, (t < length u)%nat ->
  nth t (dsum u v) 0%nat = nth t u 0%nat.
Proof. intros u v t H. unfold dsum. apply nth_app1. exact H. Qed.

Lemma dsum_nth_hi : forall u v t,
  (length u <= t)%nat -> (t < length u + length v)%nat ->
  nth t (dsum u v) 0%nat = (nth (t - length u)%nat v 0%nat + length u)%nat.
Proof.
  intros u v t H1 H2. unfold dsum.
  rewrite nth_app2 by exact H1.
  assert (Hm : (t - length u < length v)%nat) by lia.
  erewrite nth_indep by (rewrite len_map_add; exact Hm).
  rewrite map_nth. reflexivity.
Qed.

Lemma dsum_val_lo : forall u v m t, is_perm u m -> (t < length u)%nat ->
  (nth t (dsum u v) 0%nat < length u)%nat.
Proof.
  intros u v m t Hp H. destruct Hp as [Hlen [_ Hlt]].
  rewrite dsum_nth_lo by exact H.
  rewrite Hlen. apply Hlt. apply nth_In. lia.
Qed.

Lemma dsum_val_hi : forall u v t,
  (length u <= t)%nat -> (t < length u + length v)%nat ->
  (length u <= nth t (dsum u v) 0%nat)%nat.
Proof. intros u v t H1 H2. rewrite dsum_nth_hi by assumption. lia. Qed.

Theorem dsum_avoids : forall u v m,
  is_perm u m -> ~ contains_132 u -> ~ contains_213 v ->
  ~ contains_1324 (dsum u v).
Proof.
  intros u v m Hu N132u N213v [i [j [k [l H]]]].
  destruct H as [Hij [Hjk [Hkl [Hlen [Hik [Hkj Hjl]]]]]].
  rewrite dsum_length in Hlen.
  destruct (Nat.lt_ge_cases j (length u)) as [Hj | Hj].
  - assert (Hi : (i < length u)%nat) by lia.
    assert (Hk : (k < length u)%nat).
    { destruct (Nat.lt_ge_cases k (length u)) as [Hk1|Hk2]; [exact Hk1|].
      exfalso.
      assert (A1 : (nth j (dsum u v) 0%nat < length u)%nat)
        by (apply (dsum_val_lo u v m); assumption).
      assert (A2 : (length u <= nth k (dsum u v) 0%nat)%nat)
        by (apply dsum_val_hi; lia).
      lia. }
    apply N132u. exists i, j, k.
    rewrite (dsum_nth_lo u v i Hi) in Hik.
    rewrite (dsum_nth_lo u v k Hk) in Hik, Hkj.
    rewrite (dsum_nth_lo u v j Hj) in Hkj.
    unfold has_132_at. repeat split; lia.
  - assert (Hk : (length u <= k)%nat) by lia.
    assert (Hl : (length u <= l)%nat) by lia.
    apply N213v.
    exists (j - length u)%nat, (k - length u)%nat, (l - length u)%nat.
    assert (Ej : nth j (dsum u v) 0%nat
               = (nth (j - length u)%nat v 0%nat + length u)%nat)
      by (apply dsum_nth_hi; lia).
    assert (Ek : nth k (dsum u v) 0%nat
               = (nth (k - length u)%nat v 0%nat + length u)%nat)
      by (apply dsum_nth_hi; lia).
    assert (El : nth l (dsum u v) 0%nat
               = (nth (l - length u)%nat v 0%nat + length u)%nat)
      by (apply dsum_nth_hi; lia).
    rewrite Ej, Ek in Hkj. rewrite Ej, El in Hjl.
    unfold has_213_at. repeat split; lia.
Qed.

(* Sharp: a 132 in the lower block with anything above it already makes a 1324. *)
Theorem dsum_132_gives_1324 : forall u v m,
  is_perm u m -> contains_132 u -> (0 < length v)%nat ->
  contains_1324 (dsum u v).
Proof.
  intros u v m Hu [i [j [k H]]] Hv.
  destruct H as [Hij [Hjk [Hk [Hik Hkj]]]].
  assert (Hvj : (nth j u 0%nat < length u)%nat).
  { destruct Hu as [Hlen [_ Hlt]]. rewrite Hlen. apply Hlt. apply nth_In. lia. }
  assert (El : nth (length u) (dsum u v) 0%nat
             = (nth (length u - length u)%nat v 0%nat + length u)%nat)
    by (apply dsum_nth_hi; lia).
  rewrite Nat.sub_diag in El.
  exists i, j, k, (length u). unfold has_1324_at.
  rewrite (dsum_nth_lo u v i) by lia.
  rewrite (dsum_nth_lo u v j) by lia.
  rewrite (dsum_nth_lo u v k) by lia.
  rewrite El, dsum_length. repeat split; lia.
Qed.

(* The chain decomposition.  Cells two or more apart are skew and adjacent ones
   alternate between sharing a row and a column; those are the hypotheses. *)

Section StaircaseChain.

Variable w : list nat.
Variable cell : nat -> nat.
Variable kind : nat -> bool.

(* cells two or more apart are skew: earlier is left of and above later *)
Hypothesis far : forall p q, (cell p + 2 <= cell q)%nat ->
  (p < q)%nat /\ (nth q w 0%nat < nth p w 0%nat)%nat.

(* adjacent cells alternate between sharing a row and sharing a column *)
Hypothesis alt : forall m, kind (S m) = negb (kind m).

Hypothesis sep_pos : forall m p q,
  kind m = true -> cell p = m -> cell q = S m -> (p < q)%nat.

(* The value-separation of the other adjacency is not needed: `far` already
   fixes both coordinates for cells two or more apart, and the one descent of an
   occurrence is ruled out by the position separation alone. *)

Lemma cell_close : forall p q,
  (p < q)%nat -> (nth p w 0%nat < nth q w 0%nat)%nat ->
  (cell p <= cell q + 1)%nat /\ (cell q <= cell p + 1)%nat.
Proof.
  intros p q Hpq Hval. split.
  - destruct (Nat.le_gt_cases (cell p) (cell q + 1)) as [H|H]; [exact H|].
    exfalso. destruct (far q p ltac:(lia)) as [Hqp _]. lia.
  - destruct (Nat.le_gt_cases (cell q) (cell p + 1)) as [H|H]; [exact H|].
    exfalso. destruct (far p q ltac:(lia)) as [_ Hv]. lia.
Qed.

(* Every pair of the occurrence is within one cell; the descent (j,k) needs the
   alternation. *)
Theorem chain_pairwise : forall i j k l, has_1324_at w i j k l ->
  (cell i <= cell j + 1)%nat /\ (cell j <= cell i + 1)%nat /\
  (cell i <= cell k + 1)%nat /\ (cell k <= cell i + 1)%nat /\
  (cell i <= cell l + 1)%nat /\ (cell l <= cell i + 1)%nat /\
  (cell j <= cell k + 1)%nat /\ (cell k <= cell j + 1)%nat /\
  (cell j <= cell l + 1)%nat /\ (cell l <= cell j + 1)%nat /\
  (cell k <= cell l + 1)%nat /\ (cell l <= cell k + 1)%nat.
Proof.
  intros i j k l H.
  destruct H as [Hij [Hjk [Hkl [Hlen [Hik [Hkj Hjl]]]]]].
  assert (Aij := cell_close i j ltac:(lia) ltac:(lia)).
  assert (Aik := cell_close i k ltac:(lia) ltac:(lia)).
  assert (Ail := cell_close i l ltac:(lia) ltac:(lia)).
  assert (Ajl := cell_close j l ltac:(lia) ltac:(lia)).
  assert (Akl := cell_close k l ltac:(lia) ltac:(lia)).
  assert (Hj1 : (cell j <= cell k + 1)%nat).
  { destruct (Nat.le_gt_cases (cell j) (cell k + 1)) as [H|H]; [exact H|].
    exfalso. destruct (far k j ltac:(lia)) as [Hkj2 _]. lia. }
  assert (Hk1 : (cell k <= cell j + 1)%nat).
  { destruct (Nat.le_gt_cases (cell k) (cell j + 1)) as [H|H]; [exact H|].
    exfalso.
    assert (Ei : cell i = S (cell j)) by lia.
    assert (Ek : cell k = S (S (cell j))) by lia.
    assert (El : cell l = S (cell j)) by lia.
    destruct (kind (cell j)) eqn:Tj.
    - assert (Hji : (j < i)%nat)
        by (apply (sep_pos (cell j) j i); [exact Tj | reflexivity | exact Ei]).
      lia.
    - assert (Tj1 : kind (S (cell j)) = true)
        by (rewrite alt, Tj; reflexivity).
      assert (Hlk : (l < k)%nat)
        by (apply (sep_pos (S (cell j)) l k); [exact Tj1 | exact El | exact Ek]).
      lia. }
  repeat split; lia.
Qed.

Theorem chain_local : forall i j k l, has_1324_at w i j k l ->
  (cell i <= cell j + 1)%nat /\ (cell j <= cell i + 1)%nat /\
  (cell j <= cell k + 1)%nat /\ (cell k <= cell j + 1)%nat /\
  (cell k <= cell l + 1)%nat /\ (cell l <= cell k + 1)%nat.
Proof.
  intros i j k l H. assert (P := chain_pairwise i j k l H).
  repeat split; lia.
Qed.

(* Four indices pairwise within one of each other span two consecutive cells. *)
Theorem chain_two_cells : forall i j k l, has_1324_at w i j k l ->
  exists c,
    (c <= cell i)%nat /\ (cell i <= S c)%nat /\
    (c <= cell j)%nat /\ (cell j <= S c)%nat /\
    (c <= cell k)%nat /\ (cell k <= S c)%nat /\
    (c <= cell l)%nat /\ (cell l <= S c)%nat.
Proof.
  intros i j k l H. assert (P := chain_pairwise i j k l H).
  exists (Nat.min (Nat.min (cell i) (cell j)) (Nat.min (cell k) (cell l))).
  repeat split; lia.
Qed.

(* Hence avoidance is decided two adjacent cells at a time. *)
Theorem chain_pairs_suffice :
  (forall c i j k l,
     (c <= cell i)%nat -> (cell i <= S c)%nat ->
     (c <= cell j)%nat -> (cell j <= S c)%nat ->
     (c <= cell k)%nat -> (cell k <= S c)%nat ->
     (c <= cell l)%nat -> (cell l <= S c)%nat ->
     ~ has_1324_at w i j k l) ->
  ~ contains_1324 w.
Proof.
  intros Hpair [i [j [k [l Hocc]]]].
  destruct (chain_two_cells i j k l Hocc)
    as [c [A1 [A2 [B1 [B2 [C1 [C2 [D1 D2]]]]]]]].
  exact (Hpair c i j k l A1 A2 B1 B2 C1 C2 D1 D2 Hocc).
Qed.

End StaircaseChain.

(* For f on a finite list and an involution s permuting it, Cov(f, f o s) is the
   variance of the symmetric part less that of the antisymmetric part. *)

Require Import Permutation.

Fixpoint csum (l : list Z) : Z :=
  match l with
  | nil => 0%Z
  | a :: r => (a + csum r)%Z
  end.

Lemma csum_perm : forall l1 l2, Permutation l1 l2 -> csum l1 = csum l2.
Proof.
  intros l1 l2 H.
  induction H as [|x l l' H IH|x y l|l1 l2 l3 H1 IH1 H2 IH2]; simpl;
    [reflexivity | rewrite IH; reflexivity | ring | rewrite IH1; exact IH2].
Qed.

Lemma csum_map_ext : forall (A : Type) (L : list A) (u v : A -> Z),
  (forall x, u x = v x) -> csum (map u L) = csum (map v L).
Proof.
  intros A L u v H. induction L as [|a L IH]; simpl;
    [reflexivity | rewrite H, IH; reflexivity].
Qed.

Lemma csum_map_add : forall (A : Type) (L : list A) (u v : A -> Z),
  csum (map (fun x => (u x + v x)%Z) L)
  = (csum (map u L) + csum (map v L))%Z.
Proof. intros A L u v. induction L as [|a L IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma csum_map_sub : forall (A : Type) (L : list A) (u v : A -> Z),
  csum (map (fun x => (u x - v x)%Z) L)
  = (csum (map u L) - csum (map v L))%Z.
Proof. intros A L u v. induction L as [|a L IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma csum_map_scal : forall (A : Type) (L : list A) (c : Z) (u : A -> Z),
  csum (map (fun x => (c * u x)%Z) L) = (c * csum (map u L))%Z.
Proof. intros A L c u. induction L as [|a L IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma csum_map_invol : forall (A : Type) (L : list A) (f : A -> Z) (s : A -> A),
  Permutation (map s L) L ->
  csum (map (fun x => f (s x)) L) = csum (map f L).
Proof.
  intros A L f s Hp.
  replace (map (fun x => f (s x)) L) with (map f (map s L))
    by (rewrite map_map; reflexivity).
  apply csum_perm. apply Permutation_map. exact Hp.
Qed.

(* Summing a Z-valued statistic over the fibres of a key recovers the total. *)

Definition foldZ {A : Type} (h : A -> Z) (l : list A) : Z :=
  fold_right (fun k acc => (h k + acc)%Z) 0%Z l.

Lemma foldZ_nil : forall (A : Type) (h : A -> Z), foldZ h nil = 0%Z.
Proof. reflexivity. Qed.

Lemma foldZ_cons : forall (A : Type) (h : A -> Z) (a : A) (l : list A),
  foldZ h (a :: l) = (h a + foldZ h l)%Z.
Proof. reflexivity. Qed.

Lemma foldZ_ext : forall (A : Type) (h1 h2 : A -> Z) (l : list A),
  (forall k, h1 k = h2 k) -> foldZ h1 l = foldZ h2 l.
Proof.
  intros A h1 h2 l H. induction l as [|a l IH]; [reflexivity|].
  rewrite !foldZ_cons, H, IH. reflexivity.
Qed.

Lemma foldZ_zero : forall (A : Type) (l : list A),
  foldZ (fun _ : A => 0%Z) l = 0%Z.
Proof.
  intros A l. induction l as [|a l IH]; [reflexivity|].
  rewrite foldZ_cons, IH. ring.
Qed.

Lemma foldZ_add : forall (A : Type) (h1 h2 : A -> Z) (l : list A),
  foldZ (fun k => (h1 k + h2 k)%Z) l = (foldZ h1 l + foldZ h2 l)%Z.
Proof.
  intros A h1 h2 l. induction l as [|a l IH]; [reflexivity|].
  rewrite !foldZ_cons, IH. ring.
Qed.

Lemma foldZ_pick_zero : forall (A : Type)
    (eqA : forall x y : A, {x = y} + {x <> y}) (a : A) (v : Z) (l : list A),
  ~ In a l -> foldZ (fun k => if eqA a k then v else 0%Z) l = 0%Z.
Proof.
  intros A eqA a v l. induction l as [|b l IH]; intro H; [reflexivity|].
  rewrite foldZ_cons.
  destruct (eqA a b) as [E|E]; [exfalso; apply H; left; symmetry; exact E|].
  rewrite IH by (intro C; apply H; right; exact C). ring.
Qed.

Lemma foldZ_pick_one : forall (A : Type)
    (eqA : forall x y : A, {x = y} + {x <> y}) (a : A) (v : Z) (l : list A),
  NoDup l -> In a l -> foldZ (fun k => if eqA a k then v else 0%Z) l = v.
Proof.
  intros A eqA a v l. induction l as [|b l IH]; intros Hnd Hin;
    [contradiction|].
  inversion Hnd as [|x r Hnb Hnd' Heq]; subst.
  rewrite foldZ_cons.
  destruct (eqA a b) as [E|E].
  - subst b. rewrite (foldZ_pick_zero A eqA a v l Hnb). ring.
  - rewrite IH; [ring | exact Hnd' |].
    destruct Hin as [Hc|Hc]; [exfalso; apply E; symmetry; exact Hc | exact Hc].
Qed.

Theorem csum_fibres : forall (A K : Type)
    (eqK : forall x y : K, {x = y} + {x <> y})
    (key : A -> K) (keys : list K) (l : list A) (g : A -> Z),
  NoDup keys ->
  (forall x, In x l -> In (key x) keys) ->
  csum (map g l)
  = foldZ (fun k =>
      csum (map g (filter (fun x => if eqK (key x) k then true else false) l)))
      keys.
Proof.
  intros A K eqK key keys l g Hnd.
  induction l as [|x l IH]; intro Hcov.
  - cbn [map csum filter]. rewrite foldZ_zero. reflexivity.
  - assert (Hx : In (key x) keys) by (apply Hcov; left; reflexivity).
    assert (Hl : forall y, In y l -> In (key y) keys)
      by (intros y Hy; apply Hcov; right; exact Hy).
    rewrite (foldZ_ext K _
      (fun k => ((if eqK (key x) k then g x else 0%Z)
                 + csum (map g (filter
                     (fun y => if eqK (key y) k then true else false) l)))%Z)
      keys).
    + rewrite foldZ_add, (foldZ_pick_one K eqK (key x) (g x) keys Hnd Hx),
              <- (IH Hl). cbn [map csum]. ring.
    + intro k. cbn [filter].
      destruct (eqK (key x) k); cbn [map csum]; ring.
Qed.

(* Everything is scaled by 4 so the halves in h and g stay in Z. *)
Theorem cov_symmetric_split :
  forall (A : Type) (L : list A) (f : A -> Z) (s : A -> A),
  Permutation (map s L) L ->
  (4 * (Z.of_nat (length L) * csum (map (fun x => (f x * f (s x))%Z) L)
        - csum (map f L) * csum (map f L))
   = (Z.of_nat (length L)
        * csum (map (fun x => ((f x + f (s x)) * (f x + f (s x)))%Z) L)
      - csum (map (fun x => (f x + f (s x))%Z) L)
        * csum (map (fun x => (f x + f (s x))%Z) L))
     - Z.of_nat (length L)
        * csum (map (fun x => ((f x - f (s x)) * (f x - f (s x)))%Z) L))%Z.
Proof.
  intros A L f s Hp.
  assert (Hsum : csum (map (fun x => (f x + f (s x))%Z) L)
               = (2 * csum (map f L))%Z).
  { rewrite csum_map_add, (csum_map_invol A L f s Hp). ring. }
  assert (Hdiff : (csum (map (fun x => ((f x + f (s x)) * (f x + f (s x)))%Z) L)
                 - csum (map (fun x => ((f x - f (s x)) * (f x - f (s x)))%Z) L)
                 = 4 * csum (map (fun x => (f x * f (s x))%Z) L))%Z).
  { rewrite <- csum_map_sub.
    rewrite (csum_map_ext A L _ (fun x => (4 * (f x * f (s x)))%Z))
      by (intro x; ring).
    apply csum_map_scal. }
  rewrite Hsum. nia.
Qed.

(* The two parts are orthogonal, so Var(f) = Var(h) + Var(g). *)
(* The involution condition is not needed: the summand is f^2 - (f o s)^2 and
   the permutation hypothesis alone makes the two halves sum equally.  `pinv` is
   involutive only on permutations, so it cannot discharge an unrestricted
   forall x, s (s x) = x. *)
Theorem sym_antisym_orthogonal :
  forall (A : Type) (L : list A) (f : A -> Z) (s : A -> A),
  Permutation (map s L) L ->
  csum (map (fun x => ((f x + f (s x)) * (f x - f (s x)))%Z) L) = 0%Z.
Proof.
  intros A L f s Hp.
  rewrite (csum_map_ext A L _
            (fun x => ((f x * f x) - (f (s x) * f (s x)))%Z))
    by (intro x; ring).
  rewrite csum_map_sub.
  rewrite (csum_map_invol A L (fun y => (f y * f y)%Z) s Hp).
  ring.
Qed.

Theorem var_splits :
  forall (A : Type) (L : list A) (f : A -> Z) (s : A -> A),
  Permutation (map s L) L ->
  (4 * (Z.of_nat (length L) * csum (map (fun x => (f x * f x)%Z) L)
        - csum (map f L) * csum (map f L))
   = (Z.of_nat (length L)
        * csum (map (fun x => ((f x + f (s x)) * (f x + f (s x)))%Z) L)
      - csum (map (fun x => (f x + f (s x))%Z) L)
        * csum (map (fun x => (f x + f (s x))%Z) L))
     + Z.of_nat (length L)
        * csum (map (fun x => ((f x - f (s x)) * (f x - f (s x)))%Z) L))%Z.
Proof.
  intros A L f s Hp.
  assert (Hsum : csum (map (fun x => (f x + f (s x))%Z) L)
               = (2 * csum (map f L))%Z).
  { rewrite csum_map_add, (csum_map_invol A L f s Hp). ring. }
  assert (Htot : (csum (map (fun x => ((f x + f (s x)) * (f x + f (s x)))%Z) L)
                + csum (map (fun x => ((f x - f (s x)) * (f x - f (s x)))%Z) L)
                = 4 * csum (map (fun x => (f x * f x)%Z) L))%Z).
  { rewrite <- csum_map_add.
    rewrite (csum_map_ext A L _
              (fun x => (2 * (f x * f x) + 2 * (f (s x) * f (s x)))%Z))
      by (intro x; ring).
    rewrite csum_map_add, !csum_map_scal.
    rewrite (csum_map_invol A L (fun y => (f y * f y)%Z) s Hp). ring. }
  rewrite Hsum. nia.
Qed.

(* Lagrange's identity over Z: the Cauchy-Schwarz defect is the sum of the
   squared two-by-two minors. *)

Definition dotp (l : list (Z * Z)) : Z :=
  csum (map (fun p => (fst p * snd p)%Z) l).
Definition sqf (l : list (Z * Z)) : Z :=
  csum (map (fun p => (fst p * fst p)%Z) l).
Definition sqs (l : list (Z * Z)) : Z :=
  csum (map (fun p => (snd p * snd p)%Z) l).

(* the squared two-by-two minors, over the pairs taken in order *)
Fixpoint minors (l : list (Z * Z)) : Z :=
  match l with
  | nil => 0
  | p :: r =>
      csum (map (fun q => ((fst p * snd q - fst q * snd p)
                           * (fst p * snd q - fst q * snd p))%Z) r)
      + minors r
  end.

Lemma csum_nonneg : forall l, (forall x, In x l -> 0 <= x) -> 0 <= csum l.
Proof.
  induction l as [|a l IH]; intro H; cbn [csum]; [lia|].
  assert (Ha : 0 <= a) by (apply H; left; reflexivity).
  assert (Hl : 0 <= csum l)
    by (apply IH; intros x Hx; apply H; right; exact Hx).
  lia.
Qed.

Lemma z_sq_nonneg : forall d : Z, 0 <= d * d.
Proof. intro d. destruct (Z.le_ge_cases 0 d); nia. Qed.

Lemma minors_nonneg : forall l, 0 <= minors l.
Proof.
  induction l as [|p r IH]; cbn [minors]; [lia|].
  assert (H : 0 <= csum (map (fun q => ((fst p * snd q - fst q * snd p)
                                * (fst p * snd q - fst q * snd p))%Z) r)).
  { apply csum_nonneg. intros x Hx. apply in_map_iff in Hx.
    destruct Hx as [q [Hq _]]. rewrite <- Hq. cbn beta. apply z_sq_nonneg. }
  lia.
Qed.

(* the head against the tail, expanded *)
Lemma minors_head : forall a b r,
  csum (map (fun q => ((a * snd q - fst q * b) * (a * snd q - fst q * b))%Z) r)
  = (a * a * sqs r - 2 * a * b * dotp r + b * b * sqf r)%Z.
Proof.
  intros a b. unfold dotp, sqf, sqs.
  induction r as [|q r IH]; cbn [csum map]; [ring|]. rewrite IH. ring.
Qed.

Theorem lagrange_identity : forall l,
  (sqf l * sqs l - dotp l * dotp l)%Z = minors l.
Proof.
  induction l as [|p r IH].
  - unfold dotp, sqf, sqs. cbn [csum map minors]. ring.
  - destruct p as [a b]. cbn [minors fst snd].
    rewrite (minors_head a b r), <- IH.
    unfold dotp, sqf, sqs. cbn [csum map fst snd]. ring.
Qed.

Theorem cauchy_schwarz : forall l, (dotp l * dotp l <= sqf l * sqs l)%Z.
Proof.
  intro l. assert (H := lagrange_identity l).
  assert (K := minors_nonneg l). lia.
Qed.

(* Weighted Cauchy-Schwarz with denominators cleared:
   (prod n_i)(sum S_i)^2 <= (sum n_i) * sum_i S_i^2 prod_{k<>i} n_k. *)

Fixpoint nprodz (l : list (nat * Z)) : Z :=
  match l with nil => 1 | p :: r => Z.of_nat (fst p) * nprodz r end.

Fixpoint nsumz (l : list (nat * Z)) : Z :=
  match l with nil => 0 | p :: r => Z.of_nat (fst p) + nsumz r end.

Fixpoint ssumz (l : list (nat * Z)) : Z :=
  match l with nil => 0 | p :: r => snd p + ssumz r end.

(* sum_i S_i^2 prod_{k <> i} n_k, without ever forming a quotient *)
Fixpoint qsumz (l : list (nat * Z)) : Z :=
  match l with
  | nil => 0
  | p :: r => Z.of_nat (fst p) * qsumz r + nprodz r * snd p * snd p
  end.

Definition posw (l : list (nat * Z)) : Prop :=
  forall p, In p l -> (1 <= fst p)%nat.

Lemma nsumz_nonneg : forall l, 0 <= nsumz l.
Proof. induction l as [|p r IH]; cbn [nsumz]; lia. Qed.

Lemma nprodz_pos : forall l, posw l -> 1 <= nprodz l.
Proof.
  induction l as [|p r IH]; intro H; cbn [nprodz]; [lia|].
  assert (Hp : (1 <= fst p)%nat) by (apply H; left; reflexivity).
  assert (Hr : 1 <= nprodz r)
    by (apply IH; intros q Hq; apply H; right; exact Hq).
  assert (Hz : 1 <= Z.of_nat (fst p)) by lia.
  nia.
Qed.

Lemma nprodz_cons : forall p r, nprodz (p :: r) = Z.of_nat (fst p) * nprodz r.
Proof. reflexivity. Qed.
Lemma nsumz_cons : forall p r, nsumz (p :: r) = Z.of_nat (fst p) + nsumz r.
Proof. reflexivity. Qed.
Lemma ssumz_cons : forall p r, ssumz (p :: r) = snd p + ssumz r.
Proof. reflexivity. Qed.
Lemma qsumz_cons : forall p r,
  qsumz (p :: r) = Z.of_nat (fst p) * qsumz r + nprodz r * snd p * snd p.
Proof. reflexivity. Qed.

Theorem weighted_cauchy_schwarz : forall l, posw l ->
  nprodz l * ssumz l * ssumz l <= nsumz l * qsumz l.
Proof.
  induction l as [|p r IH]; intro H.
  - cbn [nprodz nsumz ssumz qsumz]. lia.
  - assert (Hposr : posw r) by (intros x Hx; apply H; right; exact Hx).
    assert (Hn : (1 <= fst p)%nat) by (apply H; left; reflexivity).
    assert (HIH := IH Hposr).
    destruct r as [|q r'].
    + cbn [nprodz nsumz ssumz qsumz]. nia.
    + assert (Hq : (1 <= fst q)%nat) by (apply H; right; left; reflexivity).
      rewrite nprodz_cons, nsumz_cons, ssumz_cons, qsumz_cons.
      set (n := Z.of_nat (fst p)). set (sv := snd p).
      set (N := nsumz (q :: r')) in *. set (P := nprodz (q :: r')) in *.
      set (Q := qsumz (q :: r')) in *. set (T := ssumz (q :: r')) in *.
      assert (Hnz : 1 <= n) by (unfold n; lia).
      assert (HP : 1 <= P) by (unfold P; apply nprodz_pos; exact Hposr).
      assert (HNpos : 1 <= N).
      { unfold N. rewrite nsumz_cons.
        assert (K := nsumz_nonneg r'). lia. }
      assert (HD : 0 <= N * Q - P * T * T) by lia.
      assert (Key : N * ((n + N) * (n * Q + P * sv * sv)
                         - n * P * (sv + T) * (sv + T))
                  = (N * n) * (N * Q - P * T * T)
                    + (n * n) * (N * Q - P * T * T)
                    + P * ((n * T - N * sv) * (n * T - N * sv))) by ring.
      assert (H1 : 0 <= (N * n) * (N * Q - P * T * T))
        by (apply Z.mul_nonneg_nonneg; [nia | exact HD]).
      assert (H2 : 0 <= (n * n) * (N * Q - P * T * T))
        by (apply Z.mul_nonneg_nonneg; [nia | exact HD]).
      assert (H3 : 0 <= P * ((n * T - N * sv) * (n * T - N * sv)))
        by (apply Z.mul_nonneg_nonneg;
            [lia | apply (z_sq_nonneg (n * T - N * sv))]).
      assert (H4 : 0 <= N * ((n + N) * (n * Q + P * sv * sv)
                             - n * P * (sv + T) * (sv + T))) by lia.
      destruct (Z.le_gt_cases 0 ((n + N) * (n * Q + P * sv * sv)
                                 - n * P * (sv + T) * (sv + T))) as [HE|HE];
        [lia|].
      exfalso. nia.
Qed.

(* The stratified split, with the stratum sizes multiplied through to clear the
   denominators in N P - S^2 = within + between. *)

Record stratum := mkStratum { st_n : nat ; st_S : Z ; st_P : Z }.

Definition proj_ns (l : list stratum) : list (nat * Z) :=
  map (fun s => (st_n s, st_S s)) l.

Fixpoint stP (l : list stratum) : Z :=
  match l with nil => 0 | s :: r => st_P s + stP r end.

(* sum_i (prod_k n_k / n_i)(n_i P_i - S_i^2), formed without a quotient *)
Fixpoint defw (l : list stratum) : Z :=
  match l with
  | nil => 0
  | s :: r => nprodz (proj_ns r)
                * (Z.of_nat (st_n s) * st_P s - st_S s * st_S s)
              + Z.of_nat (st_n s) * defw r
  end.

Lemma proj_ns_cons : forall s r,
  proj_ns (s :: r) = (st_n s, st_S s) :: proj_ns r.
Proof. reflexivity. Qed.

Lemma defw_closed : forall l,
  defw l = nprodz (proj_ns l) * stP l - qsumz (proj_ns l).
Proof.
  induction l as [|s r IH]; [reflexivity|].
  cbn [defw stP]. rewrite proj_ns_cons, nprodz_cons, qsumz_cons.
  cbn [fst snd]. rewrite IH. ring.
Qed.

Theorem strata_split : forall l,
  nprodz (proj_ns l)
    * (nsumz (proj_ns l) * stP l - ssumz (proj_ns l) * ssumz (proj_ns l))
  = nsumz (proj_ns l) * defw l
    + (nsumz (proj_ns l) * qsumz (proj_ns l)
       - nprodz (proj_ns l) * ssumz (proj_ns l) * ssumz (proj_ns l)).
Proof. intro l. rewrite defw_closed. ring. Qed.

Corollary between_nonneg : forall l, posw (proj_ns l) ->
  0 <= nsumz (proj_ns l) * qsumz (proj_ns l)
       - nprodz (proj_ns l) * ssumz (proj_ns l) * ssumz (proj_ns l).
Proof.
  intros l H. assert (K := weighted_cauchy_schwarz (proj_ns l) H). lia.
Qed.

Corollary cov_ge_within : forall l, posw (proj_ns l) ->
  nsumz (proj_ns l) * defw l
  <= nprodz (proj_ns l)
       * (nsumz (proj_ns l) * stP l - ssumz (proj_ns l) * ssumz (proj_ns l)).
Proof.
  intros l H. assert (K := between_nonneg l H).
  assert (E := strata_split l). lia.
Qed.

(* Only the within deficit matters, not its sign. *)
Corollary cov_nonneg_of_within_bounded : forall l, posw (proj_ns l) ->
  - (nsumz (proj_ns l) * defw l)
  <= nsumz (proj_ns l) * qsumz (proj_ns l)
     - nprodz (proj_ns l) * ssumz (proj_ns l) * ssumz (proj_ns l) ->
  0 <= nprodz (proj_ns l)
         * (nsumz (proj_ns l) * stP l - ssumz (proj_ns l) * ssumz (proj_ns l)).
Proof.
  intros l H Hb. assert (E := strata_split l). lia.
Qed.

(* The covariance as an ordered-pair sum, equal to N sum f (f o s) - (sum f)^2
   up to a factor of two. *)

Definition csum2 {A : Type} (L : list A) (g : A -> A -> Z) : Z :=
  csum (map (fun x => csum (map (fun y => g x y) L)) L).

Lemma csum_map_lin4 : forall (A : Type) (L : list A) (u v w : A -> Z)
    (c1 c2 c3 c0 : Z),
  csum (map (fun x => (c1 * u x + c2 * v x + c3 * w x + c0)%Z) L)
  = (c1 * csum (map u L) + c2 * csum (map v L) + c3 * csum (map w L)
     + Z.of_nat (length L) * c0)%Z.
Proof.
  intros A L u v w c1 c2 c3 c0.
  induction L as [|a L IH]; cbn [csum map length]; [ring|].
  rewrite IH, Nat2Z.inj_succ. ring.
Qed.

(* the inner sum, at a fixed left coordinate *)
Lemma csum_inner : forall (A : Type) (L : list A) (f : A -> Z) (s : A -> A)
    (a b : Z),
  csum (map (fun y => ((a - f y) * (b - f (s y)))%Z) L)
  = (Z.of_nat (length L) * (a * b) - a * csum (map (fun y => f (s y)) L)
     - b * csum (map f L) + csum (map (fun y => (f y * f (s y))%Z) L))%Z.
Proof.
  intros A L f s a b.
  induction L as [|z L IH]; cbn [csum map length]; [ring|].
  rewrite IH, Nat2Z.inj_succ. ring.
Qed.

Theorem cov_pair_form :
  forall (A : Type) (L : list A) (f : A -> Z) (s : A -> A),
  Permutation (map s L) L ->
  (2 * (Z.of_nat (length L) * csum (map (fun x => (f x * f (s x))%Z) L)
        - csum (map f L) * csum (map f L))
   = csum2 L (fun x y => ((f x - f y) * (f (s x) - f (s y)))%Z))%Z.
Proof.
  intros A L f s Hp.
  assert (Hs : csum (map (fun y => f (s y)) L) = csum (map f L))
    by (apply (csum_map_invol A L f s Hp)).
  unfold csum2.
  rewrite (csum_map_ext A L
    (fun x => csum (map (fun y => ((f x - f y) * (f (s x) - f (s y)))%Z) L))
    (fun x => (Z.of_nat (length L) * ((f x * f (s x))%Z)
               + (Z.opp (csum (map f L))) * (f x)
               + (Z.opp (csum (map f L))) * (f (s x))
               + csum (map (fun y => (f y * f (s y))%Z) L))%Z)).
  2:{ intro x. rewrite (csum_inner A L f s (f x) (f (s x))), Hs. ring. }
  rewrite (csum_map_lin4 A L
    (fun x => (f x * f (s x))%Z) f (fun x => f (s x))
    (Z.of_nat (length L)) (Z.opp (csum (map f L)))
    (Z.opp (csum (map f L))) (csum (map (fun y => (f y * f (s y))%Z) L))).
  rewrite Hs. ring.
Qed.

(* Hence the two statements of the conjecture are interchangeable. *)
Corollary cov_iff_pair_sum :
  forall (A : Type) (L : list A) (f : A -> Z) (s : A -> A),
  Permutation (map s L) L ->
  ((0 <= Z.of_nat (length L) * csum (map (fun x => (f x * f (s x))%Z) L)
         - csum (map f L) * csum (map f L))%Z
   <-> (0 <= csum2 L (fun x y => ((f x - f y) * (f (s x) - f (s y)))%Z))%Z).
Proof.
  intros A L f s Hp. assert (H := cov_pair_form A L f s Hp). lia.
Qed.

(* Positive quadrant dependence gives the Chebyshev step termwise, through the
   layer-cake decomposition, with no ordering of f against g. *)

Definition gtb1 (a x : nat) : nat := if (a <? x)%nat then 1%nat else 0%nat.

Fixpoint sumn (n : nat) (h : nat -> nat) : nat :=
  match n with O => 0%nat | S k => (sumn k h + h k)%nat end.

Lemma sumn_zero : forall n, sumn n (fun _ => 0%nat) = 0%nat.
Proof. induction n as [|n IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma sumn_extn : forall n (h h' : nat -> nat),
  (forall a, h a = h' a) -> sumn n h = sumn n h'.
Proof.
  induction n as [|n IH]; intros h h' H; simpl; [reflexivity|].
  rewrite (IH h h' H), H. reflexivity.
Qed.

Lemma sumn_len : forall n (h h' : nat -> nat),
  (forall a, (h a <= h' a)%nat) -> (sumn n h <= sumn n h')%nat.
Proof.
  induction n as [|n IH]; intros h h' H; simpl; [lia|].
  assert (A := IH h h' H). assert (B := H n). lia.
Qed.

Lemma sumn_addn : forall n (h h' : nat -> nat),
  sumn n (fun a => (h a + h' a)%nat) = (sumn n h + sumn n h')%nat.
Proof.
  induction n as [|n IH]; intros h h'; simpl; [reflexivity|]. rewrite IH. lia.
Qed.

Lemma sumn_scaln : forall n c (h : nat -> nat),
  sumn n (fun a => (c * h a)%nat) = (c * sumn n h)%nat.
Proof.
  induction n as [|n IH]; intros c h; simpl; [lia|]. rewrite IH. lia.
Qed.

Lemma sumn_prodn : forall n (h k : nat -> nat),
  sumn n (fun a => sumn n (fun b => (h a * k b)%nat)) = (sumn n h * sumn n k)%nat.
Proof.
  intros n h k.
  rewrite (sumn_extn n (fun a => sumn n (fun b => (h a * k b)%nat))
                       (fun a => (sumn n k * h a)%nat))
    by (intro a; rewrite (sumn_scaln n (h a) k); lia).
  rewrite (sumn_scaln n (sumn n k) h). lia.
Qed.

(* The layer cake: a value is the number of thresholds it exceeds. *)
Lemma layer_cake : forall M x, sumn M (fun a => gtb1 a x) = Nat.min x M.
Proof.
  induction M as [|M IH]; intro x; simpl; [lia|].
  rewrite IH. unfold gtb1. destruct (Nat.ltb_spec M x); lia.
Qed.

Fixpoint cnt2 (a b : nat) (l : list (nat * nat)) : nat :=
  match l with
  | nil => 0%nat
  | p :: r => ((gtb1 a (fst p) * gtb1 b (snd p)) + cnt2 a b r)%nat
  end.

Fixpoint cntA (a : nat) (l : list (nat * nat)) : nat :=
  match l with nil => 0%nat | p :: r => (gtb1 a (fst p) + cntA a r)%nat end.

Fixpoint cntB (b : nat) (l : list (nat * nat)) : nat :=
  match l with nil => 0%nat | p :: r => (gtb1 b (snd p) + cntB b r)%nat end.

Fixpoint sumA (l : list (nat * nat)) : nat :=
  match l with nil => 0%nat | p :: r => (fst p + sumA r)%nat end.

Fixpoint sumB (l : list (nat * nat)) : nat :=
  match l with nil => 0%nat | p :: r => (snd p + sumB r)%nat end.

Fixpoint sumAB (l : list (nat * nat)) : nat :=
  match l with nil => 0%nat | p :: r => ((fst p * snd p) + sumAB r)%nat end.

Lemma layer_A : forall M l, (forall p, In p l -> (fst p <= M)%nat) ->
  sumn M (fun a => cntA a l) = sumA l.
Proof.
  intros M l. induction l as [|p r IH]; intro H; simpl.
  - apply sumn_zero.
  - rewrite sumn_addn, (layer_cake M (fst p)),
            (IH ltac:(intros q Hq; apply H; right; exact Hq)).
    assert (fst p <= M)%nat by (apply H; left; reflexivity). lia.
Qed.

Lemma layer_B : forall M l, (forall p, In p l -> (snd p <= M)%nat) ->
  sumn M (fun b => cntB b l) = sumB l.
Proof.
  intros M l. induction l as [|p r IH]; intro H; simpl.
  - apply sumn_zero.
  - rewrite sumn_addn, (layer_cake M (snd p)),
            (IH ltac:(intros q Hq; apply H; right; exact Hq)).
    assert (snd p <= M)%nat by (apply H; left; reflexivity). lia.
Qed.

Lemma layer_AB : forall M l,
  (forall p, In p l -> (fst p <= M)%nat /\ (snd p <= M)%nat) ->
  sumn M (fun a => sumn M (fun b => cnt2 a b l)) = sumAB l.
Proof.
  intros M l. induction l as [|p r IH]; intro H; simpl.
  - rewrite (sumn_extn M (fun a => sumn M (fun _ => 0%nat)) (fun _ => 0%nat))
      by (intro a; apply sumn_zero).
    apply sumn_zero.
  - assert (Hp : (fst p <= M)%nat /\ (snd p <= M)%nat)
      by (apply H; left; reflexivity).
    destruct Hp as [Hp1 Hp2].
    rewrite (sumn_extn M
      (fun a => sumn M (fun b => ((gtb1 a (fst p) * gtb1 b (snd p)) + cnt2 a b r)%nat))
      (fun a => ((gtb1 a (fst p) * Nat.min (snd p) M) + sumn M (fun b => cnt2 a b r))%nat)).
    + rewrite sumn_addn.
      rewrite (sumn_extn M (fun a => (gtb1 a (fst p) * Nat.min (snd p) M)%nat)
                           (fun a => (Nat.min (snd p) M * gtb1 a (fst p))%nat))
        by (intro a; lia).
      rewrite (sumn_scaln M (Nat.min (snd p) M) (fun a => gtb1 a (fst p))).
      rewrite (layer_cake M (fst p)).
      rewrite (IH ltac:(intros q Hq; apply H; right; exact Hq)).
      rewrite (Nat.min_l (snd p) M Hp2), (Nat.min_l (fst p) M Hp1). lia.
    + intro a. rewrite sumn_addn.
      rewrite (sumn_scaln M (gtb1 a (fst p)) (fun b => gtb1 b (snd p))).
      rewrite (layer_cake M (snd p)). reflexivity.
Qed.

(* At l the pairs (d_A b, d_C b) over Av(132)_m this reads D(m,m)^2 <= Cat(m) T(m,m,m). *)
Theorem pqd_chebyshev : forall M l,
  (forall p, In p l -> (fst p <= M)%nat /\ (snd p <= M)%nat) ->
  (forall a b, (cntA a l * cntB b l <= length l * cnt2 a b l)%nat) ->
  (sumA l * sumB l <= length l * sumAB l)%nat.
Proof.
  intros M l Hb Hpqd.
  rewrite <- (layer_A M l ltac:(intros p Hp; apply (Hb p Hp))).
  rewrite <- (layer_B M l ltac:(intros p Hp; apply (Hb p Hp))).
  rewrite <- (layer_AB M l Hb).
  rewrite <- sumn_prodn.
  rewrite <- (sumn_scaln M (length l) (fun a => sumn M (fun b => cnt2 a b l))).
  apply sumn_len. intro a.
  rewrite <- (sumn_scaln M (length l) (fun b => cnt2 a b l)).
  apply sumn_len. intro b. apply Hpqd.
Qed.

(* The case with equal coordinate totals. *)
Corollary pqd_square : forall M l,
  (forall p, In p l -> (fst p <= M)%nat /\ (snd p <= M)%nat) ->
  (forall a b, (cntA a l * cntB b l <= length l * cnt2 a b l)%nat) ->
  sumB l = sumA l ->
  (sumA l * sumA l <= length l * sumAB l)%nat.
Proof.
  intros M l Hb Hpqd Heq.
  rewrite <- Heq at 2. apply (pqd_chebyshev M l Hb Hpqd).
Qed.

(* Rearranging the suffix downward injects each pattern's words into the
   decreasing pattern's, so N_dec - N_sigma is non-negative. *)

Fixpoint dins (x : nat) (l : list nat) : list nat :=
  match l with
  | nil => x :: nil
  | a :: r => if Nat.ltb a x then x :: a :: r else a :: dins x r
  end.

Fixpoint dsort (l : list nat) : list nat :=
  match l with
  | nil => nil
  | a :: r => dins a (dsort r)
  end.

Fixpoint sortedD (l : list nat) : Prop :=
  match l with
  | nil => True
  | a :: r => (forall y, In y r -> (y <= a)%nat) /\ sortedD r
  end.

Lemma dins_in : forall x l y, In y (dins x l) <-> (x = y \/ In y l).
Proof.
  intros x l. induction l as [|a r IH]; intro y; simpl.
  - tauto.
  - destruct (Nat.ltb a x) eqn:E; simpl; [tauto|]. rewrite IH. tauto.
Qed.

Lemma dins_perm : forall x l, Permutation (x :: l) (dins x l).
Proof.
  intros x l. induction l as [|a r IH]; simpl; [apply Permutation_refl|].
  destruct (Nat.ltb a x) eqn:E; [apply Permutation_refl|].
  eapply Permutation_trans; [apply perm_swap|].
  apply perm_skip. exact IH.
Qed.

Lemma dsort_perm : forall l, Permutation l (dsort l).
Proof.
  induction l as [|a r IH]; simpl; [apply Permutation_refl|].
  eapply Permutation_trans; [apply perm_skip; exact IH | apply dins_perm].
Qed.

Lemma dins_sortedD : forall x l, sortedD l -> sortedD (dins x l).
Proof.
  intros x l. induction l as [|a r IH]; intro H; simpl.
  - split; [intros y []| exact I].
  - destruct H as [Ha Hr].
    destruct (Nat.ltb a x) eqn:E; simpl.
    + apply Nat.ltb_lt in E. split; [| split; [exact Ha | exact Hr]].
      intros y [Hy|Hy]; [lia | apply Ha in Hy; lia].
    + apply Nat.ltb_ge in E. split; [| apply IH; exact Hr].
      intros y Hy. apply dins_in in Hy. destruct Hy as [Hy|Hy];
        [lia | apply Ha; exact Hy].
Qed.

Lemma dsort_sortedD : forall l, sortedD (dsort l).
Proof.
  induction l as [|a r IH]; simpl; [exact I | apply dins_sortedD; exact IH].
Qed.

Lemma sortedD_nth : forall l, sortedD l ->
  forall t t', (t < t')%nat -> (t' < length l)%nat ->
  (nth t' l 0%nat <= nth t l 0%nat)%nat.
Proof.
  induction l as [|a r IH]; intros H t t' Ht Ht'; simpl in Ht'; [lia|].
  destruct H as [Ha Hr].
  destruct t as [|t]; simpl.
  - destruct t' as [|t']; [lia|]. simpl.
    apply Ha. apply nth_In. lia.
  - destruct t' as [|t']; [lia|]. simpl.
    apply IH; [exact Hr | lia | lia].
Qed.

(* With distinct entries the descending order is strict. *)
Lemma sortedD_strict : forall l, NoDup l -> sortedD l ->
  forall t t', (t < t')%nat -> (t' < length l)%nat ->
  (nth t' l 0%nat < nth t l 0%nat)%nat.
Proof.
  intros l Hnd Hs t t' Ht Ht'.
  assert (Hle : (nth t' l 0%nat <= nth t l 0%nat)%nat)
    by (apply sortedD_nth; assumption).
  assert (Hne : nth t' l 0%nat <> nth t l 0%nat).
  { intro E. apply (proj1 (NoDup_nth l 0%nat) Hnd t' t) in E; lia. }
  lia.
Qed.

(* Open statements, Admitted.  Nothing above depends on them. *)

Require Import QArith Qabs.

Definition Qn (n : nat) : Q := inject_Z (Z.of_nat n).

Fixpoint binomN (n k : nat) : nat :=
  match n, k with
  | _, O => 1%nat
  | O, S _ => 0%nat
  | S n', S k' => (binomN n' k' + binomN n' (S k'))%nat
  end.

Fixpoint factn (n : nat) : nat :=
  match n with O => 1%nat | S m => (n * factn m)%nat end.

Fixpoint polyQ (c : list Q) (x : Q) : Q :=
  match c with [] => 0 | a :: r => Qplus a (Qmult x (polyQ r x)) end.

(* i-th backward difference of a polynomial, evaluated at x *)
Fixpoint delta (i : nat) (c : list Q) (x : Q) : Q :=
  match i with
  | O => polyQ c x
  | S i' => Qminus (delta i' c x) (delta i' c (Qminus x 1))
  end.

Fixpoint sumQn (n : nat) (f : nat -> Q) : Q :=
  match n with O => f O | S m => Qplus (sumQn m f) (f (S m)) end.

Definition altQ (t : nat) : Q := if Nat.even t then 1 else Qopp 1.

(* Coefficientwise arithmetic on coefficient lists. *)

Fixpoint padd (a b : list Q) : list Q :=
  match a, b with
  | nil, b' => b'
  | a', nil => a'
  | u :: a', v :: b' => Qplus u v :: padd a' b'
  end.

Fixpoint psub (a b : list Q) : list Q :=
  match a, b with
  | nil, b' => map Qopp b'
  | a', nil => a'
  | u :: a', v :: b' => Qminus u v :: psub a' b'
  end.

Definition pcadd (a : Q) (u : list Q) : list Q :=
  match u with nil => a :: nil | u0 :: u' => Qplus a u0 :: u' end.

Lemma polyQ_map_opp : forall b x, polyQ (map Qopp b) x == Qopp (polyQ b x).
Proof.
  induction b as [|v b IH]; intro x; simpl; [ring|]. rewrite IH. ring.
Qed.

Lemma padd_spec : forall a b x, polyQ (padd a b) x == Qplus (polyQ a x) (polyQ b x).
Proof.
  induction a as [|u a IH]; intros b x; simpl; [ring|].
  destruct b as [|v b]; simpl; [ring|]. rewrite IH. ring.
Qed.

Lemma psub_spec : forall a b x, polyQ (psub a b) x == Qminus (polyQ a x) (polyQ b x).
Proof.
  induction a as [|u a IH]; intros b x; simpl.
  - rewrite polyQ_map_opp. ring.
  - destruct b as [|v b]; simpl; [ring|]. rewrite IH. ring.
Qed.

Lemma pcadd_spec : forall a u x, polyQ (pcadd a u) x == Qplus a (polyQ u x).
Proof. intros a u x. destruct u as [|u0 u]; simpl; ring. Qed.

Lemma padd_len : forall a b, length (padd a b) = Nat.max (length a) (length b).
Proof.
  induction a as [|u a IH]; intro b; simpl; [reflexivity|].
  destruct b as [|v b]; simpl; [lia|]. rewrite IH. lia.
Qed.

Lemma psub_len : forall a b, length (psub a b) = Nat.max (length a) (length b).
Proof.
  induction a as [|u a IH]; intro b; simpl.
  - rewrite len_map. lia.
  - destruct b as [|v b]; simpl; [lia|]. rewrite IH. lia.
Qed.

Lemma pcadd_len : forall a u, length (pcadd a u) = Nat.max 1 (length u).
Proof. intros a u. destruct u; simpl; lia. Qed.

(* The coefficient list of f(x-1). *)
Fixpoint shiftp (c : list Q) : list Q :=
  match c with
  | nil => nil
  | a :: r => pcadd a (psub (0%Q :: shiftp r) (shiftp r))
  end.

Lemma shiftp_len : forall c, length (shiftp c) = length c.
Proof.
  induction c as [|a c IH]; [reflexivity|].
  cbn [shiftp]. rewrite pcadd_len, psub_len. cbn [length].
  rewrite IH. lia.
Qed.

Lemma shiftp_spec : forall c x, polyQ (shiftp c) x == polyQ c (Qminus x 1).
Proof.
  induction c as [|a c IH]; intro x; [simpl; ring|].
  cbn [shiftp]. rewrite pcadd_spec, psub_spec.
  cbn [polyQ]. rewrite IH. ring.
Qed.

(* Delta drops the degree by one. *)
Lemma diff_drop : forall n c, (length c <= S n)%nat ->
  exists c', (length c' <= n)%nat /\
    forall x, polyQ c' x == Qminus (polyQ c x) (polyQ c (Qminus x 1)).
Proof.
  induction n as [|n IH]; intros c Hc.
  - exists nil. split; [simpl; lia|]. intro x.
    destruct c as [|a c]; simpl; [ring|].
    destruct c as [|b c]; simpl in *; [ring | lia].
  - destruct c as [|a r].
    + exists nil. split; [simpl; lia|]. intro x. simpl. ring.
    + simpl in Hc.
      destruct (IH r ltac:(lia)) as [r' [Hlen Hspec]].
      exists (padd (0%Q :: r') (shiftp r)). split.
      * rewrite padd_len, shiftp_len. cbn [length].
        apply Nat.max_lub; lia.
      * intro x. rewrite padd_spec, shiftp_spec.
        cbn [polyQ]. rewrite Hspec. cbn [polyQ]. ring.
Qed.

(* Delta^(i+1) f = Delta^i (Delta f), so the outer and inner readings agree. *)
Lemma delta_shift_in : forall i c c',
  (forall y, polyQ c' y == Qminus (polyQ c y) (polyQ c (Qminus y 1))) ->
  forall x, delta i c' x == delta (S i) c x.
Proof.
  induction i as [|i IH]; intros c c' H x; simpl.
  - apply H.
  - rewrite (IH c c' H x), (IH c c' H (Qminus x 1)). reflexivity.
Qed.

Theorem delta_vanishes : forall n c x,
  (length c <= S n)%nat -> delta (S n) c x == 0.
Proof.
  induction n as [|n IH]; intros c x Hc.
  - simpl. destruct c as [|a c]; simpl; [ring|].
    destruct c as [|b c]; simpl in *; [ring | lia].
  - destruct (diff_drop (S n) c Hc) as [c' [Hlen Hspec]].
    rewrite <- (delta_shift_in (S n) c c' Hspec x).
    apply IH. exact Hlen.
Qed.

(* Telescoping: Delta^i f(x-1) = Delta^i f(x) - Delta^(i+1) f(x). *)
Lemma sum_telescope : forall n c x,
  sumQn n (fun i => delta i c (Qminus x 1))
  == Qminus (polyQ c x) (delta (S n) c x).
Proof.
  induction n as [|n IH]; intros c x.
  - cbn [sumQn delta]. ring.
  - cbn [sumQn]. rewrite (IH c x). cbn [delta]. ring.
Qed.

(* Summing the backward differences at x-1 recovers the polynomial at x. *)
Theorem sum_delta : forall n c x,
  (length c <= S n)%nat ->
  sumQn n (fun i => delta i c (Qminus x 1)) == polyQ c x.
Proof.
  intros n c x Hc. rewrite sum_telescope, (delta_vanishes n c x Hc). ring.
Qed.

Lemma delta_congr : forall i a b x,
  (forall y, polyQ a y == polyQ b y) -> delta i a x == delta i b x.
Proof.
  induction i as [|i IH]; intros a b x H; simpl; [apply H|].
  rewrite (IH a b x H), (IH a b (Qminus x 1) H). reflexivity.
Qed.

Lemma delta_psub : forall i a b x,
  delta i (psub a b) x == Qminus (delta i a x) (delta i b x).
Proof.
  induction i as [|i IH]; intros a b x; simpl; [apply psub_spec|].
  rewrite (IH a b x), (IH a b (Qminus x 1)). ring.
Qed.

Lemma polyQ_zero_list : forall c x,
  (forall j, nth j c 0%Q == 0) -> polyQ c x == 0.
Proof.
  induction c as [|u c IH]; intros x H; simpl; [ring|].
  rewrite (IH x (fun j => H (S j))).
  assert (Hu : u == 0) by apply (H O). rewrite Hu. ring.
Qed.

Lemma polyQ_firstn : forall m c x,
  (forall j, (m <= j)%nat -> nth j c 0%Q == 0) ->
  polyQ (firstn m c) x == polyQ c x.
Proof.
  induction m as [|m IH]; intros c x H; simpl.
  - symmetry. apply polyQ_zero_list. intro j. apply H. lia.
  - destruct c as [|u c]; simpl; [ring|].
    rewrite (IH c x (fun j Hj => H (S j) ltac:(lia))). reflexivity.
Qed.

Lemma polyQ_ext : forall c x y, x == y -> polyQ c x == polyQ c y.
Proof.
  induction c as [|a c IH]; intros x y H; simpl; [reflexivity|].
  rewrite (IH x y H), H. reflexivity.
Qed.

Lemma delta_ext : forall i c x y, x == y -> delta i c x == delta i c y.
Proof.
  induction i as [|i IH]; intros c x y H; simpl.
  - apply polyQ_ext; exact H.
  - assert (H1 : Qminus x 1 == Qminus y 1) by (rewrite H; reflexivity).
    rewrite (IH c x y H), (IH c _ _ H1). reflexivity.
Qed.

Lemma sumQn_ext : forall n f g, (forall i, f i == g i) -> sumQn n f == sumQn n g.
Proof.
  induction n as [|n IH]; intros f g H; simpl; [apply H|].
  rewrite (IH f g H), (H (S n)). reflexivity.
Qed.

(* Binomial with a rational upper index, and the weights w_i = C(2i,i)/4^i. *)

Fixpoint binQ (x : Q) (k : nat) : Q :=
  match k with
  | O => 1
  | S k' => Qdiv (Qmult (binQ x k') (Qminus x (Qn k'))) (Qn (S k'))
  end.

Fixpoint wQ (i : nat) : Q :=
  match i with
  | O => 1
  | S i' => Qdiv (Qmult (wQ i') (Qn (2 * i' + 1))) (Qn (2 * i' + 2))
  end.

Lemma Qn_S : forall k, Qn (S k) == Qplus (Qn k) 1.
Proof. intro k. unfold Qn, Qeq. simpl. lia. Qed.

Lemma Qn_nonzero : forall k, ~ Qeq (Qn (S k)) 0.
Proof. intros k H. unfold Qn, Qeq in H. simpl in H. lia. Qed.

Lemma Qn_0 : Qn 0 == 0.
Proof. reflexivity. Qed.

Lemma Qn_1 : Qn 1 == 1.
Proof. reflexivity. Qed.

(* Absorption: binQ x (S k) = x * binQ (x-1) k / (k+1). *)
Lemma binQ_absorb : forall k x,
  binQ x (S k) == Qdiv (Qmult x (binQ (Qminus x 1) k)) (Qn (S k)).
Proof.
  induction k as [|k IH]; intro x.
  - change (binQ x 1) with (Qdiv (Qmult (binQ x 0) (Qminus x (Qn 0))) (Qn 1)).
    change (binQ x 0) with (1:Q). change (binQ (Qminus x 1) 0) with (1:Q).
    rewrite Qn_0, Qn_1. field.
  - change (binQ x (S (S k)))
      with (Qdiv (Qmult (binQ x (S k)) (Qminus x (Qn (S k)))) (Qn (S (S k)))).
    change (binQ (Qminus x 1) (S k))
      with (Qdiv (Qmult (binQ (Qminus x 1) k) (Qminus (Qminus x 1) (Qn k)))
                 (Qn (S k))).
    rewrite (IH x).
    setoid_replace (Qminus x (Qn (S k)))
      with (Qminus (Qminus x 1) (Qn k)) by (rewrite (Qn_S k); ring).
    field. split; apply Qn_nonzero.
Qed.

Lemma binQ_pascal : forall k x,
  binQ x (S k) == Qplus (binQ (Qminus x 1) (S k)) (binQ (Qminus x 1) k).
Proof.
  induction k as [|k IH]; intro x.
  - change (binQ x 1) with (Qdiv (Qmult (binQ x 0) (Qminus x (Qn 0))) (Qn 1)).
    change (binQ (Qminus x 1) 1)
      with (Qdiv (Qmult (binQ (Qminus x 1) 0) (Qminus (Qminus x 1) (Qn 0))) (Qn 1)).
    change (binQ x 0) with (1:Q). change (binQ (Qminus x 1) 0) with (1:Q).
    rewrite Qn_0, Qn_1. field.
  - change (binQ x (S (S k)))
      with (Qdiv (Qmult (binQ x (S k)) (Qminus x (Qn (S k)))) (Qn (S (S k)))).
    rewrite (IH x).
    change (binQ (Qminus x 1) (S (S k)))
      with (Qdiv (Qmult (binQ (Qminus x 1) (S k))
                        (Qminus (Qminus x 1) (Qn (S k)))) (Qn (S (S k)))).
    change (binQ (Qminus x 1) (S k))
      with (Qdiv (Qmult (binQ (Qminus x 1) k) (Qminus (Qminus x 1) (Qn k)))
                 (Qn (S k))).
    assert (H1 : ~ Qn (S k) == 0) by apply Qn_nonzero.
    assert (H2 : ~ Qn (S (S k)) == 0) by apply Qn_nonzero.
    rewrite (Qn_S (S k)), (Qn_S k) in *.
    field. split; assumption.
Qed.

Lemma binQ_ext : forall k x y, x == y -> binQ x k == binQ y k.
Proof.
  induction k as [|k IH]; intros x y H; [reflexivity|].
  cbn [binQ]. rewrite (IH x y H), H. reflexivity.
Qed.

Lemma binQ_diag : forall k, binQ (Qn k) k == 1.
Proof.
  induction k as [|k IH]; [reflexivity|].
  rewrite binQ_absorb.
  assert (E : Qminus (Qn (S k)) 1 == Qn k) by (rewrite (Qn_S k); ring).
  rewrite (binQ_ext k _ _ E), IH. field. apply Qn_nonzero.
Qed.

Lemma Qn_add : forall a b, Qn (a + b) == Qplus (Qn a) (Qn b).
Proof. intros a b. unfold Qn, Qeq. simpl. lia. Qed.

Lemma Qn_mul : forall a b, Qn (a * b) == Qmult (Qn a) (Qn b).
Proof. intros a b. unfold Qn, Qeq. simpl. lia. Qed.

Lemma Qn_sub : forall a b, (b <= a)%nat -> Qn (a - b) == Qminus (Qn a) (Qn b).
Proof. intros a b H. unfold Qn, Qeq. simpl. lia. Qed.

Lemma altQ_S : forall j, altQ (S j) == Qopp (altQ j).
Proof.
  intro j. unfold altQ. rewrite Nat.even_succ, <- Nat.negb_even.
  destruct (Nat.even j); reflexivity.
Qed.

Lemma Qn2 : Qn 2 == 2.
Proof. unfold Qn, Qeq. simpl. lia. Qed.

Lemma Qn_pos_nonzero : forall m, (1 <= m)%nat -> ~ Qeq (Qn m) 0.
Proof. intros m H. destruct m as [|m]; [lia|]. apply Qn_nonzero. Qed.

Lemma Qdiv_zero_num : forall a b, ~ b == 0 -> Qdiv a b == 0 -> a == 0.
Proof.
  intros a b Hb H.
  transitivity (Qmult (Qdiv a b) b).
  - field. exact Hb.
  - rewrite H. ring.
Qed.

Lemma wQ_nonzero : forall i, ~ (wQ i == 0).
Proof.
  induction i as [|i IH].
  - cbn [wQ]. intro H. unfold Qeq in H. simpl in H. discriminate.
  - cbn [wQ]. intro H.
    apply Qdiv_zero_num in H; [| apply Qn_pos_nonzero; lia].
    apply Qmult_integral in H. destruct H as [H|H].
    + exact (IH H).
    + revert H. apply Qn_pos_nonzero. lia.
Qed.

Lemma sumQn_ext_le : forall n (f g : nat -> Q),
  (forall i, (i <= n)%nat -> f i == g i) -> sumQn n f == sumQn n g.
Proof.
  induction n as [|n IH]; intros f g H.
  - cbn [sumQn]. apply H. lia.
  - assert (H' : forall i, (i <= n)%nat -> f i == g i)
      by (intros i Hi; apply H; lia).
    change (sumQn (S n) f) with (Qplus (sumQn n f) (f (S n))).
    change (sumQn (S n) g) with (Qplus (sumQn n g) (g (S n))).
    rewrite (IH f g H'). rewrite (H (S n)) by lia. reflexivity.
Qed.

Lemma sumQn_shift : forall n (f : nat -> Q),
  sumQn (S n) f == Qplus (f O) (sumQn n (fun i => f (S i))).
Proof.
  induction n as [|n IH]; intro f.
  - cbn [sumQn]. ring.
  - change (sumQn (S (S n)) f) with (Qplus (sumQn (S n) f) (f (S (S n)))).
    rewrite (IH f).
    change (sumQn (S n) (fun i => f (S i)))
      with (Qplus (sumQn n (fun i => f (S i))) (f (S (S n)))).
    ring.
Qed.

Lemma sumQn_rev : forall n (f : nat -> Q),
  sumQn n (fun i => f ((n - i)%nat)) == sumQn n f.
Proof.
  induction n as [|n IH]; intro f.
  - cbn [sumQn]. reflexivity.
  - change (sumQn (S n) (fun i => f ((S n - i)%nat)))
      with (Qplus (sumQn n (fun i => f ((S n - i)%nat))) (f ((S n - S n)%nat))).
    replace (S n - S n)%nat with O by lia.
    assert (E : sumQn n (fun i => f ((S n - i)%nat))
                == sumQn n (fun i => (fun m => f (S m)) ((n - i)%nat))).
    { apply sumQn_ext_le. intros i Hi.
      replace (S n - i)%nat with (S (n - i))%nat by lia. reflexivity. }
    rewrite E, (IH (fun m => f (S m))), (sumQn_shift n f). ring.
Qed.

Lemma sumQn_scal : forall n c (f : nat -> Q),
  sumQn n (fun i => Qmult c (f i)) == Qmult c (sumQn n f).
Proof.
  induction n as [|n IH]; intros c f.
  - cbn [sumQn]. reflexivity.
  - change (sumQn (S n) (fun i => Qmult c (f i)))
      with (Qplus (sumQn n (fun i => Qmult c (f i))) (Qmult c (f (S n)))).
    change (sumQn (S n) f) with (Qplus (sumQn n f) (f (S n))).
    rewrite (IH c f). ring.
Qed.

Lemma altQ_sub : forall k i, (i <= k)%nat -> altQ (k - i) == Qmult (altQ k) (altQ i).
Proof.
  intros k i H. unfold altQ. rewrite (Nat.even_sub k i H).
  destruct (Nat.even k); destruct (Nat.even i); reflexivity.
Qed.

(* The same telescoping weighted by i, collapsing to f(x+1) - f(x). *)
Lemma sum_i_telescope : forall n c x,
  sumQn n (fun i => Qmult (Qn i) (delta i c (Qminus x 1)))
  == Qminus (Qminus (sumQn n (fun i => delta i c x)) (polyQ c x))
            (Qmult (Qn n) (delta (S n) c x)).
Proof.
  induction n as [|n IH]; intros c x.
  - cbn [sumQn delta]. rewrite Qn_0. ring.
  - change (sumQn (S n) (fun i => Qmult (Qn i) (delta i c (Qminus x 1))))
      with (Qplus (sumQn n (fun i => Qmult (Qn i) (delta i c (Qminus x 1))))
                  (Qmult (Qn (S n)) (delta (S n) c (Qminus x 1)))).
    change (sumQn (S n) (fun i => delta i c x))
      with (Qplus (sumQn n (fun i => delta i c x)) (delta (S n) c x)).
    rewrite (IH c x), (Qn_S n). cbn [delta]. ring.
Qed.

Theorem sum_i_delta : forall n c x, (length c <= S n)%nat ->
  sumQn n (fun i => Qmult (Qn i) (delta i c (Qminus x 1)))
  == Qminus (polyQ c (Qplus x 1)) (polyQ c x).
Proof.
  intros n c x Hc.
  rewrite (sum_i_telescope n c x), (delta_vanishes n c x Hc).
  assert (E : sumQn n (fun i => delta i c x)
              == sumQn n (fun i => delta i c (Qminus (Qplus x 1) 1))).
  { apply sumQn_ext_le. intros i Hi. apply delta_ext. ring. }
  rewrite E, (sum_delta n c (Qplus x 1) Hc). ring.
Qed.

(* Alternating partial sums of a binomial row: sum_{i<=k} (-1)^i C(x,i)
   = (-1)^k C(x-1,k), by Pascal. *)
Lemma alt_partial : forall k x,
  sumQn k (fun i => Qmult (altQ i) (binQ x i))
  == Qmult (altQ k) (binQ (Qminus x 1) k).
Proof.
  induction k as [|k IH]; intro x.
  - cbn [sumQn binQ]. change (altQ 0) with (1:Q). ring.
  - cbn [sumQn]. rewrite (IH x), (binQ_pascal k x), (altQ_S k). ring.
Qed.

Lemma binQ_zero : forall k m, (m < k)%nat -> binQ (Qn m) k == 0.
Proof.
  induction k as [|k IH]; intros m Hm; [lia|].
  change (binQ (Qn m) (S k))
    with (Qdiv (Qmult (binQ (Qn m) k) (Qminus (Qn m) (Qn k))) (Qn (S k))).
  destruct (Nat.eq_dec m k) as [E|E].
  - subst m. assert (Z : Qminus (Qn k) (Qn k) == 0) by ring.
    rewrite Z. field. apply Qn_nonzero.
  - rewrite (IH m ltac:(lia)). field. apply Qn_nonzero.
Qed.

(* The alternating row sum vanishes: sum_{i<=k} (-1)^i C(k,i) = 0 for k >= 1. *)
Theorem alt_row : forall k, (1 <= k)%nat ->
  sumQn k (fun i => Qmult (altQ i) (binQ (Qn k) i)) == 0.
Proof.
  intros k Hk. rewrite alt_partial.
  assert (E : Qminus (Qn k) 1 == Qn (k - 1)).
  { rewrite (Qn_sub k 1 ltac:(lia)), Qn_1. reflexivity. }
  rewrite (binQ_ext k _ _ E), (binQ_zero k (k - 1) ltac:(lia)). ring.
Qed.

(* wQ is the central binomial weight C(2i,i)/4^i. *)

Lemma binomN_binomZ : forall n k, Z.of_nat (binomN n k) = binomZ n k.
Proof.
  induction n as [|n IH]; intro k.
  - destruct k; reflexivity.
  - destruct k as [|k]; [reflexivity|].
    change (binomN (S n) (S k)) with (binomN n k + binomN n (S k))%nat.
    rewrite Nat2Z.inj_add, (IH k), (IH (S k)). reflexivity.
Qed.

Lemma binomZ_mid : forall n, binomZ (2 * n + 1) n = binomZ (2 * n + 1) (S n).
Proof.
  intro n. assert (H := binomZ_step (2 * n + 1) n ltac:(lia)).
  replace (Z.of_nat (2 * n + 1) - Z.of_nat n)%Z with (Z.of_nat (S n)) in H by lia.
  apply (Z.mul_reg_l _ _ (Z.of_nat (S n))); [lia | exact H].
Qed.

Lemma binomZ_central : forall n,
  (Z.of_nat (S n) * binomZ (2 * n + 2) (S n)
   = 2 * Z.of_nat (2 * n + 1) * binomZ (2 * n) n)%Z.
Proof.
  intro n.
  assert (P1 : binomZ (2 * n + 2) (S n)
               = (binomZ (2 * n + 1) n + binomZ (2 * n + 1) (S n))%Z).
  { replace (2 * n + 2)%nat with (S (2 * n + 1))%nat by lia.
    apply binomZ_pascal. }
  assert (P2 : binomZ (2 * n + 1) (S n)
               = (binomZ (2 * n) n + binomZ (2 * n) (S n))%Z).
  { replace (2 * n + 1)%nat with (S (2 * n))%nat by lia. apply binomZ_pascal. }
  assert (S1 := binomZ_step (2 * n) n ltac:(lia)).
  replace (Z.of_nat (2 * n) - Z.of_nat n)%Z with (Z.of_nat n) in S1 by lia.
  assert (M := binomZ_mid n).
  rewrite P1, M, P2. nia.
Qed.

Lemma Qn_four_pow : forall i, Qn (4 ^ S i) == Qmult 4 (Qn (4 ^ i)).
Proof.
  intro i. change (4 ^ S i)%nat with (4 * 4 ^ i)%nat.
  rewrite Qn_mul. assert (E : Qn 4 == 4) by (unfold Qn, Qeq; simpl; lia).
  rewrite E. reflexivity.
Qed.

Lemma four_pow_pos : forall i, (1 <= 4 ^ i)%nat.
Proof. induction i as [|i IH]; simpl; [lia | nia]. Qed.

Theorem wQ_eq : forall i,
  Qmult (wQ i) (Qn (4 ^ i)) == Qn (binomN (2 * i) i).
Proof.
  induction i as [|i IH].
  - cbn [wQ].
    replace (4 ^ 0)%nat with 1%nat by reflexivity.
    replace (binomN (2 * 0) 0) with 1%nat by reflexivity.
    rewrite Qn_1. ring.
  - assert (H1 : ~ Qn (2 * i + 2) == 0) by (apply Qn_pos_nonzero; lia).
    assert (HN : (S i * binomN (2 * i + 2) (S i)
                  = 2 * (2 * i + 1) * binomN (2 * i) i)%nat).
    { apply Nat2Z.inj. rewrite !Nat2Z.inj_mul, !binomN_binomZ.
      change (Z.of_nat 2) with 2%Z. exact (binomZ_central i). }
    assert (HC : Qmult (Qn (S i)) (Qn (binomN (2 * i + 2) (S i)))
                 == Qmult (Qmult 2 (Qn (2 * i + 1))) (Qn (binomN (2 * i) i))).
    { transitivity (Qn (S i * binomN (2 * i + 2) (S i))).
      - rewrite Qn_mul. reflexivity.
      - rewrite HN, !Qn_mul, Qn2. ring. }
    assert (E2 : Qn (2 * i + 2) == Qmult 2 (Qn (S i))).
    { rewrite Qn_add, Qn_mul, Qn2, (Qn_S i). ring. }
    assert (G : Qmult (Qmult 4 (Qn (2 * i + 1))) (Qn (binomN (2 * i) i))
                == Qmult (Qn (2 * i + 2)) (Qn (binomN (2 * i + 2) (S i)))).
    { rewrite E2.
      transitivity (Qmult 2 (Qmult (Qn (S i)) (Qn (binomN (2 * i + 2) (S i))))).
      - rewrite HC. ring.
      - ring. }
    cbn [wQ]. rewrite Qn_four_pow.
    replace (2 * S i)%nat with (2 * i + 2)%nat by lia.
    transitivity (Qdiv (Qmult (Qmult 4 (Qn (2 * i + 1)))
                              (Qmult (wQ i) (Qn (4 ^ i))))
                       (Qn (2 * i + 2))).
    { field. exact H1. }
    rewrite IH, G. field. exact H1.
Qed.

(* The alternating row weighted by i vanishes for k >= 2. *)
Theorem alt_row_i : forall k, (2 <= k)%nat ->
  sumQn k (fun i => Qmult (Qn i) (Qmult (altQ i) (binQ (Qn k) i))) == 0.
Proof.
  intros k Hk. destruct k as [|k']; [lia|].
  rewrite (sumQn_shift k' (fun i => Qmult (Qn i)
                                          (Qmult (altQ i) (binQ (Qn (S k')) i)))).
  assert (E0 : Qmult (Qn 0) (Qmult (altQ 0) (binQ (Qn (S k')) 0)) == 0)
    by (rewrite Qn_0; ring).
  rewrite E0.
  transitivity (Qplus 0 (sumQn k' (fun j =>
      Qmult (Qopp (Qn (S k'))) (Qmult (altQ j) (binQ (Qn k') j))))).
  { apply Qplus_comp; [reflexivity|].
    apply sumQn_ext_le. intros j Hj.
    assert (Hab := binQ_absorb j (Qn (S k'))).
    assert (E1 : Qminus (Qn (S k')) 1 == Qn k')
      by (rewrite (Qn_S k'); ring).
    rewrite (binQ_ext j _ _ E1) in Hab.
    rewrite Hab, (altQ_S j). field. apply Qn_nonzero. }
  rewrite (sumQn_scal k' (Qopp (Qn (S k')))
                        (fun j => Qmult (altQ j) (binQ (Qn k') j))).
  rewrite (alt_row k' ltac:(lia)). ring.
Qed.

(* w_i binQ(-1/2 - i, k-i) = (-1)^(k-i) w_k C(k,i), by downward induction. *)
Theorem collapse_term : forall j k, (j <= k)%nat ->
  Qmult (wQ (k - j)) (binQ (Qminus (Qopp (Qmake 1 2)) (Qn (k - j))) j)
  == Qmult (altQ j) (Qmult (wQ k) (binQ (Qn k) (k - j))).
Proof.
  induction j as [|j IH]; intros k Hk.
  - rewrite Nat.sub_0_r, binQ_diag.
    change (binQ (Qminus (Qopp (Qmake 1 2)) (Qn k)) 0) with (1:Q).
    change (altQ 0) with (1:Q). ring.
  - assert (Hj : (j <= k)%nat) by lia.
    specialize (IH k Hj).
    remember (k - S j)%nat as i eqn:Hi.
    replace (k - j)%nat with (S i) in IH by lia.
    assert (E1 : Qminus (Qminus (Qopp (Qmake 1 2)) (Qn i)) 1
                 == Qminus (Qopp (Qmake 1 2)) (Qn (S i)))
      by (rewrite (Qn_S i); ring).
    rewrite binQ_absorb, (binQ_ext j _ _ E1).
    assert (HB : binQ (Qminus (Qopp (Qmake 1 2)) (Qn (S i))) j
                 == Qdiv (Qmult (altQ j) (Qmult (wQ k) (binQ (Qn k) (S i))))
                         (wQ (S i)))
      by (rewrite <- IH; field; apply wQ_nonzero).
    rewrite HB.
    change (wQ (S i))
      with (Qdiv (Qmult (wQ i) (Qn (2 * i + 1))) (Qn (2 * i + 2))).
    change (binQ (Qn k) (S i))
      with (Qdiv (Qmult (binQ (Qn k) i) (Qminus (Qn k) (Qn i))) (Qn (S i))).
    assert (Ek : Qminus (Qn k) (Qn i) == Qn (S j)).
    { rewrite <- Qn_sub by lia. replace (k - i)%nat with (S j) by lia. reflexivity. }
    assert (Ey : Qminus (Qopp (Qmake 1 2)) (Qn i)
                 == Qopp (Qdiv (Qn (2 * i + 1)) 2)).
    { rewrite Qn_add, Qn_mul, Qn2, Qn_1. field. }
    assert (E2 : Qn (2 * i + 2) == Qmult 2 (Qn (S i))).
    { rewrite Qn_add, Qn_mul, Qn2, (Qn_S i). ring. }
    rewrite Ek, Ey, E2, altQ_S.
    field. repeat split;
      first [ apply wQ_nonzero | apply Qn_nonzero | (apply Qn_pos_nonzero; lia) ].
Qed.

Theorem collapse_sum_i : forall k, (2 <= k)%nat ->
  sumQn k (fun j => Qmult (Qn (k - j))
             (Qmult (wQ (k - j))
                    (binQ (Qminus (Qopp (Qmake 1 2)) (Qn (k - j))) j))) == 0.
Proof.
  intros k Hk.
  transitivity (sumQn k (fun j => Qmult (Qn (k - j))
             (Qmult (altQ j) (Qmult (wQ k) (binQ (Qn k) (k - j)))))).
  { apply sumQn_ext_le. intros j Hj. rewrite (collapse_term j k Hj). reflexivity. }
  transitivity (sumQn k (fun j =>
      (fun i => Qmult (Qn i)
                  (Qmult (altQ (k - i)) (Qmult (wQ k) (binQ (Qn k) i))))
        ((k - j)%nat))).
  { apply sumQn_ext_le. intros j Hj.
    replace (k - (k - j))%nat with j by lia. reflexivity. }
  rewrite (sumQn_rev k (fun i => Qmult (Qn i)
             (Qmult (altQ (k - i)) (Qmult (wQ k) (binQ (Qn k) i))))).
  transitivity (sumQn k (fun i => Qmult (Qmult (altQ k) (wQ k))
             (Qmult (Qn i) (Qmult (altQ i) (binQ (Qn k) i))))).
  { apply sumQn_ext_le. intros i Hi. rewrite (altQ_sub k i Hi). ring. }
  rewrite (sumQn_scal k (Qmult (altQ k) (wQ k))
             (fun i => Qmult (Qn i) (Qmult (altQ i) (binQ (Qn k) i)))).
  rewrite (alt_row_i k Hk). ring.
Qed.

(* The binomial basis as coefficient lists. *)

Definition pscale (a : Q) (c : list Q) : list Q := map (Qmult a) c.

Lemma pscale_spec : forall a c x, polyQ (pscale a c) x == Qmult a (polyQ c x).
Proof.
  intros a c x. induction c as [|u c IH]; simpl; [ring|].
  unfold pscale in IH. rewrite IH. ring.
Qed.

Lemma pscale_len : forall a c, length (pscale a c) = length c.
Proof. intros a c. unfold pscale. apply len_map. Qed.

Fixpoint binlist (k : nat) : list Q :=
  match k with
  | O => 1%Q :: nil
  | S k' => pscale (Qinv (Qn (S k')))
                   (psub (0%Q :: binlist k') (pscale (Qn k') (binlist k')))
  end.

Lemma binlist_spec : forall k x, polyQ (binlist k) x == binQ x k.
Proof.
  induction k as [|k IH]; intro x; [simpl; ring|].
  cbn [binlist]. rewrite pscale_spec, psub_spec.
  cbn [polyQ]. rewrite pscale_spec, (IH x).
  change (binQ x (S k))
    with (Qdiv (Qmult (binQ x k) (Qminus x (Qn k))) (Qn (S k))).
  field. apply Qn_nonzero.
Qed.

Lemma binlist_len : forall k, length (binlist k) = S k.
Proof.
  induction k as [|k IH]; [reflexivity|].
  cbn [binlist]. rewrite pscale_len, psub_len, pscale_len. cbn [length].
  rewrite IH. lia.
Qed.

(* Delta acts on the binomial basis as a shift: Delta^i binQ(.,k)(x) = binQ(x-i, k-i). *)
Theorem delta_binlist : forall i k x, (i <= k)%nat ->
  delta i (binlist k) x == binQ (Qminus x (Qn i)) (k - i).
Proof.
  induction i as [|i IH]; intros k x Hi.
  - cbn [delta]. rewrite binlist_spec, Nat.sub_0_r.
    apply binQ_ext. rewrite Qn_0. ring.
  - cbn [delta].
    rewrite (IH k x ltac:(lia)), (IH k (Qminus x 1) ltac:(lia)).
    replace (k - i)%nat with (S (k - S i))%nat by lia.
    assert (E : Qminus (Qminus x 1) (Qn i) == Qminus (Qminus x (Qn i)) 1) by ring.
    rewrite (binQ_ext (S (k - S i)) _ _ E).
    rewrite (binQ_pascal (k - S i) (Qminus x (Qn i))).
    assert (E2 : Qminus (Qminus x (Qn i)) 1 == Qminus x (Qn (S i)))
      by (rewrite (Qn_S i); ring).
    rewrite (binQ_ext (k - S i) _ _ E2). ring.
Qed.

Lemma nth_nil : forall m, nth m (@nil Q) 0%Q = 0%Q.
Proof. intro m. destruct m; reflexivity. Qed.

Lemma nth_mapopp : forall b m, nth m (map Qopp b) 0%Q == Qopp (nth m b 0%Q).
Proof.
  induction b as [|v b IH]; intro m.
  - change (map Qopp (@nil Q)) with (@nil Q). rewrite !nth_nil. ring.
  - destruct m as [|m]; [reflexivity|].
    change (nth (S m) (map Qopp (v :: b)) 0%Q)
      with (nth m (map Qopp b) 0%Q).
    change (nth (S m) (v :: b) 0%Q) with (nth m b 0%Q). apply IH.
Qed.

Lemma nth_pscale : forall c a m,
  nth m (pscale a c) 0%Q == Qmult a (nth m c 0%Q).
Proof.
  induction c as [|u c IH]; intros a m; unfold pscale.
  - change (map (Qmult a) (@nil Q)) with (@nil Q). rewrite !nth_nil. ring.
  - destruct m as [|m]; [reflexivity|].
    change (nth (S m) (map (Qmult a) (u :: c)) 0%Q)
      with (nth m (map (Qmult a) c) 0%Q).
    change (nth (S m) (u :: c) 0%Q) with (nth m c 0%Q). apply (IH a m).
Qed.

Lemma nth_psub : forall a b m,
  nth m (psub a b) 0%Q == Qminus (nth m a 0%Q) (nth m b 0%Q).
Proof.
  induction a as [|u a IH]; intros b m.
  - change (psub (@nil Q) b) with (map Qopp b).
    rewrite nth_mapopp, (nth_nil m). ring.
  - destruct b as [|v b].
    + change (psub (u :: a) (@nil Q)) with (u :: a).
      rewrite (nth_nil m). ring.
    + destruct m as [|m]; [reflexivity|].
      change (nth (S m) (psub (u :: a) (v :: b)) 0%Q)
        with (nth m (psub a b) 0%Q).
      change (nth (S m) (u :: a) 0%Q) with (nth m a 0%Q).
      change (nth (S m) (v :: b) 0%Q) with (nth m b 0%Q). apply IH.
Qed.

Lemma factn_pos : forall k, (1 <= factn k)%nat.
Proof. induction k as [|k IH]; simpl; [lia | nia]. Qed.

Lemma binlist_lead : forall k, nth k (binlist k) 0%Q == Qinv (Qn (factn k)).
Proof.
  induction k as [|k IH]; [reflexivity|].
  cbn [binlist]. rewrite nth_pscale, nth_psub, nth_pscale.
  cbn [nth]. rewrite IH.
  assert (Hov : nth (S k) (binlist k) 0%Q = 0%Q).
  { apply nth_overflow. rewrite binlist_len. lia. }
  rewrite Hov.
  change (factn (S k)) with ((S k) * factn k)%nat.
  rewrite Qn_mul. field. split.
  - apply Qn_pos_nonzero. apply factn_pos.
  - apply Qn_nonzero.
Qed.

Lemma delta_pscale : forall i q c x,
  delta i (pscale q c) x == Qmult q (delta i c x).
Proof.
  induction i as [|i IH]; intros q c x; simpl; [apply pscale_spec|].
  rewrite (IH q c x), (IH q c (Qminus x 1)). ring.
Qed.

Lemma delta_padd : forall i a b x,
  delta i (padd a b) x == Qplus (delta i a x) (delta i b x).
Proof.
  induction i as [|i IH]; intros a b x; simpl; [apply padd_spec|].
  rewrite (IH a b x), (IH a b (Qminus x 1)). ring.
Qed.

Lemma sumQn_add : forall n (f g : nat -> Q),
  sumQn n (fun i => Qplus (f i) (g i)) == Qplus (sumQn n f) (sumQn n g).
Proof.
  induction n as [|n IH]; intros f g.
  - cbn [sumQn]. reflexivity.
  - change (sumQn (S n) (fun i => Qplus (f i) (g i)))
      with (Qplus (sumQn n (fun i => Qplus (f i) (g i))) (Qplus (f (S n)) (g (S n)))).
    change (sumQn (S n) f) with (Qplus (sumQn n f) (f (S n))).
    change (sumQn (S n) g) with (Qplus (sumQn n g) (g (S n))).
    rewrite (IH f g). ring.
Qed.

Lemma sumQn_trunc : forall n k (f : nat -> Q), (k <= n)%nat ->
  (forall i, (k < i)%nat -> (i <= n)%nat -> f i == 0) ->
  sumQn n f == sumQn k f.
Proof.
  induction n as [|n IH]; intros k f Hk H.
  - replace k with O by lia. reflexivity.
  - destruct (Nat.eq_dec k (S n)) as [E|E]; [subst; reflexivity|].
    change (sumQn (S n) f) with (Qplus (sumQn n f) (f (S n))).
    rewrite (IH k f ltac:(lia) ltac:(intros i H1 H2; apply H; lia)).
    rewrite (H (S n) ltac:(lia) ltac:(lia)). ring.
Qed.

(* sum_{i<=k} w_i binQ(-1/2 - i, k-i) = 0 for k >= 1. *)
Theorem collapse_sum : forall k, (1 <= k)%nat ->
  sumQn k (fun j => Qmult (wQ (k - j))
                          (binQ (Qminus (Qopp (Qmake 1 2)) (Qn (k - j))) j)) == 0.
Proof.
  intros k Hk.
  transitivity (sumQn k (fun j => Qmult (altQ j)
                          (Qmult (wQ k) (binQ (Qn k) (k - j))))).
  { apply sumQn_ext_le. intros j Hj. apply collapse_term. exact Hj. }
  transitivity (sumQn k (fun j =>
      (fun i => Qmult (altQ (k - i)) (Qmult (wQ k) (binQ (Qn k) i))) ((k - j)%nat))).
  { apply sumQn_ext_le. intros j Hj.
    replace (k - (k - j))%nat with j by lia. reflexivity. }
  rewrite (sumQn_rev k (fun i => Qmult (altQ (k - i))
                                       (Qmult (wQ k) (binQ (Qn k) i)))).
  transitivity (sumQn k (fun i => Qmult (Qmult (altQ k) (wQ k))
                                        (Qmult (altQ i) (binQ (Qn k) i)))).
  { apply sumQn_ext_le. intros i Hi. rewrite (altQ_sub k i Hi). ring. }
  rewrite (sumQn_scal k (Qmult (altQ k) (wQ k))
                       (fun i => Qmult (altQ i) (binQ (Qn k) i))).
  rewrite (alt_row k Hk). ring.
Qed.

Lemma contains_132_dec : forall u, {contains_132 u} + {~ contains_132 u}.
Proof.
  intro u.
  assert (H : {exists i, (i < length u)%nat /\
                 exists j, (j < length u)%nat /\
                 exists k, (k < length u)%nat /\ has_132_at u i j k}
            + {~ exists i, (i < length u)%nat /\
                 exists j, (j < length u)%nat /\
                 exists k, (k < length u)%nat /\ has_132_at u i j k}).
  { apply bounded_ex_dec. intro i.
    apply bounded_ex_dec. intro j.
    apply bounded_ex_dec. intro k.
    apply has_132_at_dec. }
  destruct H as [H | H].
  - left. destruct H as [i [_ [j [_ [k [_ H]]]]]]. exists i, j, k. exact H.
  - right. intros [i [j [k Hc]]]. apply H.
    assert (Hd := Hc). unfold has_132_at in Hd.
    destruct Hd as [Hij [Hjk [Hk _]]].
    exists i. split; [lia|]. exists j. split; [lia|].
    exists k. split; [lia | exact Hc].
Defined.

Definition avoids132b (u : list nat) : bool :=
  if contains_132_dec u then false else true.

(* D(d,M): 1324-avoiders of length M+d whose length-M prefix avoids 132. *)
Definition Ddiag (d M : nat) : nat :=
  length (filter (fun w => avoids132b (firstn M w)) (gen (M + d))).

Lemma filter_all_gen : forall (A : Type) (P : A -> bool) (l : list A),
  (forall y, In y l -> P y = true) -> filter P l = l.
Proof.
  intros A P. induction l as [|a l IH]; intro H; simpl; [reflexivity|].
  rewrite (H a (or_introl eq_refl)). f_equal.
  apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

(* A prefix of length at most two avoids 132, so the first three columns are card. *)
Theorem Ddiag_short : forall d M, (M <= 2)%nat -> Ddiag d M = card (M + d).
Proof.
  intros d M HM. unfold Ddiag, card.
  rewrite filter_all_gen; [reflexivity|].
  intros w _. unfold avoids132b.
  destruct (contains_132_dec (firstn M w)) as [H|H]; [exfalso | reflexivity].
  apply (short_avoids_132 (firstn M w)); [| exact H].
  rewrite length_firstn. lia.
Qed.

(* Counting a list by the fibres of a map with decidable equality on the target. *)

Lemma filter_filter : forall (A : Type) (P Q : A -> bool) (l : list A),
  filter Q (filter P l) = filter (fun x => andb (P x) (Q x)) l.
Proof.
  intros A P Q. induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (P a) eqn:E; simpl.
  - destruct (Q a); simpl; rewrite IH; reflexivity.
  - exact IH.
Qed.

Lemma fold_count_zero : forall (A : Type) (eqA : forall x y : A, {x = y} + {x <> y})
    (a : A) (keys : list A),
  ~ In a keys ->
  fold_right (fun k acc => ((if eqA a k then 1 else 0) + acc)%nat) 0%nat keys = 0%nat.
Proof.
  intros A eqA a. induction keys as [|k ks IH]; intro H; simpl; [reflexivity|].
  destruct (eqA a k) as [E|E];
    [exfalso; apply H; left; symmetry; exact E|].
  simpl. apply IH. intro Hc. apply H. right. exact Hc.
Qed.

Lemma fold_count_one : forall (A : Type) (eqA : forall x y : A, {x = y} + {x <> y})
    (a : A) (keys : list A),
  NoDup keys -> In a keys ->
  fold_right (fun k acc => ((if eqA a k then 1 else 0) + acc)%nat) 0%nat keys = 1%nat.
Proof.
  intros A eqA a. induction keys as [|k ks IH]; intros Hnd Hin; simpl in Hin;
    [contradiction|].
  inversion Hnd as [|y r Hnk Hnd' Heq]; subst.
  simpl. destruct (eqA a k) as [E|E].
  - subst a. rewrite (fold_count_zero A eqA k ks Hnk). reflexivity.
  - simpl. apply IH; [exact Hnd'|].
    destruct Hin as [Hc|Hc]; [exfalso; apply E; symmetry; exact Hc | exact Hc].
Qed.

Lemma fold_add_split : forall (A : Type) (g h : A -> nat) (keys : list A),
  fold_right (fun k acc => (g k + h k + acc)%nat) 0%nat keys
  = (fold_right (fun k acc => (g k + acc)%nat) 0%nat keys
     + fold_right (fun k acc => (h k + acc)%nat) 0%nat keys)%nat.
Proof.
  intros A g h. induction keys as [|k ks IH]; simpl; [reflexivity|].
  rewrite IH. lia.
Qed.

Lemma fold_ext : forall (A : Type) (g h : A -> nat) (keys : list A),
  (forall k, g k = h k) ->
  fold_right (fun k acc => (g k + acc)%nat) 0%nat keys
  = fold_right (fun k acc => (h k + acc)%nat) 0%nat keys.
Proof.
  intros A g h keys H. induction keys as [|k ks IH]; simpl; [reflexivity|].
  rewrite (H k), IH. reflexivity.
Qed.

Lemma fold_zero : forall (A : Type) (keys : list A),
  fold_right (fun (_ : A) acc => (0 + acc)%nat) 0%nat keys = 0%nat.
Proof. intros A. induction keys as [|k ks IH]; simpl; [reflexivity | exact IH]. Qed.

Theorem length_fibres : forall (A B : Type)
    (eqA : forall x y : A, {x = y} + {x <> y})
    (f : B -> A) (keys : list A) (l : list B),
  NoDup keys ->
  (forall x, In x l -> In (f x) keys) ->
  length l
  = fold_right (fun k acc =>
      (length (filter (fun x => if eqA (f x) k then true else false) l) + acc)%nat)
      0%nat keys.
Proof.
  intros A B eqA f keys l Hnd Hcov. revert Hcov.
  induction l as [|x l IH]; intro Hcov.
  - rewrite (fold_ext A
      (fun k => length (filter (fun y => if eqA (f y) k then true else false)
                               (@nil B)))
      (fun _ => 0%nat) keys) by (intro k; reflexivity).
    symmetry. apply fold_zero.
  - assert (Hx : In (f x) keys) by (apply Hcov; left; reflexivity).
    assert (Hl : forall y, In y l -> In (f y) keys)
      by (intros y Hy; apply Hcov; right; exact Hy).
    rewrite (fold_ext A
      (fun k => length (filter (fun y => if eqA (f y) k then true else false)
                               (x :: l)))
      (fun k => ((if eqA (f x) k then 1 else 0)
                 + length (filter (fun y => if eqA (f y) k then true else false) l))%nat)
      keys) by (intro k; simpl; destruct (eqA (f x) k); reflexivity).
    rewrite fold_add_split, (fold_count_one A eqA (f x) keys Hnd Hx),
            <- (IH Hl). reflexivity.
Qed.

(* A 132-free prefix with a strictly decreasing suffix avoids 1324: an occurrence
   would need an ascent in the suffix. *)
Theorem decreasing_tail_avoids : forall pre suf,
  ~ contains_132 pre ->
  (forall t t', (t < t')%nat -> (t' < length suf)%nat ->
     (nth t' suf 0%nat < nth t suf 0%nat)%nat) ->
  ~ contains_1324 (pre ++ suf).
Proof.
  intros pre suf Hpre Hdec C.
  apply (localise pre suf Hpre) in C.
  destruct C as [t [t' [i [j [Htt' [Ht' [Hij [Hj [H1 [H2 H3]]]]]]]]]].
  assert (Hlt : (nth (length pre + t) (pre ++ suf) 0%nat
                 < nth (length pre + t') (pre ++ suf) 0%nat)%nat) by lia.
  rewrite (nth_app2 pre suf (length pre + t) 0%nat) in Hlt by lia.
  rewrite (nth_app2 pre suf (length pre + t') 0%nat) in Hlt by lia.
  replace (length pre + t - length pre)%nat with t in Hlt by lia.
  replace (length pre + t' - length pre)%nat with t' in Hlt by lia.
  specialize (Hdec t t' Htt' Ht'). lia.
Qed.

(* Relabelling through a strictly increasing list is an order isomorphism. *)

Definition relab (vals u : list nat) : list nat :=
  map (fun t => nth t vals 0%nat) u.

Definition incr (vals : list nat) : Prop :=
  forall a b, (a < b)%nat -> (b < length vals)%nat ->
    (nth a vals 0%nat < nth b vals 0%nat)%nat.

Lemma relab_length : forall vals u, length (relab vals u) = length u.
Proof. intros vals u. unfold relab. apply len_map_gen. Qed.

Lemma relab_nth : forall vals u t, (t < length u)%nat ->
  nth t (relab vals u) 0%nat = nth (nth t u 0%nat) vals 0%nat.
Proof.
  intros vals u t H. unfold relab.
  erewrite nth_indep by (rewrite len_map_gen; exact H).
  rewrite map_nth. reflexivity.
Qed.

Lemma relab_lt : forall vals u a b,
  incr vals ->
  (forall x, In x u -> (x < length vals)%nat) ->
  (a < length u)%nat -> (b < length u)%nat ->
  ((nth a (relab vals u) 0%nat < nth b (relab vals u) 0%nat)%nat
   <-> (nth a u 0%nat < nth b u 0%nat)%nat).
Proof.
  intros vals u a b Hi Hb Ha Hbb.
  assert (Va : (nth a u 0%nat < length vals)%nat)
    by (apply Hb; apply nth_in; exact Ha).
  assert (Vb : (nth b u 0%nat < length vals)%nat)
    by (apply Hb; apply nth_in; exact Hbb).
  rewrite (relab_nth vals u a Ha), (relab_nth vals u b Hbb).
  split.
  - intro H. destruct (Nat.lt_trichotomy (nth a u 0%nat) (nth b u 0%nat))
      as [K | [K | K]]; [exact K | rewrite K in H; lia |].
    exfalso. assert (nth (nth b u 0%nat) vals 0%nat < nth (nth a u 0%nat) vals 0%nat)%nat
      by (apply Hi; [exact K | exact Va]). lia.
  - intro H. apply Hi; [exact H | exact Vb].
Qed.

Theorem relab_132 : forall vals u,
  incr vals -> (forall x, In x u -> (x < length vals)%nat) ->
  (contains_132 (relab vals u) <-> contains_132 u).
Proof.
  intros vals u Hi Hb. split.
  - intros [i [j [k H]]]. unfold has_132_at in H.
    destruct H as [Hij [Hjk [Hk [Hik Hkj]]]].
    rewrite relab_length in Hk.
    exists i, j, k. unfold has_132_at. repeat split; try lia.
    + apply (relab_lt vals u i k Hi Hb ltac:(lia) ltac:(lia)). exact Hik.
    + apply (relab_lt vals u k j Hi Hb ltac:(lia) ltac:(lia)). exact Hkj.
  - intros [i [j [k H]]]. unfold has_132_at in H.
    destruct H as [Hij [Hjk [Hk [Hik Hkj]]]].
    exists i, j, k. unfold has_132_at. rewrite relab_length. repeat split; try lia.
    + apply (relab_lt vals u i k Hi Hb ltac:(lia) ltac:(lia)). exact Hik.
    + apply (relab_lt vals u k j Hi Hb ltac:(lia) ltac:(lia)). exact Hkj.
Qed.

(* The decreasing suffix fibre is a free product: prefix pattern and suffix
   values are chosen independently, giving N_dec(M) = Cat(M) C(M+d,d). *)
Theorem dec_fibre_free : forall vals u suf,
  incr vals ->
  (forall x, In x u -> (x < length vals)%nat) ->
  ~ contains_132 u ->
  (forall t t', (t < t')%nat -> (t' < length suf)%nat ->
     (nth t' suf 0%nat < nth t suf 0%nat)%nat) ->
  ~ contains_1324 (relab vals u ++ suf).
Proof.
  intros vals u suf Hi Hb Hu Hd.
  apply decreasing_tail_avoids; [| exact Hd].
  intro C. apply Hu. apply (relab_132 vals u Hi Hb). exact C.
Qed.

(* The max-split: placing the maximum between two parts, the left carried above
   the right, gives a 132-avoider exactly when both parts are. *)

Definition midmax (u v : list nat) : list nat :=
  map (fun x => (x + length v)%nat) u ++ (length u + length v)%nat :: v.

Lemma midmax_length : forall u v,
  length (midmax u v) = (length u + S (length v))%nat.
Proof. intros u v. unfold midmax. rewrite len_app, len_map_add. simpl. lia. Qed.

Lemma midmax_lo : forall u v t, (t < length u)%nat ->
  nth t (midmax u v) 0%nat = (nth t u 0%nat + length v)%nat.
Proof.
  intros u v t H. unfold midmax.
  assert (Hm : (t < length (map (fun x => (x + length v)%nat) u))%nat)
    by (rewrite len_map_add; exact H).
  rewrite nth_app1 by exact Hm.
  erewrite nth_indep by exact Hm. rewrite map_nth. reflexivity.
Qed.

Lemma midmax_mid : forall u v,
  nth (length u) (midmax u v) 0%nat = (length u + length v)%nat.
Proof.
  intros u v. unfold midmax.
  rewrite nth_app2 by (rewrite len_map_add; lia).
  rewrite len_map_add, Nat.sub_diag. reflexivity.
Qed.

Lemma midmax_hi : forall u v t, (length u < t)%nat ->
  nth t (midmax u v) 0%nat = nth (t - S (length u))%nat v 0%nat.
Proof.
  intros u v t H. unfold midmax.
  rewrite nth_app2 by (rewrite len_map_add; lia).
  rewrite len_map_add.
  replace (t - length u)%nat with (S (t - S (length u)))%nat by lia.
  reflexivity.
Qed.

Theorem midmax_132 : forall u v m n,
  is_perm u m -> is_perm v n ->
  (contains_132 (midmax u v) <-> (contains_132 u \/ contains_132 v)).
Proof.
  intros u v m n Hu Hv.
  assert (Hlu : length u = m) by av.
  assert (Hlv : length v = n) by av.
  assert (Bu : forall t, (t < length u)%nat -> (nth t u 0%nat < m)%nat).
  { intros t Ht. destruct Hu as [_ [_ Hb]]. apply Hb. apply nth_In. exact Ht. }
  assert (Bv : forall t, (t < length v)%nat -> (nth t v 0%nat < n)%nat).
  { intros t Ht. destruct Hv as [_ [_ Hb]]. apply Hb. apply nth_In. exact Ht. }
  split.
  - intros [i [j [k H]]]. unfold has_132_at in H.
    destruct H as [Hij [Hjk [Hk [Hik Hkj]]]].
    rewrite midmax_length in Hk.
    destruct (Nat.lt_ge_cases k (length u)) as [Hklo | Hkhi].
    + left. exists i, j, k. unfold has_132_at.
      assert (Ai : (i < length u)%nat) by lia.
      assert (Aj : (j < length u)%nat) by lia.
      assert (Ak : (k < length u)%nat) by lia.
      rewrite (midmax_lo u v i Ai) in Hik.
      rewrite (midmax_lo u v k Ak) in Hik, Hkj.
      rewrite (midmax_lo u v j Aj) in Hkj.
      repeat split; lia.
    + destruct (Nat.eq_dec k (length u)) as [Hke | Hkne].
      * exfalso.
        assert (Aj : (j < length u)%nat) by lia.
        assert (Bj : (nth j u 0%nat < m)%nat) by (apply Bu; exact Aj).
        rewrite Hke, midmax_mid, (midmax_lo u v j Aj) in Hkj. lia.
      * assert (Ak : (length u < k)%nat) by lia.
        assert (Ck : (k - S (length u) < length v)%nat) by lia.
        assert (Bk : (nth (k - S (length u)) v 0%nat < n)%nat)
          by (apply Bv; exact Ck).
        assert (Hi : (length u < i)%nat).
        { destruct (Nat.lt_ge_cases i (length u)) as [Hi1 | Hi2].
          - exfalso.
            rewrite (midmax_lo u v i Hi1), (midmax_hi u v k Ak) in Hik. lia.
          - destruct (Nat.eq_dec i (length u)) as [He | Hne]; [|lia].
            exfalso.
            rewrite He, midmax_mid, (midmax_hi u v k Ak) in Hik. lia. }
        right.
        exists (i - S (length u))%nat, (j - S (length u))%nat,
               (k - S (length u))%nat.
        unfold has_132_at.
        assert (Aj : (length u < j)%nat) by lia.
        rewrite (midmax_hi u v i Hi) in Hik.
        rewrite (midmax_hi u v k Ak) in Hik, Hkj.
        rewrite (midmax_hi u v j Aj) in Hkj.
        repeat split; lia.
  - intros [H | H].
    + destruct H as [i [j [k H]]]. unfold has_132_at in H.
      destruct H as [Hij [Hjk [Hk [Hik Hkj]]]].
      exists i, j, k. unfold has_132_at. rewrite midmax_length.
      rewrite (midmax_lo u v i ltac:(lia)), (midmax_lo u v j ltac:(lia)),
              (midmax_lo u v k ltac:(lia)).
      repeat split; lia.
    + destruct H as [i [j [k H]]]. unfold has_132_at in H.
      destruct H as [Hij [Hjk [Hk [Hik Hkj]]]].
      exists (S (length u) + i)%nat, (S (length u) + j)%nat,
             (S (length u) + k)%nat.
      unfold has_132_at. rewrite midmax_length.
      rewrite (midmax_hi u v (S (length u) + i)%nat ltac:(lia)),
              (midmax_hi u v (S (length u) + j)%nat ltac:(lia)),
              (midmax_hi u v (S (length u) + k)%nat ltac:(lia)).
      replace (S (length u) + i - S (length u))%nat with i by lia.
      replace (S (length u) + j - S (length u))%nat with j by lia.
      replace (S (length u) + k - S (length u))%nat with k by lia.
      repeat split; lia.
Qed.

Corollary midmax_avoids : forall u v m n,
  is_perm u m -> is_perm v n ->
  (~ contains_132 (midmax u v) <-> (~ contains_132 u /\ ~ contains_132 v)).
Proof.
  intros u v m n Hu Hv.
  destruct (midmax_132 u v m n Hu Hv) as [Hf Hb]. split.
  - intro H. split; intro C; apply H; apply Hb; [left | right]; exact C.
  - intros [H1 H2] C. destruct (Hf C) as [C' | C']; [apply H1 | apply H2]; exact C'.
Qed.

Theorem midmax_perm : forall u v m n,
  is_perm u m -> is_perm v n -> is_perm (midmax u v) (S (m + n)).
Proof.
  intros u v m n [Hlu [Hnu Hbu]] [Hlv [Hnv Hbv]]. unfold midmax.
  split; [| split].
  - rewrite len_app, len_map_add. simpl. lia.
  - apply NoDup_app_disj.
    + apply NoDup_map_add; exact Hnu.
    + constructor; [| exact Hnv].
      intro Hin. apply Hbv in Hin. lia.
    + intros x Hx Hy. apply in_map_iff in Hx. destruct Hx as [y [Hxy Hin]].
      apply Hbu in Hin. simpl in Hy. destruct Hy as [He | Hy].
      * lia.
      * apply Hbv in Hy. lia.
  - intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx | Hx].
    + apply in_map_iff in Hx. destruct Hx as [y [Hy Hin]].
      apply Hbu in Hin. lia.
    + simpl in Hx. destruct Hx as [He | Hx]; [lia | apply Hbv in Hx; lia].
Qed.

Lemma midmax_inj : forall u v u' v',
  length v = length v' -> midmax u v = midmax u' v' -> u = u' /\ v = v'.
Proof.
  intros u v u' v' Hv He.
  assert (Htot : (length u + S (length v) = length u' + S (length v'))%nat)
    by (rewrite <- (midmax_length u v), <- (midmax_length u' v'), He; reflexivity).
  assert (Hlu : length u = length u') by lia.
  unfold midmax in He.
  assert (Hml : length (map (fun x => (x + length v)%nat) u)
              = length (map (fun x => (x + length v')%nat) u'))
    by (rewrite !len_map_add; exact Hlu).
  destruct (app_split_eq _ _ _ _ Hml He) as [H1 H2].
  injection H2 as _ H2v.
  split; [| exact H2v].
  rewrite Hv in H1. exact (map_add_inj (length v') u u' H1).
Qed.

Lemma nth_map_add : forall c l t, (t < length l)%nat ->
  nth t (map (fun x => (x + c)%nat) l) 0%nat = (nth t l 0%nat + c)%nat.
Proof.
  intros c l t H.
  erewrite nth_indep by (rewrite len_map_add; exact H).
  rewrite map_nth. reflexivity.
Qed.

Lemma contains_132_addc : forall c l,
  contains_132 (map (fun x => (x + c)%nat) l) <-> contains_132 l.
Proof.
  intros c l. split; intros [i [j [k H]]]; unfold has_132_at in H;
    destruct H as [Hij [Hjk [Hk [Hik Hkj]]]]; exists i, j, k; unfold has_132_at.
  - rewrite len_map_add in Hk.
    assert (Ai : (i < length l)%nat) by lia.
    assert (Aj : (j < length l)%nat) by lia.
    assert (Ak : (k < length l)%nat) by lia.
    rewrite (nth_map_add c l i Ai) in Hik.
    rewrite (nth_map_add c l k Ak) in Hik, Hkj.
    rewrite (nth_map_add c l j Aj) in Hkj.
    repeat split; lia.
  - rewrite len_map_add.
    rewrite (nth_map_add c l i ltac:(lia)), (nth_map_add c l j ltac:(lia)),
            (nth_map_add c l k ltac:(lia)).
    repeat split; lia.
Qed.

(* A permutation of [0,m) contains every value below m. *)
Lemma perm_full : forall w m, is_perm w m -> forall t, (t < m)%nat -> In t w.
Proof.
  intros w m Hp t Ht. destruct Hp as [Hlen [Hnd Hb]].
  assert (Hincl : incl w (seq 0 m)).
  { intros x Hx. apply in_seq. split; [lia | apply Hb; exact Hx]. }
  assert (Hlen' : (length (seq 0 m) <= length w)%nat)
    by (rewrite length_seq, Hlen; lia).
  assert (H := NoDup_length_incl Hnd Hlen' Hincl).
  apply H. apply in_seq. lia.
Qed.

(* Every 132-avoider is a midmax, so the decomposition is exact. *)
Theorem midmax_split : forall w m,
  is_perm w (S m) -> ~ contains_132 w ->
  exists u, exists v,
    midmax u v = w /\ (length u + length v = m)%nat /\
    is_perm u (length u) /\ is_perm v (length v) /\
    ~ contains_132 u /\ ~ contains_132 v.
Proof.
  intros w m Hp H132.
  assert (Hne : w <> []).
  { destruct Hp as [Hlen _]. intro Hc. subst w. simpl in Hlen. discriminate. }
  assert (Hnd : NoDup w) by av.
  destruct (exists_max_split w Hnd Hne) as [pre [n [suf [Heq [Hpre Hsuf]]]]].
  assert (Hlen : length w = S m) by av.
  assert (Hsplit : (length pre + S (length suf) = S m)%nat)
    by (rewrite Heq, len_app in Hlen; simpl in Hlen; lia).
  assert (Hnm : n = m).
  { assert (Hin : In n w)
      by (rewrite Heq; apply in_or_app; right; left; reflexivity).
    assert (Hnlt : (n < S m)%nat) by (destruct Hp as [_ [_ Hb]]; apply Hb; exact Hin).
    assert (Hm : In m w) by (apply (perm_full w (S m) Hp); lia).
    rewrite Heq in Hm. apply in_app_or in Hm. destruct Hm as [Hm | Hm].
    - specialize (Hpre m Hm). lia.
    - simpl in Hm. destruct Hm as [He | Hm]; [lia | specialize (Hsuf m Hm); lia]. }
  assert (Hdom : forall a b, In a pre -> In b suf -> (b < a)%nat).
  { intros a b Ha Hb.
    assert (Hle : (b <= a)%nat).
    { apply (split_132_dominates pre suf n Hpre Hsuf); try assumption.
      rewrite <- Heq. exact H132. }
    destruct (Nat.eq_dec b a) as [He | Hne2]; [|lia].
    exfalso. subst b. rewrite Heq in Hnd.
    apply (nodup_app_disjoint pre (n :: suf) a Hnd Ha). right. exact Hb. }
  assert (Hsufv : forall s, In s suf -> (s < length suf)%nat).
  { intros s Hs.
    assert (Hsub : incl (seq 0 (S s)) suf).
    { intros t Ht. apply in_seq in Ht.
      assert (Htw : In t w) by (apply (perm_full w (S m) Hp); specialize (Hsuf s Hs); lia).
      rewrite Heq in Htw. apply in_app_or in Htw. destruct Htw as [Htw | Htw].
      - exfalso. specialize (Hdom t s Htw Hs). lia.
      - simpl in Htw. destruct Htw as [He | Htw]; [| exact Htw].
        exfalso. specialize (Hsuf s Hs). lia. }
    assert (Hnds : NoDup suf).
    { rewrite Heq in Hnd. assert (K : NoDup (n :: suf)) by (apply (nodup_app_r pre); exact Hnd).
      inversion K; assumption. }
    assert (K := NoDup_incl_length (seq_NoDup (S s) 0) Hsub).
    rewrite length_seq in K. lia. }
  assert (Hprev : forall a, In a pre -> (length suf <= a)%nat).
  { intros a Ha.
    assert (Hsub : incl suf (seq 0 a)).
    { intros t Ht. apply in_seq. split; [lia | apply (Hdom a t Ha Ht)]. }
    assert (Hnds : NoDup suf).
    { rewrite Heq in Hnd. assert (K : NoDup (n :: suf)) by (apply (nodup_app_r pre); exact Hnd).
      inversion K; assumption. }
    assert (K := NoDup_incl_length Hnds Hsub).
    rewrite length_seq in K. lia. }
  exists (map (fun x => (x - length suf)%nat) pre), suf.
  assert (Hback : map (fun x => (x + length suf)%nat)
                      (map (fun x => (x - length suf)%nat) pre) = pre).
  { rewrite map_map. rewrite <- (map_id pre) at 2. apply map_ext_in.
    intros a Ha. specialize (Hprev a Ha). lia. }
  assert (Hlu : length (map (fun x => (x - length suf)%nat) pre) = length pre)
    by apply len_map_gen.
  assert (Hnds : NoDup suf).
  { rewrite Heq in Hnd.
    assert (K : NoDup (n :: suf)) by (apply (nodup_app_r pre); exact Hnd).
    inversion K; assumption. }
  assert (Hndp : NoDup pre).
  { rewrite Heq in Hnd. clear -Hnd.
    induction pre as [|a p IH]; [constructor|].
    inversion Hnd as [|z r Hz Hnd' Hq]; subst.
    constructor; [intro Hc; apply Hz; apply in_or_app; left; exact Hc
                 | apply IH; exact Hnd']. }
  assert (Hw : midmax (map (fun x => (x - length suf)%nat) pre) suf = w).
  { unfold midmax. rewrite Hback, Hlu, Heq, Hnm.
    replace (length pre + length suf)%nat with m by lia. reflexivity. }
  assert (Hsum : (length (map (fun x => (x - length suf)%nat) pre)
                  + length suf)%nat = m) by (rewrite Hlu; lia).
  assert (Hpu : is_perm (map (fun x => (x - length suf)%nat) pre)
                        (length (map (fun x => (x - length suf)%nat) pre))).
  { split; [reflexivity | split].
    - apply nodup_map_inj_in; [| exact Hndp].
      intros x y Hx Hy He.
      assert (Ax := Hprev x Hx). assert (Ay := Hprev y Hy). lia.
    - intros x Hx. rewrite Hlu. apply in_map_iff in Hx.
      destruct Hx as [a [Ha Hin]]. specialize (Hprev a Hin).
      assert (Halt : (a < m)%nat) by (specialize (Hpre a Hin); lia). lia. }
  assert (Hpv : is_perm suf (length suf)).
  { split; [reflexivity | split; [exact Hnds | exact Hsufv]]. }
  assert (Hcu : ~ contains_132 (map (fun x => (x - length suf)%nat) pre)).
  { intro C. apply (contains_132_addc (length suf)) in C.
    rewrite Hback in C. apply (prefix_avoids_132 pre (n :: suf)); [| exact C].
    rewrite <- Heq. exact H132. }
  assert (Hcv : ~ contains_132 suf).
  { apply (suffix_avoids_132 (pre ++ [n])).
    rewrite <- app_assoc. simpl. rewrite <- Heq. exact H132. }
  split; [exact Hw|].
  split; [exact Hsum|].
  split; [exact Hpu|].
  split; [exact Hpv|].
  split; [exact Hcu | exact Hcv].
Qed.

(* The maximum sits at one position, so the split point is recoverable. *)
Lemma midmax_max_unique : forall u v m n t,
  is_perm u m -> is_perm v n ->
  (t < length u + S (length v))%nat ->
  nth t (midmax u v) 0%nat = (length u + length v)%nat -> t = length u.
Proof.
  intros u v m n t Hu Hv Ht He.
  assert (Hlu : length u = m) by av.
  assert (Hlv : length v = n) by av.
  destruct (Nat.lt_trichotomy t (length u)) as [K | [K | K]]; [| exact K |].
  - exfalso. rewrite (midmax_lo u v t K) in He.
    assert (nth t u 0%nat < m)%nat
      by (destruct Hu as [_ [_ Hb]]; apply Hb; apply nth_In; lia). lia.
  - exfalso. rewrite (midmax_hi u v t K) in He.
    assert (nth (t - S (length u)) v 0%nat < n)%nat
      by (destruct Hv as [_ [_ Hb]]; apply Hb; apply nth_In; lia). lia.
Qed.

Lemma midmax_len_eq : forall u v u' v' m n m' n',
  is_perm u m -> is_perm v n -> is_perm u' m' -> is_perm v' n' ->
  midmax u v = midmax u' v' -> length u = length u'.
Proof.
  intros u v u' v' m n m' n' Hu Hv Hu' Hv' He.
  assert (Htot : (length u + S (length v) = length u' + S (length v'))%nat)
    by (rewrite <- (midmax_length u v), <- (midmax_length u' v'), He; reflexivity).
  apply (midmax_max_unique u' v' m' n' (length u) Hu' Hv'); [lia|].
  rewrite <- He, midmax_mid. lia.
Qed.

(* Standardisation, and the pattern of the length-d suffix. *)

Lemma dsort_length : forall l, length (dsort l) = length l.
Proof. intro l. symmetry. apply Permutation_length. apply dsort_perm. Qed.

Lemma dsort_In : forall l x, In x (dsort l) <-> In x l.
Proof.
  intros l x. split; intro H.
  - apply (Permutation_in x (Permutation_sym (dsort_perm l))). exact H.
  - apply (Permutation_in x (dsort_perm l)). exact H.
Qed.

(* The descending rearrangement lands in the class. *)
Theorem dsort_avoids : forall pre suf,
  ~ contains_132 pre -> NoDup suf ->
  ~ contains_1324 (pre ++ dsort suf).
Proof.
  intros pre suf Hpre Hnd.
  apply decreasing_tail_avoids; [exact Hpre|].
  intros t t' Ht Ht'.
  apply sortedD_strict; [| apply dsort_sortedD | exact Ht | exact Ht'].
  apply (Permutation_NoDup (dsort_perm suf)). exact Hnd.
Qed.

Definition rankin (u : list nat) (x : nat) : nat :=
  length (filter (fun y => y <? x) u).

(* Rank determines the entry, which makes the rearrangement injective per pattern. *)
Lemma rankin_lt : forall l x y, NoDup l -> In x l -> In y l -> (x < y)%nat ->
  (rankin l x < rankin l y)%nat.
Proof.
  intros l x y Hnd Hx Hy Hxy. unfold rankin.
  assert (Hnd2 : NoDup (x :: filter (fun z => z <? x) l)).
  { constructor.
    - intro Hin. apply filter_In in Hin. destruct Hin as [_ Hlt].
      apply Nat.ltb_lt in Hlt. lia.
    - apply NoDup_filter. exact Hnd. }
  assert (Hsub : incl (x :: filter (fun z => z <? x) l)
                      (filter (fun z => z <? y) l)).
  { intros a Ha. apply filter_In. destruct Ha as [Ha|Ha].
    - subst a. split; [exact Hx | apply Nat.ltb_lt; exact Hxy].
    - apply filter_In in Ha. destruct Ha as [Hal Hlt].
      apply Nat.ltb_lt in Hlt. split; [exact Hal | apply Nat.ltb_lt; lia]. }
  assert (Hlen := NoDup_incl_length Hnd2 Hsub).
  simpl in Hlen. lia.
Qed.

Lemma rankin_inj : forall l x y, NoDup l -> In x l -> In y l ->
  rankin l x = rankin l y -> x = y.
Proof.
  intros l x y Hnd Hx Hy He.
  destruct (Nat.lt_trichotomy x y) as [H|[H|H]]; [| exact H |].
  - exfalso.
    assert (rankin l x < rankin l y)%nat by (apply rankin_lt; assumption). lia.
  - exfalso.
    assert (rankin l y < rankin l x)%nat by (apply rankin_lt; assumption). lia.
Qed.

Definition std (u : list nat) : list nat := map (rankin u) u.

Lemma map_nth_def : forall (f : nat -> nat) l t, (t < length l)%nat ->
  nth t (map f l) 0%nat = f (nth t l 0%nat).
Proof.
  intros f l t H.
  erewrite nth_indep by (rewrite len_map_gen; exact H).
  rewrite map_nth. reflexivity.
Qed.

Lemma perm_filter : forall (f : nat -> bool) l l',
  Permutation l l' -> Permutation (filter f l) (filter f l').
Proof.
  intros f l l' H. induction H; simpl.
  - apply Permutation_refl.
  - destruct (f x); [apply perm_skip; exact IHPermutation | exact IHPermutation].
  - destruct (f x); destruct (f y); simpl;
      auto using Permutation_refl, perm_swap.
  - eapply Permutation_trans; eassumption.
Qed.

(* Rank depends only on the multiset, so rearranging a list leaves it alone. *)
Lemma rankin_perm : forall l l', Permutation l l' ->
  forall x, rankin l x = rankin l' x.
Proof.
  intros l l' H x. unfold rankin.
  apply Permutation_length. apply perm_filter. exact H.
Qed.

(* Same multiset and same standardisation force equality. *)
Theorem std_perm_eq : forall s1 s2,
  Permutation s1 s2 -> NoDup s1 -> length s1 = length s2 ->
  std s1 = std s2 -> s1 = s2.
Proof.
  intros s1 s2 Hp Hnd Hlen Hstd.
  apply (nth_ext s1 s2 0%nat 0%nat); [exact Hlen|].
  intros t Ht.
  assert (E : nth t (map (rankin s1) s1) 0%nat
            = nth t (map (rankin s2) s2) 0%nat)
    by (unfold std in Hstd; rewrite Hstd; reflexivity).
  rewrite (map_nth_def (rankin s1) s1 t Ht) in E.
  rewrite (map_nth_def (rankin s2) s2 t ltac:(lia)) in E.
  rewrite <- (rankin_perm s1 s2 Hp (nth t s2 0%nat)) in E.
  apply (rankin_inj s1); [exact Hnd | apply nth_In; lia | | exact E].
  apply (Permutation_in _ (Permutation_sym Hp)). apply nth_In; lia.
Qed.

Lemma filter_all_true : forall (f : nat -> bool) l,
  (forall x, In x l -> f x = true) -> filter f l = l.
Proof.
  intros f. induction l as [|a r IH]; intro H; simpl; [reflexivity|].
  rewrite (H a (or_introl eq_refl)). f_equal. apply IH.
  intros x Hx. apply H. right. exact Hx.
Qed.

(* In a descending duplicate-free list rank counts positions from the far end. *)
Lemma dec_rankin : forall l, NoDup l -> sortedD l ->
  forall t, (t < length l)%nat ->
  rankin l (nth t l 0%nat) = (length l - 1 - t)%nat.
Proof.
  induction l as [|a r IH]; intros Hnd Hs t Ht; simpl in Ht; [lia|].
  destruct Hs as [Ha Hr].
  inversion Hnd as [|x xs Hnotin Hndr Heq]; subst.
  destruct t as [|t].
  - unfold rankin. simpl nth. simpl filter.
    rewrite Nat.ltb_irrefl.
    rewrite filter_all_true.
    + simpl. lia.
    + intros x Hx. apply Nat.ltb_lt.
      assert (Hle : (x <= a)%nat) by (apply Ha; exact Hx).
      assert (Hne : x <> a) by (intro E; subst; contradiction).
      lia.
  - unfold rankin. simpl nth. simpl filter.
    assert (Hax : (a <? nth t r 0%nat) = false).
    { apply Nat.ltb_ge. apply Ha. apply nth_In. simpl in Ht. lia. }
    rewrite Hax.
    change (length (filter (fun z => z <? nth t r 0%nat) r))
      with (rankin r (nth t r 0%nat)).
    rewrite (IH Hndr Hr t ltac:(simpl in Ht; lia)).
    simpl. lia.
Qed.

Theorem dec_std_nth : forall l, NoDup l -> sortedD l ->
  forall t, (t < length l)%nat ->
  nth t (std l) 0%nat = (length l - 1 - t)%nat.
Proof.
  intros l Hnd Hs t Ht. unfold std.
  rewrite (map_nth_def (rankin l) l t Ht).
  apply dec_rankin; assumption.
Qed.

Lemma is_perm_perm : forall u v m, Permutation u v -> is_perm u m -> is_perm v m.
Proof.
  intros u v m Hp [Hlen [Hnd Hlt]]. split; [| split].
  - rewrite <- (Permutation_length Hp). exact Hlen.
  - apply (Permutation_NoDup Hp). exact Hnd.
  - intros x Hx. apply Hlt.
    apply (Permutation_in _ (Permutation_sym Hp)). exact Hx.
Qed.

Lemma len_seq : forall n a, length (seq a n) = n.
Proof. induction n as [|n IH]; intro a; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(* The pattern a descending rearrangement's suffix standardises to. *)
Definition decpat (d : nat) : list nat := map (fun t => (d - 1 - t)%nat) (seq 0 d).

Lemma decpat_length : forall d, length (decpat d) = d.
Proof. intro d. unfold decpat. rewrite len_map_gen, len_seq. reflexivity. Qed.

Lemma decpat_nth : forall d t, (t < d)%nat ->
  nth t (decpat d) 0%nat = (d - 1 - t)%nat.
Proof.
  intros d t H. unfold decpat.
  rewrite (map_nth_def (fun t => (d - 1 - t)%nat) (seq 0 d) t)
    by (rewrite len_seq; exact H).
  rewrite seq_nth by exact H. reflexivity.
Qed.

Theorem dec_std : forall l, NoDup l -> sortedD l -> std l = decpat (length l).
Proof.
  intros l Hnd Hs.
  apply (nth_ext (std l) (decpat (length l)) 0%nat 0%nat).
  - unfold std. rewrite len_map_gen, decpat_length. reflexivity.
  - intros t Ht. unfold std in Ht. rewrite len_map_gen in Ht.
    rewrite (dec_std_nth l Hnd Hs t Ht).
    rewrite (decpat_nth (length l) t Ht). reflexivity.
Qed.

Lemma strict_dec_sortedD : forall l,
  (forall t t', (t < t')%nat -> (t' < length l)%nat ->
     (nth t' l 0%nat < nth t l 0%nat)%nat) -> sortedD l.
Proof.
  induction l as [|a r IH]; simpl; [intros _; exact I|].
  intro H. split.
  - intros y Hy. apply In_nth with (d := 0%nat) in Hy.
    destruct Hy as [t [Ht Hnth]].
    assert (K := H 0%nat (S t) ltac:(lia) ltac:(simpl; lia)).
    simpl in K. rewrite Hnth in K. lia.
  - apply IH. intros t t' Ht Ht'.
    exact (H (S t) (S t') ltac:(lia) ltac:(simpl; lia)).
Qed.

(* Standardising to the decreasing pattern forces the list to be decreasing. *)
Theorem dec_std_conv : forall l, NoDup l -> std l = decpat (length l) ->
  forall t t', (t < t')%nat -> (t' < length l)%nat ->
    (nth t' l 0%nat < nth t l 0%nat)%nat.
Proof.
  intros l Hnd Hs t t' Ht Ht'.
  assert (Et : rankin l (nth t l 0%nat) = (length l - 1 - t)%nat).
  { rewrite <- (map_nth_def (rankin l) l t ltac:(lia)).
    change (map (rankin l) l) with (std l). rewrite Hs.
    apply decpat_nth. lia. }
  assert (Et' : rankin l (nth t' l 0%nat) = (length l - 1 - t')%nat).
  { rewrite <- (map_nth_def (rankin l) l t' Ht').
    change (map (rankin l) l) with (std l). rewrite Hs.
    apply decpat_nth. exact Ht'. }
  assert (Int : In (nth t l 0%nat) l) by (apply nth_In; lia).
  assert (Int' : In (nth t' l 0%nat) l) by (apply nth_In; exact Ht').
  destruct (Nat.lt_trichotomy (nth t' l 0%nat) (nth t l 0%nat)) as [K | [K | K]].
  - exact K.
  - exfalso. rewrite K in Et'. lia.
  - exfalso.
    assert (rankin l (nth t l 0%nat) < rankin l (nth t' l 0%nat))%nat
      by (apply rankin_lt; assumption).
    lia.
Qed.

Definition suffix_pat (d : nat) (w : list nat) : list nat :=
  std (skipn (length w - d) w).

Lemma avoids132b_true : forall u, avoids132b u = true -> ~ contains_132 u.
Proof.
  intros u H. unfold avoids132b in H.
  destruct (contains_132_dec u); [discriminate | assumption].
Qed.

Lemma avoids132b_intro : forall u, ~ contains_132 u -> avoids132b u = true.
Proof.
  intros u H. unfold avoids132b.
  destruct (contains_132_dec u); [contradiction | reflexivity].
Qed.

Lemma NoDup_skipn : forall (l : list nat) n, NoDup l -> NoDup (skipn n l).
Proof.
  induction l as [|a r IH]; intros n H.
  - destruct n; simpl; constructor.
  - destruct n as [|n]; simpl; [exact H|].
    inversion H as [|x xs Hni Hnd]; subst. apply IH. exact Hnd.
Qed.

(* Replace the suffix by its descending rearrangement, leaving the prefix alone. *)
Definition flatten_suffix (M : nat) (w : list nat) : list nat :=
  firstn M w ++ dsort (skipn M w).

Lemma flatten_perm : forall M w, Permutation w (flatten_suffix M w).
Proof.
  intros M w. unfold flatten_suffix.
  rewrite <- (firstn_skipn M w) at 1.
  apply Permutation_app_head. apply dsort_perm.
Qed.

Lemma flatten_firstn : forall M w, (M <= length w)%nat ->
  firstn M (flatten_suffix M w) = firstn M w.
Proof.
  intros M w H. unfold flatten_suffix.
  rewrite firstn_app, length_firstn.
  replace (Nat.min M (length w)) with M by lia.
  rewrite Nat.sub_diag. simpl. rewrite app_nil_r.
  apply firstn_all2. rewrite length_firstn. lia.
Qed.

Lemma flatten_skipn : forall M w, (M <= length w)%nat ->
  skipn M (flatten_suffix M w) = dsort (skipn M w).
Proof.
  intros M w H. unfold flatten_suffix.
  rewrite skipn_app, length_firstn.
  replace (Nat.min M (length w)) with M by lia.
  rewrite Nat.sub_diag. simpl.
  rewrite skipn_all2 by (rewrite length_firstn; lia). reflexivity.
Qed.

(* N_sigma(M): those counted by D(d,M) whose suffix has pattern sigma. *)
Lemma suffix_pat_skipn : forall d M w, length w = (M + d)%nat ->
  suffix_pat d w = std (skipn M w).
Proof.
  intros d M w H. unfold suffix_pat. rewrite H.
  replace (M + d - d)%nat with M by lia. reflexivity.
Qed.

(* The decreasing suffix fibre without standardisation: 132-free prefix, strictly
   decreasing suffix, avoidance automatic. *)
Theorem dec_fibre_iff : forall d M w,
  length w = (M + d)%nat -> NoDup w ->
  (suffix_pat d w = decpat d <->
   (forall t t', (t < t')%nat -> (t' < d)%nat ->
      (nth t' (skipn M w) 0%nat < nth t (skipn M w) 0%nat)%nat)).
Proof.
  intros d M w Hlen Hnd.
  assert (Hsk : length (skipn M w) = d)
    by (rewrite length_skipn, Hlen; lia).
  assert (Hnds : NoDup (skipn M w)) by (apply NoDup_skipn; exact Hnd).
  rewrite (suffix_pat_skipn d M w Hlen). split.
  - intros Hs t t' Ht Ht'.
    apply (dec_std_conv (skipn M w) Hnds);
      [rewrite Hsk; exact Hs | exact Ht | rewrite Hsk; exact Ht'].
  - intro Hd. rewrite (dec_std (skipn M w) Hnds), Hsk; [reflexivity|].
    apply strict_dec_sortedD. intros t t' Ht Ht'.
    apply Hd; [exact Ht | rewrite Hsk in Ht'; exact Ht'].
Qed.

Corollary dec_fibre_avoids : forall d M w,
  length w = (M + d)%nat -> NoDup w ->
  ~ contains_132 (firstn M w) -> suffix_pat d w = decpat d ->
  ~ contains_1324 w.
Proof.
  intros d M w Hlen Hnd Hpre Hsuf.
  rewrite <- (firstn_skipn M w).
  apply decreasing_tail_avoids; [exact Hpre|].
  intros t t' Ht Ht'.
  assert (Hsk : length (skipn M w) = d)
    by (rewrite length_skipn, Hlen; lia).
  apply (proj1 (dec_fibre_iff d M w Hlen Hnd) Hsuf);
    [exact Ht | rewrite Hsk in Ht'; exact Ht'].
Qed.

Lemma flatten_in_gen : forall d M w,
  In w (gen (M + d)) -> avoids132b (firstn M w) = true ->
  In (flatten_suffix M w) (gen (M + d)).
Proof.
  intros d M w Hw Hp.
  destruct (card_is_cardinality (M + d)) as [_ Hs].
  apply Hs in Hw. destruct Hw as [Hperm Hav].
  apply Hs. split.
  - apply (is_perm_perm w); [apply flatten_perm | exact Hperm].
  - unfold flatten_suffix. apply dsort_avoids.
    + apply avoids132b_true. exact Hp.
    + apply NoDup_skipn. destruct Hperm as [_ [Hnd _]]. exact Hnd.
Qed.

Lemma flatten_pat : forall d M w, length w = (M + d)%nat -> NoDup w ->
  suffix_pat d (flatten_suffix M w) = decpat d.
Proof.
  intros d M w Hlen Hnd.
  assert (Hl : length (flatten_suffix M w) = (M + d)%nat)
    by (rewrite <- (Permutation_length (flatten_perm M w)); exact Hlen).
  rewrite (suffix_pat_skipn d M) by exact Hl.
  rewrite flatten_skipn by lia.
  rewrite dec_std.
  - rewrite dsort_length, length_skipn, Hlen. f_equal. lia.
  - apply (Permutation_NoDup (dsort_perm (skipn M w))).
    apply NoDup_skipn. exact Hnd.
  - apply dsort_sortedD.
Qed.

Lemma flatten_inj : forall d M sg w1 w2,
  length w1 = (M + d)%nat -> length w2 = (M + d)%nat -> NoDup w1 ->
  suffix_pat d w1 = sg -> suffix_pat d w2 = sg ->
  flatten_suffix M w1 = flatten_suffix M w2 -> w1 = w2.
Proof.
  intros d M sg w1 w2 H1 H2 Hnd Hs1 Hs2 He.
  assert (Hf : firstn M w1 = firstn M w2).
  { rewrite <- (flatten_firstn M w1) by lia.
    rewrite <- (flatten_firstn M w2) by lia. rewrite He. reflexivity. }
  assert (Hd : dsort (skipn M w1) = dsort (skipn M w2)).
  { rewrite <- (flatten_skipn M w1) by lia.
    rewrite <- (flatten_skipn M w2) by lia. rewrite He. reflexivity. }
  assert (Hp : Permutation (skipn M w1) (skipn M w2)).
  { eapply Permutation_trans; [apply dsort_perm|].
    rewrite Hd. apply Permutation_sym. apply dsort_perm. }
  assert (Hst : std (skipn M w1) = std (skipn M w2)).
  { rewrite <- (suffix_pat_skipn d M w1) by exact H1.
    rewrite <- (suffix_pat_skipn d M w2) by exact H2.
    rewrite Hs1, Hs2. reflexivity. }
  assert (Hsk : skipn M w1 = skipn M w2).
  { apply std_perm_eq;
      [exact Hp | apply NoDup_skipn; exact Hnd | | exact Hst].
    rewrite !length_skipn. lia. }
  rewrite <- (firstn_skipn M w1), <- (firstn_skipn M w2), Hf, Hsk. reflexivity.
Qed.

Definition Nsig (d M : nat) (sg : list nat) : nat :=
  length (filter (fun w =>
            andb (avoids132b (firstn M w))
                 (if list_eq_dec Nat.eq_dec (suffix_pat d w) sg
                  then true else false))
          (gen (M + d))).

(* The decreasing pattern is the largest fibre. *)
Theorem Nsig_le_dec : forall d M sg,
  (Nsig d M sg <= Nsig d M (decpat d))%nat.
Proof.
  intros d M sg. unfold Nsig.
  rewrite <- (len_map_gen _ _ (flatten_suffix M)
    (filter (fun w => andb (avoids132b (firstn M w))
              (if list_eq_dec Nat.eq_dec (suffix_pat d w) sg then true else false))
            (gen (M + d)))).
  apply NoDup_incl_length.
  - apply NoDup_map_inj; [apply NoDup_filter; apply gen_nodup|].
    intros x y Hx Hy He.
    apply filter_In in Hx. destruct Hx as [Hxg Hxf].
    apply filter_In in Hy. destruct Hy as [Hyg Hyf].
    apply andb_true_iff in Hxf. destruct Hxf as [_ Hxs].
    apply andb_true_iff in Hyf. destruct Hyf as [_ Hys].
    destruct (list_eq_dec Nat.eq_dec (suffix_pat d x) sg) as [Ex|];
      [|discriminate].
    destruct (list_eq_dec Nat.eq_dec (suffix_pat d y) sg) as [Ey|];
      [|discriminate].
    destruct (card_is_cardinality (M + d)) as [_ Hs].
    apply Hs in Hxg. apply Hs in Hyg.
    destruct Hxg as [[Hlx [Hndx _]] _]. destruct Hyg as [[Hly _] _].
    exact (flatten_inj d M sg x y Hlx Hly Hndx Ex Ey He).
  - intros z Hz. apply in_map_iff in Hz. destruct Hz as [w [Hw Hin]].
    apply filter_In in Hin. destruct Hin as [Hg Hf].
    apply andb_true_iff in Hf. destruct Hf as [Hav _].
    destruct (card_is_cardinality (M + d)) as [_ Hs].
    assert (Hg' := Hg). apply Hs in Hg'.
    destruct Hg' as [[Hl [Hnd _]] _].
    subst z. apply filter_In. split.
    + apply flatten_in_gen; assumption.
    + apply andb_true_iff. split.
      * rewrite flatten_firstn by lia. exact Hav.
      * rewrite (flatten_pat d M w Hl Hnd).
        destruct (list_eq_dec Nat.eq_dec (decpat d) (decpat d));
          [reflexivity | contradiction].
Qed.

(* D(d,M) = sum over suffix patterns of N_sigma(M). *)
Theorem Ddiag_partition : forall d M (keys : list (list nat)),
  NoDup keys ->
  (forall w, In w (filter (fun w => avoids132b (firstn M w)) (gen (M + d))) ->
             In (suffix_pat d w) keys) ->
  Ddiag d M = fold_right (fun sg acc => (Nsig d M sg + acc)%nat) 0%nat keys.
Proof.
  intros d M keys Hnd Hcov. unfold Ddiag.
  rewrite (length_fibres (list nat) (list nat) (list_eq_dec Nat.eq_dec)
             (suffix_pat d) keys _ Hnd Hcov).
  apply fold_ext. intro sg. unfold Nsig.
  rewrite <- filter_filter. reflexivity.
Qed.

(* An enumerator for Av(132), mirroring gen: appending creates a 132 exactly when
   the new letter plays the '2', which is the failure of safe_at. *)

Lemma append_132 : forall u y,
  contains_132 (u ++ [y]) <->
  (contains_132 u \/ exists i j, (i < j)%nat /\ (j < length u)%nat /\
     (nth i u 0%nat < y)%nat /\ (y < nth j u 0%nat)%nat).
Proof.
  intros u y. split.
  - intros [i [j [k H]]]. unfold has_132_at in H.
    destruct H as [Hij [Hjk [Hklen [Hik Hkj]]]].
    rewrite len_app in Hklen. simpl in Hklen.
    destruct (Nat.eq_dec k (length u)) as [Hk | Hk].
    + right. exists i, j. rewrite Hk in Hik, Hkj. rewrite nth_last in Hik, Hkj.
      rewrite (nth_app1 u [y] i 0%nat) in Hik by lia.
      rewrite (nth_app1 u [y] j 0%nat) in Hkj by lia.
      repeat split; try lia; assumption.
    + left. exists i, j, k. unfold has_132_at.
      rewrite (nth_app1 u [y] i 0%nat) in Hik by lia.
      rewrite (nth_app1 u [y] k 0%nat) in Hik by lia.
      rewrite (nth_app1 u [y] k 0%nat) in Hkj by lia.
      rewrite (nth_app1 u [y] j 0%nat) in Hkj by lia.
      repeat split; try lia; assumption.
  - intros [H | [i [j [Hij [Hj [Hi Hjy]]]]]].
    + destruct H as [i [j [k H]]]. unfold has_132_at in H.
      destruct H as [Hij [Hjk [Hklen [Hik Hkj]]]].
      exists i, j, k. unfold has_132_at.
      rewrite (nth_app1 u [y] i 0%nat) by lia.
      rewrite (nth_app1 u [y] j 0%nat) by lia.
      rewrite (nth_app1 u [y] k 0%nat) by lia.
      rewrite len_app. simpl. repeat split; try lia; assumption.
    + exists i, j, (length u). unfold has_132_at.
      rewrite nth_last.
      rewrite (nth_app1 u [y] i 0%nat) by lia.
      rewrite (nth_app1 u [y] j 0%nat) by lia.
      rewrite len_app. simpl. repeat split; try lia; assumption.
Qed.

Lemma bump_gt_v : forall v x, (v < bump v x)%nat <-> (v <= x)%nat.
Proof.
  intros v x. unfold bump. destruct (Nat.leb_spec v x); lia.
Qed.

(* Renormalising turns the strict test of append_132 into the safe_at test. *)
Theorem ext_132 : forall u v,
  contains_132 (ext u v) <-> (contains_132 u \/ ~ safe_at u v).
Proof.
  intros u v. unfold ext. rewrite (append_132 (map (bump v) u) v).
  rewrite (contains_132_map v u). split.
  - intros [H | [i [j [Hij [Hj [Hi Hjv]]]]]]; [left; exact H | right].
    rewrite len_map in Hj.
    rewrite (nth_map_in (bump v) u i) in Hi by lia.
    rewrite (nth_map_in (bump v) u j) in Hjv by lia.
    apply (bump_lt_v v (nth i u 0%nat)) in Hi.
    apply (bump_gt_v v (nth j u 0%nat)) in Hjv.
    intro Hs. apply Hs. exists i, j. repeat split; try lia.
  - intros [H | H]; [left; exact H | right].
    unfold safe_at in H.
    destruct (bounded_ex_dec
      (fun i => exists j, (i < j)%nat /\ (j < length u)%nat /\
                  (nth i u 0%nat < v)%nat /\ (v <= nth j u 0%nat)%nat)
      (length u)) as [Hex | Hno].
    { intro i.
      destruct (bounded_ex_dec
        (fun j => (i < j)%nat /\ (j < length u)%nat /\
                  (nth i u 0%nat < v)%nat /\ (v <= nth j u 0%nat)%nat)
        (length u)) as [K | K].
      - intro j.
        destruct (lt_dec i j) as [A|A]; [|right; tauto].
        destruct (lt_dec j (length u)) as [B|B]; [|right; tauto].
        destruct (lt_dec (nth i u 0%nat) v) as [C|C]; [|right; tauto].
        destruct (le_dec v (nth j u 0%nat)) as [D|D]; [|right; tauto].
        left. repeat split; assumption.
      - left. destruct K as [j [_ Hj]]. exists j. exact Hj.
      - right. intros [j Hj]. apply K. exists j. split; [lia | exact Hj]. }
    + destruct Hex as [i [_ [j [Hij [Hj [Hi Hjv]]]]]].
      exists i, j. rewrite len_map.
      rewrite (nth_map_in (bump v) u i) by lia.
      rewrite (nth_map_in (bump v) u j) by lia.
      repeat split; try lia.
      * apply (bump_lt_v v (nth i u 0%nat)). exact Hi.
      * apply (bump_gt_v v (nth j u 0%nat)). exact Hjv.
    + exfalso. apply H. intros [i [j [Hij [Hj [Hi Hjv]]]]].
      apply Hno. exists i. split; [lia|]. exists j. repeat split; assumption.
Qed.

Lemma safe_at_dec : forall u v, {safe_at u v} + {~ safe_at u v}.
Proof.
  intros u v. unfold safe_at.
  destruct (bounded_ex_dec
    (fun i => exists j, (i < j)%nat /\ (j < length u)%nat /\
                (nth i u 0%nat < v)%nat /\ (v <= nth j u 0%nat)%nat)
    (length u)) as [Hex | Hno].
  { intro i.
    destruct (bounded_ex_dec
      (fun j => (i < j)%nat /\ (j < length u)%nat /\
                (nth i u 0%nat < v)%nat /\ (v <= nth j u 0%nat)%nat)
      (length u)) as [K | K].
    - intro j.
      destruct (lt_dec i j) as [A|A]; [|right; tauto].
      destruct (lt_dec j (length u)) as [B|B]; [|right; tauto].
      destruct (lt_dec (nth i u 0%nat) v) as [C|C]; [|right; tauto].
      destruct (le_dec v (nth j u 0%nat)) as [D|D]; [|right; tauto].
      left. repeat split; assumption.
    - left. destruct K as [j [_ Hj]]. exists j. exact Hj.
    - right. intros [j Hj]. apply K. exists j. split; [lia | exact Hj]. }
  - right. intro Hs. apply Hs.
    destruct Hex as [i [_ [j Hj]]]. exists i, j. exact Hj.
  - left. intros [i [j [Hij [Hj [Hi Hjv]]]]].
    apply Hno. exists i. split; [lia|]. exists j. repeat split; assumption.
Defined.

Definition safeb (u : list nat) (v : nat) : bool :=
  if safe_at_dec u v then true else false.

Lemma safeb_spec : forall u v, safeb u v = true <-> safe_at u v.
Proof.
  intros u v. unfold safeb. destruct (safe_at_dec u v) as [H | H].
  - split; [intros _; exact H | reflexivity].
  - split; [discriminate | intro C; contradiction].
Qed.

Fixpoint gen132 (m : nat) : list (list nat) :=
  match m with
  | 0%nat => [[]]
  | S m' => flat_map (fun u => map (ext u) (filter (safeb u) (seq 0 (S m'))))
                     (gen132 m')
  end.

Lemma gen132_S : forall m,
  gen132 (S m) =
  flat_map (fun u => map (ext u) (filter (safeb u) (seq 0 (S m)))) (gen132 m).
Proof. intro m. reflexivity. Qed.

Lemma nil_avoids_132 : ~ contains_132 [].
Proof. intros [i [j [k H]]]. unfold has_132_at in H. simpl in H. lia. Qed.

Theorem gen132_sound : forall m w,
  In w (gen132 m) -> is_perm w m /\ ~ contains_132 w.
Proof.
  induction m as [|m IH]; intros w Hw.
  - simpl in Hw. destruct Hw as [<- | []].
    split; [| apply nil_avoids_132].
    split; [reflexivity | split; [constructor | intros x Hx; destruct Hx]].
  - rewrite gen132_S in Hw.
    apply in_flat_map in Hw. destruct Hw as [u [Hu Hw]].
    apply in_map_iff in Hw. destruct Hw as [v [Hv Hvin]].
    apply filter_In in Hvin. destruct Hvin as [Hseq Hsafe].
    apply in_seq in Hseq.
    destruct (IH u Hu) as [Hpu Hau]. subst w.
    split.
    + apply ext_perm; [exact Hpu | lia].
    + intro C. destruct (proj1 (ext_132 u v) C) as [K | K].
      * exact (Hau K).
      * exact (K (proj1 (safeb_spec u v) Hsafe)).
Qed.

Theorem gen132_complete : forall m w,
  is_perm w m -> ~ contains_132 w -> In w (gen132 m).
Proof.
  induction m as [|m IH]; intros w Hp Hav.
  - simpl. destruct Hp as [Hlen _]. destruct w as [|a w]; [left; reflexivity|].
    simpl in Hlen. discriminate.
  - rewrite gen132_S.
    destruct (ext_bijection w m Hp) as [u [v [Hw [Hpu [Hvm _]]]]].
    assert (Hu : ~ contains_132 u).
    { intro C. apply Hav. rewrite Hw. apply ext_132. left. exact C. }
    assert (Hs : safe_at u v).
    { destruct (safe_at_dec u v) as [K | K]; [exact K|].
      exfalso. apply Hav. rewrite Hw. apply ext_132. right. exact K. }
    apply in_flat_map. exists u. split.
    + apply IH; [exact Hpu | exact Hu].
    + apply in_map_iff. exists v. split; [symmetry; exact Hw|].
      apply filter_In. split; [apply in_seq; lia | apply safeb_spec; exact Hs].
Qed.

Corollary gen132_spec : forall m w,
  In w (gen132 m) <-> (is_perm w m /\ ~ contains_132 w).
Proof.
  intros m w. split; [apply gen132_sound | intros [H1 H2]; apply gen132_complete; assumption].
Qed.

Theorem gen132_nodup : forall m, NoDup (gen132 m).
Proof.
  induction m as [|m IH].
  - simpl. constructor; [intros [] | constructor].
  - rewrite gen132_S. apply nodup_flat_map; [exact IH | |].
    + intros u Hu. apply nodup_map_inj.
      * intros a b Hab. apply ext_inj in Hab. destruct Hab as [_ Hv]. exact Hv.
      * apply NoDup_filter. apply seq_NoDup.
    + intros u u' w Hu Hu' Hw Hw'.
      apply in_map_iff in Hw. destruct Hw as [v [Hv _]].
      apply in_map_iff in Hw'. destruct Hw' as [v' [Hv' _]].
      rewrite <- Hv in Hv'. apply ext_inj in Hv'.
      destruct Hv' as [Hu2 _]. symmetry. exact Hu2.
Qed.

Lemma gen132_perm : forall m w, In w (gen132 m) -> is_perm w m.
Proof. intros m w H. exact (proj1 (gen132_sound m w H)). Qed.

Lemma gen132_av : forall m w, In w (gen132 m) -> ~ contains_132 w.
Proof. intros m w H. exact (proj2 (gen132_sound m w H)). Qed.

#[export] Hint Resolve gen132_perm gen132_av gen132_nodup : av1324.

Definition card132 (m : nat) : nat := length (gen132 m).

Theorem card132_is_cardinality : forall m,
  NoDup (gen132 m) /\ forall w, In w (gen132 m) <-> (is_perm w m /\ ~ contains_132 w).
Proof. intro m. split; [apply gen132_nodup | apply gen132_spec]. Qed.

(* Every 132-avoider avoids 1324, so gen132 lands inside gen. *)
Corollary gen132_incl : forall m w, In w (gen132 m) -> In w (gen m).
Proof.
  intros m w Hw. apply gen132_spec in Hw. destruct Hw as [Hp Hav].
  apply gen_spec. split; [exact Hp | apply empty_tail_avoids; exact Hav].
Qed.

Corollary card132_le_card : forall m, (card132 m <= card m)%nat.
Proof.
  intro m. unfold card132, card.
  apply NoDup_incl_length;
    [apply gen132_nodup | intros a Ha; exact (gen132_incl m a Ha)].
Qed.

Lemma length_flat_map_gen : forall (A B : Type) (f : A -> list B) (l : list A),
  length (flat_map f l)
  = fold_right (fun x acc => (length (f x) + acc)%nat) 0%nat l.
Proof.
  intros A B f. induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite len_app_gen, IH. reflexivity.
Qed.

Definition pairs132 (m : nat) : list (list nat) :=
  flat_map (fun k => flat_map (fun u => map (midmax u) (gen132 (m - k)))
                              (gen132 k))
           (seq 0 (S m)).


Lemma pairs132_sound : forall m w, In w (pairs132 m) -> In w (gen132 (S m)).
Proof.
  intros m w Hw. unfold pairs132 in Hw.
  apply in_flat_map in Hw. destruct Hw as [k [Hk Hw]].
  apply in_seq in Hk.
  apply in_flat_map in Hw. destruct Hw as [u [Hu Hw]].
  apply in_map_iff in Hw. destruct Hw as [v [Hv Hvin]].
  apply gen132_spec in Hu. destruct Hu as [Hpu Hau].
  apply gen132_spec in Hvin. destruct Hvin as [Hpv Hav].
  subst w. apply gen132_spec. split.
  - replace (S m) with (S (k + (m - k)))%nat by lia.
    exact (midmax_perm u v k (m - k) Hpu Hpv).
  - apply (midmax_avoids u v k (m - k) Hpu Hpv). split; assumption.
Qed.

Lemma pairs132_complete : forall m w, In w (gen132 (S m)) -> In w (pairs132 m).
Proof.
  intros m w Hw. apply gen132_spec in Hw. destruct Hw as [Hp Hav].
  destruct (midmax_split w m Hp Hav)
    as [u [v [Hw' [Hsum [Hpu [Hpv [Hcu Hcv]]]]]]].
  unfold pairs132. apply in_flat_map. exists (length u). split.
  - apply in_seq. lia.
  - apply in_flat_map. exists u. split.
    + apply gen132_spec. split; assumption.
    + apply in_map_iff. exists v. split; [exact Hw'|].
      apply gen132_spec. replace (m - length u)%nat with (length v) by lia.
      split; assumption.
Qed.

Lemma pairs132_nodup : forall m, NoDup (pairs132 m).
Proof.
  intro m. unfold pairs132.
  apply NoDup_flat_map_inj; [apply seq_NoDup | |].
  - intros k Hk. apply NoDup_flat_map_inj; [apply gen132_nodup | |].
    + intros u Hu. apply NoDup_map_inj; [apply gen132_nodup|].
      intros a b Ha Hb Hab.
      apply gen132_spec in Ha. apply gen132_spec in Hb.
      assert (Hl : length a = length b)
        by (destruct Ha as [[H1 _] _]; destruct Hb as [[H2 _] _]; lia).
      exact (proj2 (midmax_inj u a u b Hl Hab)).
    + intros u u' z Hu Hu' Hz Hz'.
      apply in_map_iff in Hz. destruct Hz as [v [Hv Hvin]].
      apply in_map_iff in Hz'. destruct Hz' as [v' [Hv' Hv'in]].
      apply gen132_spec in Hu. apply gen132_spec in Hu'.
      apply gen132_spec in Hvin. apply gen132_spec in Hv'in.
      rewrite <- Hv' in Hv.
      assert (Hl := midmax_len_eq u v u' v' k (m - k) k (m - k)
                      (proj1 Hu) (proj1 Hvin) (proj1 Hu') (proj1 Hv'in) Hv).
      assert (Hlv : length v = length v').
      { assert (Htot : (length u + S (length v) = length u' + S (length v'))%nat)
          by (rewrite <- (midmax_length u v), <- (midmax_length u' v'), Hv;
              reflexivity).
        lia. }
      exact (proj1 (midmax_inj u v u' v' Hlv Hv)).
  - intros k k' z Hk Hk' Hz Hz'.
    apply in_seq in Hk. apply in_seq in Hk'.
    apply in_flat_map in Hz. destruct Hz as [u [Hu Hz]].
    apply in_flat_map in Hz'. destruct Hz' as [u' [Hu' Hz']].
    apply in_map_iff in Hz. destruct Hz as [v [Hv Hvin]].
    apply in_map_iff in Hz'. destruct Hz' as [v' [Hv' Hv'in]].
    apply gen132_spec in Hu. apply gen132_spec in Hu'.
    apply gen132_spec in Hvin. apply gen132_spec in Hv'in.
    rewrite <- Hv' in Hv.
    assert (Hl := midmax_len_eq u v u' v' k (m - k) k' (m - k')
                    (proj1 Hu) (proj1 Hvin) (proj1 Hu') (proj1 Hv'in) Hv).
    destruct Hu as [[Hlu _] _]. destruct Hu' as [[Hlu' _] _]. lia.
Qed.

(* |Av(132)| satisfies the Catalan convolution. *)
Theorem card132_convolution : forall m,
  card132 (S m)
  = fold_right (fun k acc => (card132 k * card132 (m - k) + acc)%nat) 0%nat
               (seq 0 (S m)).
Proof.
  intro m.
  assert (Hlen : card132 (S m) = length (pairs132 m)).
  { unfold card132. apply Nat.le_antisymm.
    - apply NoDup_incl_length;
        [apply gen132_nodup | intros a Ha; exact (pairs132_complete m a Ha)].
    - apply NoDup_incl_length;
        [apply pairs132_nodup | intros a Ha; exact (pairs132_sound m a Ha)]. }
  rewrite Hlen. unfold pairs132. rewrite length_flat_map_gen.
  apply fold_ext. intro k.
  rewrite (len_flat_map_const _ _ (fun u => map (midmax u) (gen132 (m - k)))
             (gen132 k) (card132 (m - k)));
    [reflexivity | intros x _; unfold card132; apply len_map_gen].
Qed.

(* card132 m = Cat(m), reduced to one recurrence.  binomZ_central is the central
   binomial ratio (n+1) C(2n+2,n+1) = 2(2n+1) C(2n,n), so a class obeying the
   same ratio agrees with the central binomials from card132 0 = 1, and
   (m+1) card132 m = C(2m,m) follows by induction with no division. *)

Lemma binomN_central : forall n,
  (S n * binomN (2 * n + 2) (S n) = 2 * (2 * n + 1) * binomN (2 * n) n)%nat.
Proof.
  intro n. apply Nat2Z.inj.
  rewrite !Nat2Z.inj_mul, !binomN_binomZ.
  change (Z.of_nat 2) with 2%Z.
  exact (binomZ_central n).
Qed.

Definition CARD132_RATIO : Prop :=
  forall m, (S (S m) * card132 (S m) = 2 * (2 * m + 1) * card132 m)%nat.

Theorem card132_binom_of_ratio : CARD132_RATIO ->
  forall m, (S m * card132 m)%nat = binomN (2 * m) m.
Proof.
  intros HR m. induction m as [|m IH]; [reflexivity|].
  assert (Hc := binomN_central m).
  assert (Hr := HR m).
  assert (Hkey : (S m * (S (S m) * card132 (S m))
                  = S m * binomN (2 * m + 2) (S m))%nat).
  { rewrite Hr, Hc, <- IH. lia. }
  replace (2 * S m)%nat with (2 * m + 2)%nat by lia.
  apply (Nat.mul_cancel_l _ _ (S m)); [lia | exact Hkey].
Qed.

(* and back again, so the ratio and the closed count are the same problem and
   either may be attacked *)
Theorem card132_ratio_of_binom :
  (forall m, (S m * card132 m)%nat = binomN (2 * m) m) -> CARD132_RATIO.
Proof.
  intros H m.
  assert (Hc := binomN_central m).
  assert (Hkey : (S m * (S (S m) * card132 (S m))
                  = S m * (2 * (2 * m + 1) * card132 m))%nat).
  { assert (E := H (S m)). replace (2 * S m)%nat with (2 * m + 2)%nat in E by lia.
    assert (F := H m). nia. }
  apply (Nat.mul_cancel_l _ _ (S m)); [lia | exact Hkey].
Qed.

(* Unconditionally, at every size the enumeration reaches. *)
Theorem card132_ratio_upto_6 : forall m, (m <= 6)%nat ->
  (S (S m) * card132 (S m) = 2 * (2 * m + 1) * card132 m)%nat.
Proof.
  intros m Hm. destruct m as [|[|[|[|[|[|[|m]]]]]]]; try lia;
    vm_compute; reflexivity.
Qed.

Theorem card132_binom_upto_7 : forall m, (m <= 7)%nat ->
  (S m * card132 m)%nat = binomN (2 * m) m.
Proof.
  intros m Hm. destruct m as [|[|[|[|[|[|[|[|m]]]]]]]]; try lia;
    vm_compute; reflexivity.
Qed.

(* The d-subsets of [0,n), as strictly increasing lists. *)

Fixpoint choose (n d : nat) : list (list nat) :=
  match n with
  | 0%nat => match d with 0%nat => [[]] | S _ => [] end
  | S n' => match d with
            | 0%nat => [[]]
            | S d' => choose n' (S d') ++ map (fun l => l ++ [n']) (choose n' d')
            end
  end.

Theorem choose_length : forall n d, length (choose n d) = binomN n d.
Proof.
  induction n as [|n IH]; intro d; simpl.
  - destruct d; reflexivity.
  - destruct d as [|d]; [reflexivity|].
    rewrite len_app_gen, len_map_gen, (IH (S d)), (IH d). lia.
Qed.

Lemma choose_len : forall n d l, In l (choose n d) -> length l = d.
Proof.
  induction n as [|n IH]; intros d l Hl; simpl in Hl.
  - destruct d; [destruct Hl as [<- | []]; reflexivity | destruct Hl].
  - destruct d as [|d]; [destruct Hl as [<- | []]; reflexivity |].
    apply in_app_or in Hl. destruct Hl as [Hl | Hl].
    + apply (IH (S d)); exact Hl.
    + apply in_map_iff in Hl. destruct Hl as [s [Hs Hin]]. subst l.
      rewrite len_app. simpl. rewrite (IH d s Hin). lia.
Qed.

Lemma choose_bound : forall n d l x, In l (choose n d) -> In x l -> (x < n)%nat.
Proof.
  induction n as [|n IH]; intros d l x Hl Hx; simpl in Hl.
  - destruct d; [destruct Hl as [<- | []]; destruct Hx | destruct Hl].
  - destruct d as [|d]; [destruct Hl as [<- | []]; destruct Hx |].
    apply in_app_or in Hl. destruct Hl as [Hl | Hl].
    + assert (K := IH (S d) l x Hl Hx). lia.
    + apply in_map_iff in Hl. destruct Hl as [s [Hs Hin]]. subst l.
      apply in_app_or in Hx. destruct Hx as [Hx | Hx].
      * assert (K := IH d s x Hin Hx). lia.
      * simpl in Hx. destruct Hx as [<- | []]. lia.
Qed.

(* A chosen list is a set presented in increasing order. *)
Lemma choose_incr : forall n d l, In l (choose n d) -> incr l.
Proof.
  induction n as [|n IH]; intros d l Hl; simpl in Hl.
  - destruct d; [destruct Hl as [<- | []] | destruct Hl].
    intros a b Hab Hb. simpl in Hb. lia.
  - destruct d as [|d].
    + destruct Hl as [<- | []]. intros a b Hab Hb. simpl in Hb. lia.
    + apply in_app_or in Hl. destruct Hl as [Hl | Hl].
      * apply (IH (S d)); exact Hl.
      * apply in_map_iff in Hl. destruct Hl as [s [Hs Hin]]. subst l.
        assert (Hls : length s = d) by (apply (choose_len n d); exact Hin).
        assert (Hi := IH d s Hin).
        intros a b Hab Hb. rewrite len_app in Hb. simpl in Hb.
        destruct (Nat.lt_ge_cases b (length s)) as [Hbs | Hbs].
        -- rewrite !nth_app1 by lia. apply Hi; [exact Hab | exact Hbs].
        -- assert (Eb : b = length s) by lia. subst b.
           rewrite nth_app1 by lia. rewrite nth_last.
           apply (choose_bound n d s); [exact Hin | apply nth_In; lia].
Qed.

(* Pstat: skew cuts summed over all prefixes; d_A at the smallest outer cell is
   Pstat plus a constant. *)

Definition dominates_upto (w : list nat) (u v : nat) : Prop :=
  forall i j, (i < u)%nat -> (u <= j)%nat -> (j < v)%nat ->
    (nth j w 0%nat < nth i w 0%nat)%nat.

Lemma dominates_upto_dec : forall w u v,
  {dominates_upto w u v} + {~ dominates_upto w u v}.
Proof.
  intros w u v. unfold dominates_upto.
  destruct (bounded_ex_dec
    (fun i => exists j, (i < u)%nat /\ (u <= j)%nat /\ (j < v)%nat /\
                ~ (nth j w 0%nat < nth i w 0%nat)%nat) u) as [Hex | Hno].
  { intro i.
    destruct (bounded_ex_dec
      (fun j => (i < u)%nat /\ (u <= j)%nat /\ (j < v)%nat /\
                ~ (nth j w 0%nat < nth i w 0%nat)%nat) v) as [K | K].
    - intro j.
      destruct (lt_dec i u) as [A|A]; [|right; tauto].
      destruct (le_dec u j) as [B|B]; [|right; tauto].
      destruct (lt_dec j v) as [C|C]; [|right; tauto].
      destruct (lt_dec (nth j w 0%nat) (nth i w 0%nat)) as [D|D];
        [right; tauto | left; repeat split; assumption].
    - left. destruct K as [j [_ Hj]]. exists j. exact Hj.
    - right. intros [j Hj]. apply K. exists j. split; [lia | exact Hj]. }
  - right. intro H. destruct Hex as [i [_ [j [Hi [Hu [Hv Hn]]]]]].
    exact (Hn (H i j Hi Hu Hv)).
  - left. intros i j Hi Hu Hv.
    destruct (lt_dec (nth j w 0%nat) (nth i w 0%nat)) as [D|D]; [exact D|].
    exfalso. apply Hno. exists i. split; [exact Hi|].
    exists j. repeat split; assumption.
Defined.

Definition domb (w : list nat) (u v : nat) : nat :=
  if dominates_upto_dec w u v then 1%nat else 0%nat.

Definition Pstat (w : list nat) : nat :=
  sumn (S (length w)) (fun v => sumn (S v) (fun u => domb w u v)).

(* The cut condition sees only the prefix. *)
Lemma nth_firstn_lt : forall (l : list nat) v j d, (j < v)%nat ->
  nth j (firstn v l) d = nth j l d.
Proof.
  induction l as [|a l IH]; intros v j d Hj.
  - rewrite firstn_nil. destruct j; reflexivity.
  - destruct v as [|v]; [lia|]. simpl.
    destruct j as [|j]; [reflexivity|]. apply IH. lia.
Qed.

Lemma dominates_upto_firstn : forall w u v, (v <= length w)%nat ->
  (dominates_upto w u v <-> dominates_upto (firstn v w) u v).
Proof.
  intros w u v Hv. unfold dominates_upto. split; intros H i j Hi Hu Hj.
  - rewrite !(nth_firstn_lt w v _ 0%nat) by lia. apply H; assumption.
  - assert (K := H i j Hi Hu Hj).
    rewrite !(nth_firstn_lt w v _ 0%nat) in K by lia. exact K.
Qed.

Fixpoint idx (x : nat) (l : list nat) : nat :=
  match l with
  | nil => 0%nat
  | y :: r => if Nat.eqb y x then 0%nat else S (idx x r)
  end.

Definition pinv (u : list nat) : list nat :=
  map (fun t => idx t u) (seq 0 (length u)).

(* pinv is the inverse permutation, idx its coordinate. *)

Lemma idx_lt : forall l x, In x l -> (idx x l < length l)%nat.
Proof.
  induction l as [|y r IH]; intros x Hx; [contradiction|].
  cbn [idx length]. destruct (Nat.eqb_spec y x) as [E|E]; [lia|].
  assert (Hr : In x r)
    by (destruct Hx as [Hc|Hc]; [exfalso; apply E; exact Hc | exact Hc]).
  assert (K := IH x Hr). lia.
Qed.

Lemma idx_nth : forall l x, In x l -> nth (idx x l) l 0%nat = x.
Proof.
  induction l as [|y r IH]; intros x Hx; [contradiction|].
  cbn [idx]. destruct (Nat.eqb_spec y x) as [E|E]; [exact E|].
  assert (Hr : In x r)
    by (destruct Hx as [Hc|Hc]; [exfalso; apply E; exact Hc | exact Hc]).
  cbn [nth]. apply IH. exact Hr.
Qed.

Lemma nth_idx : forall l, NoDup l ->
  forall i, (i < length l)%nat -> idx (nth i l 0%nat) l = i.
Proof.
  induction l as [|y r IH]; intros Hnd i Hi; cbn [length] in Hi; [lia|].
  inversion Hnd as [|z zs Hny Hndr Heq]; subst.
  destruct i as [|i].
  - cbn [nth idx]. rewrite Nat.eqb_refl. reflexivity.
  - cbn [nth idx].
    assert (Hin : In (nth i r 0%nat) r) by (apply nth_In; cbn in Hi; lia).
    destruct (Nat.eqb_spec y (nth i r 0%nat)) as [E|E].
    + exfalso. apply Hny. rewrite E. exact Hin.
    + rewrite (IH Hndr i ltac:(cbn in Hi; lia)). reflexivity.
Qed.

Lemma pinv_length : forall u, length (pinv u) = length u.
Proof.
  intro u. unfold pinv. rewrite len_map_gen, length_seq. reflexivity.
Qed.

Lemma pinv_nth : forall u x, (x < length u)%nat ->
  nth x (pinv u) 0%nat = idx x u.
Proof.
  intros u x Hx. unfold pinv.
  rewrite (map_nth_def (fun t => idx t u) (seq 0 (length u)) x)
    by (rewrite length_seq; exact Hx).
  rewrite seq_nth by exact Hx. reflexivity.
Qed.

(* the two round trips *)
Lemma pinv_nth_nth : forall u m, is_perm u m ->
  forall i, (i < m)%nat -> nth (nth i u 0%nat) (pinv u) 0%nat = i.
Proof.
  intros u m Hp i Hi. destruct Hp as [Hlen [Hnd Hb]].
  assert (Hin : In (nth i u 0%nat) u) by (apply nth_In; lia).
  assert (Hlt : (nth i u 0%nat < length u)%nat)
    by (rewrite Hlen; apply Hb; exact Hin).
  rewrite pinv_nth by exact Hlt.
  apply nth_idx; [exact Hnd | lia].
Qed.

Lemma nth_pinv_nth : forall u m, is_perm u m ->
  forall x, (x < m)%nat -> nth (nth x (pinv u) 0%nat) u 0%nat = x.
Proof.
  intros u m Hp x Hx. destruct Hp as [Hlen [Hnd Hb]].
  assert (Hin : In x u) by (apply (perm_full u m); [split; [exact Hlen | split; assumption] | exact Hx]).
  rewrite pinv_nth by lia. apply idx_nth. exact Hin.
Qed.

Theorem pinv_perm : forall u m, is_perm u m -> is_perm (pinv u) m.
Proof.
  intros u m Hp. assert (Hp' := Hp). destruct Hp as [Hlen [Hnd Hb]].
  split; [rewrite pinv_length; exact Hlen | split].
  - apply NoDup_nth with (d := 0%nat).
    intros i j Hi Hj He. rewrite pinv_length, Hlen in Hi, Hj.
    assert (Ei : nth (nth i (pinv u) 0%nat) u 0%nat = i)
      by (apply (nth_pinv_nth u m Hp'); exact Hi).
    assert (Ej : nth (nth j (pinv u) 0%nat) u 0%nat = j)
      by (apply (nth_pinv_nth u m Hp'); exact Hj).
    rewrite <- Ei, <- Ej, He. reflexivity.
  - intros x Hx. apply In_nth with (d := 0%nat) in Hx.
    destruct Hx as [t [Ht Hnth]]. rewrite pinv_length, Hlen in Ht.
    rewrite pinv_nth in Hnth by lia. rewrite <- Hnth.
    assert (Hin : In t u)
      by (apply (perm_full u m); [exact Hp' | exact Ht]).
    rewrite <- Hlen. apply idx_lt. exact Hin.
Qed.

Theorem pinv_involutive : forall u m, is_perm u m -> pinv (pinv u) = u.
Proof.
  intros u m Hp.
  assert (Hpi : is_perm (pinv u) m) by (apply (pinv_perm u m); exact Hp).
  assert (Hpii : is_perm (pinv (pinv u)) m)
    by (apply (pinv_perm (pinv u) m); exact Hpi).
  apply (nth_ext (pinv (pinv u)) u 0%nat 0%nat).
  - rewrite !pinv_length. reflexivity.
  - intros t Ht. rewrite !pinv_length in Ht.
    assert (Htm : (t < m)%nat) by (destruct Hp as [Hl _]; lia).
    assert (E : nth (nth t (pinv (pinv u)) 0%nat) (pinv u) 0%nat = t)
      by (apply (nth_pinv_nth (pinv u) m Hpi); exact Htm).
    assert (F : nth (nth t u 0%nat) (pinv u) 0%nat = t)
      by (apply (pinv_nth_nth u m Hp); exact Htm).
    assert (Ha : (nth t (pinv (pinv u)) 0%nat < m)%nat).
    { destruct Hpii as [Hl3 [_ Hb3]]. apply Hb3. apply nth_In. lia. }
    assert (Hbb : (nth t u 0%nat < m)%nat).
    { destruct Hp as [Hl [_ Hb]]. apply Hb. apply nth_In. lia. }
    assert (G := nth_pinv_nth u m Hp).
    assert (Heq : nth (nth t (pinv (pinv u)) 0%nat) (pinv u) 0%nat
                = nth (nth t u 0%nat) (pinv u) 0%nat)
      by (rewrite E, F; reflexivity).
    assert (Ka := G _ Ha). assert (Kb := G _ Hbb).
    rewrite Heq in Ka. rewrite Kb in Ka. symmetry. exact Ka.
Qed.

(* Av(132) is inverse closed, since 132 is its own inverse. *)
Theorem pinv_132 : forall u m, is_perm u m ->
  contains_132 u -> contains_132 (pinv u).
Proof.
  intros u m Hp [i [j [k H]]]. unfold has_132_at in H.
  destruct H as [Hij [Hjk [Hk [Hik Hkj]]]].
  assert (Hlen : length u = m) by av.
  assert (Hbnd : forall t, (t < m)%nat -> (nth t u 0%nat < m)%nat).
  { intros t Ht. destruct Hp as [_ [_ Hb]]. apply Hb. apply nth_In. lia. }
  exists (nth i u 0%nat), (nth k u 0%nat), (nth j u 0%nat).
  unfold has_132_at.
  rewrite (pinv_nth_nth u m Hp i ltac:(lia)).
  rewrite (pinv_nth_nth u m Hp j ltac:(lia)).
  rewrite (pinv_nth_nth u m Hp k ltac:(lia)).
  rewrite pinv_length.
  assert (Hj := Hbnd j ltac:(lia)).
  repeat split; lia.
Qed.

Corollary pinv_avoids_132 : forall u m, is_perm u m ->
  (~ contains_132 u <-> ~ contains_132 (pinv u)).
Proof.
  intros u m Hp. split; intros H C.
  - apply H. rewrite <- (pinv_involutive u m Hp).
    apply (pinv_132 (pinv u) m); [apply (pinv_perm u m); exact Hp | exact C].
  - apply H. apply (pinv_132 u m Hp). exact C.
Qed.

(* Av(1324) is inverse closed too, by the same transport: an occurrence at
   positions i < j < k < l with values v_i < v_k < v_j < v_l becomes one in the
   inverse at positions v_i < v_k < v_j < v_l carrying the values i, k, j, l,
   and reading the pattern off those gives i < j < k < l again. *)
Theorem pinv_1324 : forall u m, is_perm u m ->
  contains_1324 u -> contains_1324 (pinv u).
Proof.
  intros u m Hp [i [j [k [l H]]]]. unfold has_1324_at in H.
  destruct H as [Hij [Hjk [Hkl [Hl [Hik [Hkj Hjl]]]]]].
  assert (Hlen : length u = m) by av.
  assert (Hbnd : forall t, (t < m)%nat -> (nth t u 0%nat < m)%nat).
  { intros t Ht. destruct Hp as [_ [_ Hb]]. apply Hb. apply nth_In. lia. }
  exists (nth i u 0%nat), (nth k u 0%nat), (nth j u 0%nat), (nth l u 0%nat).
  unfold has_1324_at.
  rewrite (pinv_nth_nth u m Hp i ltac:(lia)).
  rewrite (pinv_nth_nth u m Hp j ltac:(lia)).
  rewrite (pinv_nth_nth u m Hp k ltac:(lia)).
  rewrite (pinv_nth_nth u m Hp l ltac:(lia)).
  rewrite pinv_length.
  assert (Hb := Hbnd l ltac:(lia)).
  repeat split; lia.
Qed.

Corollary pinv_avoids_1324 : forall u m, is_perm u m ->
  (~ contains_1324 u <-> ~ contains_1324 (pinv u)).
Proof.
  intros u m Hp. split; intros H C.
  - apply H. rewrite <- (pinv_involutive u m Hp).
    apply (pinv_1324 (pinv u) m); [apply (pinv_perm u m); exact Hp | exact C].
  - apply H. apply (pinv_1324 u m Hp). exact C.
Qed.

Lemma pinv_inj : forall u v m, is_perm u m -> is_perm v m ->
  pinv u = pinv v -> u = v.
Proof.
  intros u v m Hu Hv He.
  rewrite <- (pinv_involutive u m Hu), <- (pinv_involutive v m Hv), He.
  reflexivity.
Qed.

(* Hence Permutation (map pinv (gen132 m)) (gen132 m), the hypothesis every
   covariance identity above takes. *)
Theorem pinv_gen132 : forall m, Permutation (map pinv (gen132 m)) (gen132 m).
Proof.
  intro m.
  assert (Hin : forall u, In u (gen132 m) -> In (pinv u) (gen132 m)).
  { intros u Hu. apply gen132_spec in Hu. destruct Hu as [Hp Hav].
    apply gen132_spec. split.
    - apply (pinv_perm u m); exact Hp.
    - apply (pinv_avoids_132 u m Hp); exact Hav. }
  apply NoDup_Permutation.
  - apply NoDup_map_inj; [apply gen132_nodup|].
    intros x y Hx Hy He.
    apply gen132_spec in Hx. apply gen132_spec in Hy.
    exact (pinv_inj x y m (proj1 Hx) (proj1 Hy) He).
  - apply gen132_nodup.
  - intro w. split.
    + intro Hw. apply in_map_iff in Hw. destruct Hw as [u [Hu Huin]].
      subst w. apply Hin. exact Huin.
    + intro Hw. apply in_map_iff. exists (pinv w). split.
      * assert (Hp : is_perm w m) by av.
        apply (pinv_involutive w m Hp).
      * apply Hin. exact Hw.
Qed.

(* The inversion count is inverse invariant, by the bijection (i,j) |-> (u_j, u_i). *)

Definition allpairs (n : nat) : list (nat * nat) :=
  flat_map (fun i => map (fun j => (i, j)) (seq (S i) (n - S i))) (seq 0 n).

Lemma allpairs_spec : forall n p,
  In p (allpairs n) <-> ((fst p < snd p)%nat /\ (snd p < n)%nat).
Proof.
  intros n p. unfold allpairs. split.
  - intro H. apply in_flat_map in H. destruct H as [i [Hi H]].
    apply in_seq in Hi. apply in_map_iff in H. destruct H as [j [Hj Hjin]].
    apply in_seq in Hjin. subst p. cbn [fst snd]. lia.
  - intros [H1 H2]. apply in_flat_map. exists (fst p). split.
    + apply in_seq. lia.
    + apply in_map_iff. exists (snd p). split.
      * destruct p; reflexivity.
      * apply in_seq. lia.
Qed.

Lemma allpairs_nodup : forall n, NoDup (allpairs n).
Proof.
  intro n. unfold allpairs.
  apply NoDup_flat_map_inj; [apply seq_NoDup| |].
  - intros i _. apply NoDup_map_inj; [apply seq_NoDup|].
    intros a b _ _ He. congruence.
  - intros x y w Hx Hy Hwx Hwy.
    apply in_map_iff in Hwx. destruct Hwx as [a [Ha _]].
    apply in_map_iff in Hwy. destruct Hwy as [b [Hb _]].
    congruence.
Qed.

Definition invb (u : list nat) (p : nat * nat) : bool :=
  Nat.ltb (nth (snd p) u 0%nat) (nth (fst p) u 0%nat).

Definition invpairs (u : list nat) : list (nat * nat) :=
  filter (invb u) (allpairs (length u)).

Definition invcount (u : list nat) : nat := length (invpairs u).

Definition swapnth (u : list nat) (p : nat * nat) : nat * nat :=
  (nth (snd p) u 0%nat, nth (fst p) u 0%nat).

Lemma invpairs_bounds : forall u p, In p (invpairs u) ->
  (fst p < snd p)%nat /\ (snd p < length u)%nat.
Proof.
  intros u p Hp. unfold invpairs in Hp. apply filter_In in Hp.
  destruct Hp as [Hall _]. apply allpairs_spec in Hall. exact Hall.
Qed.

Lemma invpairs_transport : forall u m, is_perm u m ->
  forall p, In p (invpairs u) -> In (swapnth u p) (invpairs (pinv u)).
Proof.
  intros u m Hp p Hin.
  assert (Hlen : length u = m) by av.
  assert (Hbd := invpairs_bounds u p Hin).
  unfold invpairs in Hin. apply filter_In in Hin. destruct Hin as [_ Hb].
  unfold invb in Hb. apply Nat.ltb_lt in Hb.
  assert (Hi : (fst p < m)%nat) by lia.
  assert (Hj : (snd p < m)%nat) by lia.
  assert (Bi : (nth (fst p) u 0%nat < m)%nat).
  { destruct Hp as [_ [_ Hbb]]. apply Hbb. apply nth_In. lia. }
  unfold invpairs. apply filter_In. split.
  - apply allpairs_spec. rewrite pinv_length, Hlen.
    unfold swapnth. cbn [fst snd]. split; [exact Hb | exact Bi].
  - unfold invb, swapnth. cbn [fst snd]. apply Nat.ltb_lt.
    rewrite (pinv_nth_nth u m Hp (fst p) Hi).
    rewrite (pinv_nth_nth u m Hp (snd p) Hj).
    exact (proj1 Hbd).
Qed.

Lemma swapnth_inj : forall u m, is_perm u m ->
  forall p q, In p (invpairs u) -> In q (invpairs u) ->
  swapnth u p = swapnth u q -> p = q.
Proof.
  intros u m Hp p q Hip Hiq He.
  assert (Hlen : length u = m) by av.
  assert (Hp' := invpairs_bounds u p Hip).
  assert (Hq' := invpairs_bounds u q Hiq).
  assert (Hpf : (fst p < m)%nat) by lia.
  assert (Hps : (snd p < m)%nat) by lia.
  assert (Hqf : (fst q < m)%nat) by lia.
  assert (Hqs : (snd q < m)%nat) by lia.
  unfold swapnth in He. injection He as H1 H2.
  assert (E1 : snd p = snd q).
  { rewrite <- (pinv_nth_nth u m Hp (snd p) Hps), H1.
    apply (pinv_nth_nth u m Hp (snd q) Hqs). }
  assert (E2 : fst p = fst q).
  { rewrite <- (pinv_nth_nth u m Hp (fst p) Hpf), H2.
    apply (pinv_nth_nth u m Hp (fst q) Hqf). }
  destruct p as [a b]; destruct q as [c d]; cbn [fst snd] in E1, E2.
  rewrite E1, E2. reflexivity.
Qed.

Lemma invcount_le : forall u m, is_perm u m ->
  (invcount u <= invcount (pinv u))%nat.
Proof.
  intros u m Hp. unfold invcount.
  rewrite <- (len_map_gen _ _ (swapnth u) (invpairs u)).
  apply NoDup_incl_length.
  - apply NoDup_map_inj.
    + unfold invpairs. apply NoDup_filter. apply allpairs_nodup.
    + intros x y Hx Hy He. exact (swapnth_inj u m Hp x y Hx Hy He).
  - intros w Hw. apply in_map_iff in Hw. destruct Hw as [p [Hpw Hpin]].
    subst w. exact (invpairs_transport u m Hp p Hpin).
Qed.

Theorem invcount_pinv : forall u m, is_perm u m ->
  invcount (pinv u) = invcount u.
Proof.
  intros u m Hp.
  assert (Hpi : is_perm (pinv u) m) by (apply (pinv_perm u m); exact Hp).
  assert (H1 : (invcount u <= invcount (pinv u))%nat)
    by (apply (invcount_le u m); exact Hp).
  assert (H2 : (invcount (pinv u) <= invcount (pinv (pinv u)))%nat)
    by (apply (invcount_le (pinv u) m); exact Hpi).
  rewrite (pinv_involutive u m Hp) in H2. lia.
Qed.

Definition pqd_pairs (m : nat) : list (nat * nat) :=
  map (fun b => (Pstat b, Pstat (pinv b))) (gen132 m).

(* The open conjecture, stated where pqd_square consumes it. *)
Definition PQD_statement : Prop :=
  forall m a b,
    (cntA a (pqd_pairs m) * cntB b (pqd_pairs m)
     <= length (pqd_pairs m) * cnt2 a b (pqd_pairs m))%nat.

(* The two coordinate totals of pqd_pairs agree, since inversion permutes gen132. *)

Lemma nfold_perm : forall (A : Type) (g : A -> nat) (l1 l2 : list A),
  Permutation l1 l2 ->
  fold_right (fun x acc => (g x + acc)%nat) 0%nat l1
  = fold_right (fun x acc => (g x + acc)%nat) 0%nat l2.
Proof.
  intros A g l1 l2 H.
  induction H as [|x l l' H IH|x y l|l1 l2 l3 H1 IH1 H2 IH2];
    cbn [fold_right];
    [reflexivity | rewrite IH; reflexivity | lia | rewrite IH1; exact IH2].
Qed.

Lemma nfold_map : forall (A : Type) (g : A -> nat) (s : A -> A) (l : list A),
  fold_right (fun x acc => (g x + acc)%nat) 0%nat (map s l)
  = fold_right (fun x acc => (g (s x) + acc)%nat) 0%nat l.
Proof.
  intros A g s. induction l as [|a l IH]; cbn [map fold_right];
    [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma sumA_map : forall (A : Type) (f : A -> nat * nat) (l : list A),
  sumA (map f l) = fold_right (fun x acc => (fst (f x) + acc)%nat) 0%nat l.
Proof.
  intros A f. induction l as [|a l IH]; cbn [map sumA fold_right];
    [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma sumB_map : forall (A : Type) (f : A -> nat * nat) (l : list A),
  sumB (map f l) = fold_right (fun x acc => (snd (f x) + acc)%nat) 0%nat l.
Proof.
  intros A f. induction l as [|a l IH]; cbn [map sumB fold_right];
    [reflexivity | rewrite IH; reflexivity].
Qed.

Theorem pqd_totals_agree : forall m, sumB (pqd_pairs m) = sumA (pqd_pairs m).
Proof.
  intro m. unfold pqd_pairs.
  rewrite sumA_map, sumB_map. cbn [fst snd].
  rewrite <- (nfold_map (list nat) Pstat pinv (gen132 m)).
  apply nfold_perm. apply pinv_gen132.
Qed.

Theorem pqd_gives_chebyshev : PQD_statement ->
  forall m M,
    (forall p, In p (pqd_pairs m) -> (fst p <= M)%nat /\ (snd p <= M)%nat) ->
    sumB (pqd_pairs m) = sumA (pqd_pairs m) ->
    (sumA (pqd_pairs m) * sumA (pqd_pairs m)
     <= length (pqd_pairs m) * sumAB (pqd_pairs m))%nat.
Proof.
  intros HP m M Hb Heq.
  apply (pqd_square M (pqd_pairs m) Hb (fun a b => HP m a b) Heq).
Qed.

(* With the totals discharged, PQD alone gives the Chebyshev step. *)
Corollary pqd_suffices : PQD_statement ->
  forall m M,
    (forall p, In p (pqd_pairs m) -> (fst p <= M)%nat /\ (snd p <= M)%nat) ->
    (sumA (pqd_pairs m) * sumA (pqd_pairs m)
     <= length (pqd_pairs m) * sumAB (pqd_pairs m))%nat.
Proof.
  intros HP m M Hb.
  apply (pqd_gives_chebyshev HP m M Hb). apply pqd_totals_agree.
Qed.

(* The statistic as an integer, so the covariance identities apply to it. *)
Definition Pz (b : list nat) : Z := Z.of_nat (Pstat b).

(* The inversion strata of Av(132)_m, where the abstract split lands. *)

Definition invfibre (m k : nat) : list (list nat) :=
  filter (fun b => if Nat.eq_dec (invcount b) k then true else false)
         (gen132 m).

Definition invkeys (m : nat) : list nat :=
  nodup Nat.eq_dec (map invcount (gen132 m)).

(* Strata over an arbitrary Z-valued statistic; only the fibre sizes enter posw. *)
Definition stratum_of (F : list nat -> Z) (m k : nat) : stratum :=
  mkStratum (length (invfibre m k))
            (csum (map F (invfibre m k)))
            (csum (map (fun b => (F b * F (pinv b))%Z) (invfibre m k))).

Definition strata_of (F : list nat -> Z) (m : nat) : list stratum :=
  map (stratum_of F m) (invkeys m).

Lemma in_length_pos : forall (A : Type) (x : A) (l : list A),
  In x l -> (1 <= length l)%nat.
Proof.
  intros A x l H. destruct l as [|a l]; [contradiction | cbn [length]; lia].
Qed.

Lemma invkeys_witness : forall m k, In k (invkeys m) ->
  exists b, In b (gen132 m) /\ invcount b = k.
Proof.
  intros m k H. unfold invkeys in H. apply nodup_In in H.
  apply in_map_iff in H. destruct H as [b [Hb Hin]].
  exists b. split; [exact Hin | exact Hb].
Qed.

(* Every stratum is non-empty, because its key came from an element. *)
Theorem strata_posw : forall F m, posw (proj_ns (strata_of F m)).
Proof.
  intros F m p Hp. unfold proj_ns, strata_of in Hp.
  rewrite map_map in Hp. apply in_map_iff in Hp.
  destruct Hp as [k [Hk Hkin]]. subst p. cbn [fst].
  destruct (invkeys_witness m k Hkin) as [b [Hb He]].
  apply (in_length_pos (list nat) b).
  unfold invfibre. apply filter_In. split; [exact Hb|].
  destruct (Nat.eq_dec (invcount b) k); [reflexivity | contradiction].
Qed.

(* so the split applies to any statistic on Av(132)_m, with no hypothesis left *)
Corollary strata_cov_ge_within : forall F m,
  (nsumz (proj_ns (strata_of F m)) * defw (strata_of F m)
   <= nprodz (proj_ns (strata_of F m))
        * (nsumz (proj_ns (strata_of F m)) * stP (strata_of F m)
           - ssumz (proj_ns (strata_of F m))
             * ssumz (proj_ns (strata_of F m))))%Z.
Proof. intros F m. apply cov_ge_within. apply strata_posw. Qed.

Corollary strata_between_nonneg : forall F m,
  (0 <= nsumz (proj_ns (strata_of F m)) * qsumz (proj_ns (strata_of F m))
        - nprodz (proj_ns (strata_of F m))
          * ssumz (proj_ns (strata_of F m)) * ssumz (proj_ns (strata_of F m)))%Z.
Proof. intros F m. apply between_nonneg. apply strata_posw. Qed.

(* and the stratum sums really are the global ones *)
Lemma ssumz_map_strata : forall (K : Type) (F : K -> stratum) (keys : list K),
  ssumz (proj_ns (map F keys)) = foldZ (fun k => st_S (F k)) keys.
Proof.
  intros K F. induction keys as [|a keys IH]; [reflexivity|].
  cbn [map]. rewrite proj_ns_cons, ssumz_cons, foldZ_cons, IH.
  cbn [snd]. reflexivity.
Qed.

Lemma stP_map_strata : forall (K : Type) (F : K -> stratum) (keys : list K),
  stP (map F keys) = foldZ (fun k => st_P (F k)) keys.
Proof.
  intros K F. induction keys as [|a keys IH]; [reflexivity|].
  cbn [map stP]. rewrite foldZ_cons, IH. reflexivity.
Qed.

Theorem strata_S_total : forall F m,
  ssumz (proj_ns (strata_of F m)) = csum (map F (gen132 m)).
Proof.
  intros F m. unfold strata_of. rewrite ssumz_map_strata. symmetry.
  apply (csum_fibres (list nat) nat Nat.eq_dec invcount (invkeys m)
                     (gen132 m) F).
  - unfold invkeys. apply NoDup_nodup.
  - intros b Hb. unfold invkeys. apply nodup_In. apply in_map. exact Hb.
Qed.

Theorem strata_P_total : forall F m,
  stP (strata_of F m)
  = csum (map (fun b => (F b * F (pinv b))%Z) (gen132 m)).
Proof.
  intros F m. unfold strata_of. rewrite stP_map_strata. symmetry.
  apply (csum_fibres (list nat) nat Nat.eq_dec invcount (invkeys m)
                     (gen132 m) (fun b => (F b * F (pinv b))%Z)).
  - unfold invkeys. apply NoDup_nodup.
  - intros b Hb. unfold invkeys. apply nodup_In. apply in_map. exact Hb.
Qed.

(* The sV instantiation, which is the corner a = c = 2. *)
Corollary sV_cov_ge_within : forall m,
  (nsumz (proj_ns (strata_of Pz m)) * defw (strata_of Pz m)
   <= nprodz (proj_ns (strata_of Pz m))
        * (nsumz (proj_ns (strata_of Pz m)) * stP (strata_of Pz m)
           - ssumz (proj_ns (strata_of Pz m))
             * ssumz (proj_ns (strata_of Pz m))))%Z.
Proof. intro m. apply strata_cov_ge_within. Qed.

Corollary sV_between_nonneg : forall m,
  (0 <= nsumz (proj_ns (strata_of Pz m)) * qsumz (proj_ns (strata_of Pz m))
        - nprodz (proj_ns (strata_of Pz m))
          * ssumz (proj_ns (strata_of Pz m))
          * ssumz (proj_ns (strata_of Pz m)))%Z.
Proof. intro m. apply strata_between_nonneg. Qed.

(* The conjecture in pair form, on Av(132)_m. *)
Theorem sV_cov_pair_form : forall m,
  (2 * (Z.of_nat (length (gen132 m))
        * csum (map (fun b => (Pz b * Pz (pinv b))%Z) (gen132 m))
        - csum (map Pz (gen132 m)) * csum (map Pz (gen132 m)))
   = csum2 (gen132 m)
       (fun b b' => ((Pz b - Pz b') * (Pz (pinv b) - Pz (pinv b')))%Z))%Z.
Proof.
  intro m. apply (cov_pair_form (list nat) (gen132 m) Pz pinv).
  apply pinv_gen132.
Qed.

(* A vertical domino: a 1324-avoider of [0,a+b) with entries below b avoiding 132
   and entries at or above b avoiding 213.  The tests are existsb loops so they reduce. *)

Definition idxs (p : list nat) (s : nat) : list nat := seq s (length p - s).

Lemma in_idxs : forall p s t,
  In t (idxs p s) <-> ((s <= t)%nat /\ (t < length p)%nat).
Proof. intros p s t. unfold idxs. rewrite in_seq. lia. Qed.

Definition contains132b (p : list nat) : bool :=
  existsb (fun i => existsb (fun j => existsb (fun k =>
      andb (Nat.ltb (nth i p 0%nat) (nth k p 0%nat))
           (Nat.ltb (nth k p 0%nat) (nth j p 0%nat)))
      (idxs p (S j))) (idxs p (S i))) (idxs p 0).

Lemma contains132b_spec : forall p, contains132b p = true <-> contains_132 p.
Proof.
  intro p. unfold contains132b. split.
  - intro H.
    apply existsb_exists in H. destruct H as [i [Hi H]].
    apply existsb_exists in H. destruct H as [j [Hj H]].
    apply existsb_exists in H. destruct H as [k [Hk H]].
    apply in_idxs in Hi. apply in_idxs in Hj. apply in_idxs in Hk.
    apply andb_true_iff in H. destruct H as [H1 H2].
    apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2.
    exists i, j, k. unfold has_132_at. cbv zeta. repeat split; lia.
  - intros [i [j [k H]]]. unfold has_132_at in H. cbv zeta in H.
    destruct H as [Hij [Hjk [Hk [H1 H2]]]].
    apply existsb_exists. exists i. split; [apply in_idxs; lia|].
    apply existsb_exists. exists j. split; [apply in_idxs; lia|].
    apply existsb_exists. exists k. split; [apply in_idxs; lia|].
    apply andb_true_iff. split; apply Nat.ltb_lt; assumption.
Qed.

(* The explicit loop and the sumbool decider agree. *)
Lemma avoids132b_alt : forall p, avoids132b p = negb (contains132b p).
Proof.
  intro p. unfold avoids132b.
  destruct (contains_132_dec p) as [H | H].
  - destruct (contains132b p) eqn:E; [reflexivity|].
    exfalso. apply contains132b_spec in H. rewrite H in E. discriminate.
  - destruct (contains132b p) eqn:E; [|reflexivity].
    exfalso. apply H. apply contains132b_spec. exact E.
Qed.

Definition contains213b (p : list nat) : bool :=
  existsb (fun i => existsb (fun j => existsb (fun k =>
      andb (Nat.ltb (nth j p 0%nat) (nth i p 0%nat))
           (Nat.ltb (nth i p 0%nat) (nth k p 0%nat)))
      (idxs p (S j))) (idxs p (S i))) (idxs p 0).

Lemma contains213b_spec : forall p, contains213b p = true <-> contains_213 p.
Proof.
  intro p. unfold contains213b. split.
  - intro H.
    apply existsb_exists in H. destruct H as [i [Hi H]].
    apply existsb_exists in H. destruct H as [j [Hj H]].
    apply existsb_exists in H. destruct H as [k [Hk H]].
    apply in_idxs in Hi. apply in_idxs in Hj. apply in_idxs in Hk.
    apply andb_true_iff in H. destruct H as [H1 H2].
    apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2.
    exists i, j, k. unfold has_213_at. cbv zeta. repeat split; lia.
  - intros [i [j [k H]]]. unfold has_213_at in H. cbv zeta in H.
    destruct H as [Hij [Hjk [Hk [H1 H2]]]].
    apply existsb_exists. exists i. split; [apply in_idxs; lia|].
    apply existsb_exists. exists j. split; [apply in_idxs; lia|].
    apply existsb_exists. exists k. split; [apply in_idxs; lia|].
    apply andb_true_iff. split; apply Nat.ltb_lt; assumption.
Qed.

Definition contains1324b (p : list nat) : bool :=
  existsb (fun i => existsb (fun j => existsb (fun k => existsb (fun l =>
      andb (andb (Nat.ltb (nth i p 0%nat) (nth k p 0%nat))
                 (Nat.ltb (nth k p 0%nat) (nth j p 0%nat)))
           (Nat.ltb (nth j p 0%nat) (nth l p 0%nat)))
      (idxs p (S k))) (idxs p (S j))) (idxs p (S i))) (idxs p 0).

Lemma contains1324b_spec : forall p, contains1324b p = true <-> contains_1324 p.
Proof.
  intro p. unfold contains1324b. split.
  - intro H.
    apply existsb_exists in H. destruct H as [i [Hi H]].
    apply existsb_exists in H. destruct H as [j [Hj H]].
    apply existsb_exists in H. destruct H as [k [Hk H]].
    apply existsb_exists in H. destruct H as [l [Hl H]].
    apply in_idxs in Hi. apply in_idxs in Hj.
    apply in_idxs in Hk. apply in_idxs in Hl.
    apply andb_true_iff in H. destruct H as [H12 H3].
    apply andb_true_iff in H12. destruct H12 as [H1 H2].
    apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2. apply Nat.ltb_lt in H3.
    exists i, j, k, l. unfold has_1324_at. cbv zeta. repeat split; lia.
  - intros [i [j [k [l H]]]]. unfold has_1324_at in H. cbv zeta in H.
    destruct H as [Hij [Hjk [Hkl [Hl [H1 [H2 H3]]]]]].
    apply existsb_exists. exists i. split; [apply in_idxs; lia|].
    apply existsb_exists. exists j. split; [apply in_idxs; lia|].
    apply existsb_exists. exists k. split; [apply in_idxs; lia|].
    apply existsb_exists. exists l. split; [apply in_idxs; lia|].
    apply andb_true_iff. split; [apply andb_true_iff; split|];
      apply Nat.ltb_lt; assumption.
Qed.

(* The two cells of a vertical domino, cut by value at b. *)
Definition locell (b : nat) (w : list nat) : list nat :=
  filter (fun x => Nat.ltb x b) w.

Definition hicell (b : nat) (w : list nat) : list nat :=
  filter (fun x => Nat.leb b x) w.

Definition dominob (b : nat) (w : list nat) : bool :=
  andb (negb (contains132b (locell b w))) (negb (contains213b (hicell b w))).

Definition dominoes (a b : nat) : list (list nat) :=
  filter (dominob b) (gen (a + b)).

Definition Dcount (a b : nat) : nat := length (dominoes a b).

(* d_A, as a cardinality: the dominoes sitting over one lower cell. *)
Definition dA (a b : nat) (l : list nat) : nat :=
  length (filter (fun w => if list_eq_dec Nat.eq_dec (locell b w) l
                           then true else false)
                 (dominoes a b)).

Theorem dominoes_spec : forall a b w,
  In w (dominoes a b) <->
  (is_perm w (a + b) /\ ~ contains_1324 w
   /\ ~ contains_132 (locell b w) /\ ~ contains_213 (hicell b w)).
Proof.
  intros a b w. unfold dominoes. rewrite filter_In. split.
  - intros [Hg Hd]. apply gen_spec in Hg. destruct Hg as [Hp Hav].
    unfold dominob in Hd. apply andb_true_iff in Hd. destruct Hd as [H1 H2].
    apply negb_true_iff in H1. apply negb_true_iff in H2.
    split; [exact Hp|]. split; [exact Hav|]. split.
    + intro C. apply contains132b_spec in C. rewrite C in H1. discriminate.
    + intro C. apply contains213b_spec in C. rewrite C in H2. discriminate.
  - intros [Hp [Hav [H1 H2]]]. split.
    + apply gen_spec. split; [exact Hp | exact Hav].
    + unfold dominob. apply andb_true_iff. split; apply negb_true_iff.
      * destruct (contains132b (locell b w)) eqn:E; [|reflexivity].
        exfalso. apply H1. apply contains132b_spec. exact E.
      * destruct (contains213b (hicell b w)) eqn:E; [|reflexivity].
        exfalso. apply H2. apply contains213b_spec. exact E.
Qed.

Theorem dominoes_nodup : forall a b, NoDup (dominoes a b).
Proof.
  intros a b. unfold dominoes. apply NoDup_filter. apply gen_nodup.
Qed.

#[export] Hint Resolve dominoes_nodup : av1324.

(* The lower cell of a domino avoids 132. *)
Lemma dominoes_locell_132 : forall a b w,
  In w (dominoes a b) -> ~ contains_132 (locell b w).
Proof.
  intros a b w H. apply dominoes_spec in H. tauto.
Qed.

(* The domino total is the sum of d_A over the lower cells that occur. *)
Theorem Dcount_fibres : forall a b,
  Dcount a b
  = fold_right (fun l acc => (dA a b l + acc)%nat) 0%nat
      (nodup (list_eq_dec Nat.eq_dec) (map (locell b) (dominoes a b))).
Proof.
  intros a b. unfold Dcount, dA.
  apply (length_fibres (list nat) (list nat) (list_eq_dec Nat.eq_dec)
                       (locell b)
                       (nodup (list_eq_dec Nat.eq_dec)
                              (map (locell b) (dominoes a b)))
                       (dominoes a b)).
  - apply NoDup_nodup.
  - intros w Hw. apply nodup_In. apply in_map. exact Hw.
Qed.

(* The lower cell is a permutation of [0,b), so the fibres are indexed by gen132 b. *)
Lemma locell_is_perm : forall a b w, is_perm w (a + b) -> is_perm (locell b w) b.
Proof.
  intros a b w Hp.
  assert (Hnd : NoDup (locell b w)).
  { unfold locell. apply NoDup_filter. destruct Hp as [_ [H _]]. exact H. }
  assert (Hlt : forall x, In x (locell b w) -> (x < b)%nat).
  { intros x Hx. unfold locell in Hx. apply filter_In in Hx.
    destruct Hx as [_ Hx]. apply Nat.ltb_lt in Hx. exact Hx. }
  assert (H1 : incl (locell b w) (seq 0 b)).
  { intros x Hx. apply Hlt in Hx. apply in_seq. lia. }
  assert (H2 : incl (seq 0 b) (locell b w)).
  { intros x Hx. apply in_seq in Hx. unfold locell. apply filter_In. split.
    - apply (perm_full w (a + b) Hp). lia.
    - apply Nat.ltb_lt. lia. }
  assert (L1 := NoDup_incl_length Hnd H1).
  assert (L2 := NoDup_incl_length (seq_NoDup b 0) H2).
  rewrite length_seq in L1, L2.
  split; [lia | split; [exact Hnd | exact Hlt]].
Qed.

Lemma dominoes_locell_gen132 : forall a b w,
  In w (dominoes a b) -> In (locell b w) (gen132 b).
Proof.
  intros a b w H. apply gen132_spec.
  apply dominoes_spec in H. destruct H as [Hp [_ [H132 _]]].
  split; [apply (locell_is_perm a b w Hp) | exact H132].
Qed.

(* The decreasing lower cell constrains nothing.  By domino_criterion a 1324
   occurrence in a domino is an ascent of the lower cell interleaved with an
   ascent of the upper one, and a decreasing lower cell has no ascent, so over
   that cell the domino condition is exactly "the upper cell avoids 213" and the
   132-freeness of the lower cell is automatic.  d_A counts a free product
   there: which a of the a+b positions carry the upper cell, times the Cat(a)
   patterns it may take. *)

Lemma decpat_dec : forall b r r', (r < r')%nat -> (r' < b)%nat ->
  (nth r' (decpat b) 0%nat < nth r (decpat b) 0%nat)%nat.
Proof.
  intros b r r' H1 H2.
  rewrite (decpat_nth b r ltac:(lia)), (decpat_nth b r' H2). lia.
Qed.

Lemma decpat_avoids_132 : forall b, ~ contains_132 (decpat b).
Proof.
  intros b [i [j [k H]]]. unfold has_132_at in H.
  destruct H as [Hij [Hjk [Hk [Hik _]]]].
  rewrite decpat_length in Hk.
  assert (K := decpat_dec b i k ltac:(lia) ltac:(lia)). lia.
Qed.

(* Two low positions of w descend, read off the filtered cell through rank. *)
Lemma locell_dec_pos : forall b w p1 p2,
  locell b w = decpat b ->
  (p1 < p2)%nat -> (p2 < length w)%nat ->
  (nth p1 w 0%nat < b)%nat -> (nth p2 w 0%nat < b)%nat ->
  (nth p2 w 0%nat < nth p1 w 0%nat)%nat.
Proof.
  intros b w p1 p2 He H12 H2 Hb1 Hb2. unfold locell in He.
  assert (K1 : keeps (fun x => Nat.ltb x b) w p1) by keep.
  assert (K2 : keeps (fun x => Nat.ltb x b) w p2) by keep.
  assert (B2 := rank_bound _ w p2 K2).
  rewrite <- (rank_val _ w p1 K1), <- (rank_val _ w p2 K2), He.
  rewrite He, decpat_length in B2.
  apply decpat_dec; [apply (rank_ord _ w p1 p2 H12 K1 K2) | exact B2].
Qed.

(* Hence no 132 among low positions, which is the first hypothesis of the
   criterion stated positionally. *)
Lemma locell_dec_132_pos : forall b w i j k,
  locell b w = decpat b ->
  (i < j)%nat -> (j < k)%nat -> (k < length w)%nat ->
  (nth i w 0%nat < b)%nat -> (nth j w 0%nat < b)%nat -> (nth k w 0%nat < b)%nat ->
  ~ ((nth i w 0%nat < nth k w 0%nat)%nat /\ (nth k w 0%nat < nth j w 0%nat)%nat).
Proof.
  intros b w i j k He Hij Hjk Hk Bi Bj Bk [H1 _].
  assert (K := locell_dec_pos b w i k He ltac:(lia) Hk Bi Bk). lia.
Qed.

(* and the second hypothesis, transported from the high cell by the same rank
   argument that carries above_gives_above_213 *)
Lemma hicell_213_pos : forall b w i j k,
  ~ contains_213 (hicell b w) ->
  (i < j)%nat -> (j < k)%nat -> (k < length w)%nat ->
  (b <= nth i w 0%nat)%nat -> (b <= nth j w 0%nat)%nat ->
  (b <= nth k w 0%nat)%nat ->
  ~ ((nth j w 0%nat < nth i w 0%nat)%nat /\ (nth i w 0%nat < nth k w 0%nat)%nat).
Proof.
  intros b w i j k Hno Hij Hjk Hk Bi Bj Bk [H1 H2]. apply Hno. unfold hicell.
  apply (filter_213 (fun x => Nat.leb b x) w i j k);
    [ keep | keep | keep | unfold has_213_at; repeat split; assumption ].
Qed.

Theorem dec_cell_domino : forall a b w,
  is_perm w (a + b) ->
  locell b w = decpat b ->
  ~ contains_213 (hicell b w) ->
  In w (dominoes a b).
Proof.
  intros a b w Hp He H213. apply dominoes_spec.
  assert (H132 : ~ contains_132 (locell b w))
    by (rewrite He; apply decpat_avoids_132).
  split; [exact Hp | split; [| split; [exact H132 | exact H213]]].
  intro C.
  destruct (domino_criterion w b
              (fun i j k => locell_dec_132_pos b w i j k He)
              (fun i j k => hicell_213_pos b w i j k H213) C)
    as [p1 [q1 [p2 [q2 [A1 [A2 [A3 [A4 [A5 [A6 [A7 [A8 [A9 A10]]]]]]]]]]]]].
  assert (K := locell_dec_pos b w p1 p2 He ltac:(lia) ltac:(lia) A5 A6). lia.
Qed.

(* so over that cell the domino filter is exactly the 213 condition on the
   upper cell, with nothing else left to check *)
Corollary dec_cell_iff : forall a b w,
  is_perm w (a + b) -> locell b w = decpat b ->
  (In w (dominoes a b) <-> ~ contains_213 (hicell b w)).
Proof.
  intros a b w Hp He. split.
  - intro H. apply dominoes_spec in H. tauto.
  - intro H. exact (dec_cell_domino a b w Hp He H).
Qed.

(* so the domino total is the sum of d_A over all of Av(132)_b *)
Theorem Dcount_over_gen132 : forall a b,
  Dcount a b = fold_right (fun l acc => (dA a b l + acc)%nat) 0%nat (gen132 b).
Proof.
  intros a b. unfold Dcount, dA.
  apply (length_fibres (list nat) (list nat) (list_eq_dec Nat.eq_dec)
                       (locell b) (gen132 b) (dominoes a b)).
  - apply gen132_nodup.
  - intros w Hw. apply (dominoes_locell_gen132 a b w). exact Hw.
Qed.

(* d_A tabulated once, so the strata reduce without rebuilding the domino list. *)
Definition dAtable (a b : nat) : list (list nat * nat) :=
  let D := dominoes a b in
  map (fun l => (l, length (filter (fun w => if list_eq_dec Nat.eq_dec (locell b w) l
                                             then true else false) D)))
      (gen132 b).

Definition natlook (t : list (list nat * nat)) (l : list nat) : nat :=
  fold_right (fun p acc => if list_eq_dec Nat.eq_dec (fst p) l
                           then snd p else acc) 0%nat t.

Definition dAlook (t : list (list nat * nat)) (l : list nat) : Z :=
  Z.of_nat (natlook t l).

Lemma lookup_map_pair : forall (g : list nat -> nat) (ks : list (list nat)) l,
  In l ks ->
  fold_right (fun p acc => if list_eq_dec Nat.eq_dec (fst p) l
                           then snd p else acc)
             0%nat (map (fun x => (x, g x)) ks) = g l.
Proof.
  intros g ks l H. induction ks as [|a ks IH]; [contradiction|].
  cbn [map fold_right fst snd].
  destruct (list_eq_dec Nat.eq_dec a l) as [He | He].
  - subst a. reflexivity.
  - apply IH. destruct H as [H | H]; [contradiction | exact H].
Qed.

Theorem natlook_dAtable : forall a b l,
  In l (gen132 b) -> natlook (dAtable a b) l = dA a b l.
Proof.
  intros a b l H. unfold natlook, dAtable, dA. cbv zeta.
  apply (lookup_map_pair
           (fun x => length (filter (fun w => if list_eq_dec Nat.eq_dec (locell b w) x
                                              then true else false)
                                    (dominoes a b)))
           (gen132 b) l H).
Qed.

Corollary dAlook_dAtable : forall a b l,
  In l (gen132 b) -> dAlook (dAtable a b) l = Z.of_nat (dA a b l).
Proof.
  intros a b l H. unfold dAlook. f_equal. apply natlook_dAtable. exact H.
Qed.

Lemma nfold_ext_in : forall (A : Type) (g h : A -> nat) (l : list A),
  (forall x, In x l -> g x = h x) ->
  fold_right (fun x acc => (g x + acc)%nat) 0%nat l
  = fold_right (fun x acc => (h x + acc)%nat) 0%nat l.
Proof.
  intros A g h l H. induction l as [|a l IH]; cbn [fold_right]; [reflexivity|].
  rewrite (H a (or_introl eq_refl)). f_equal. apply IH.
  intros x Hx. apply H. right. exact Hx.
Qed.

(* The diagonal a = c = m, which is the statistic the tromino bound consumes. *)
Definition dstrata (m : nat) : list stratum :=
  let t := dAtable m m in strata_of (dAlook t) m.

Corollary diag_cov_ge_within : forall m,
  (nsumz (proj_ns (dstrata m)) * defw (dstrata m)
   <= nprodz (proj_ns (dstrata m))
        * (nsumz (proj_ns (dstrata m)) * stP (dstrata m)
           - ssumz (proj_ns (dstrata m)) * ssumz (proj_ns (dstrata m))))%Z.
Proof. intro m. unfold dstrata. cbv zeta. apply strata_cov_ge_within. Qed.

Corollary diag_between_nonneg : forall m,
  (0 <= nsumz (proj_ns (dstrata m)) * qsumz (proj_ns (dstrata m))
        - nprodz (proj_ns (dstrata m))
          * ssumz (proj_ns (dstrata m)) * ssumz (proj_ns (dstrata m)))%Z.
Proof. intro m. unfold dstrata. cbv zeta. apply strata_between_nonneg. Qed.

Theorem diag_S_total : forall m,
  ssumz (proj_ns (dstrata m)) = csum (map (fun l => Z.of_nat (dA m m l)) (gen132 m)).
Proof.
  intro m. unfold dstrata. cbv zeta. rewrite strata_S_total. f_equal.
  apply map_ext_in. intros l Hl. apply dAlook_dAtable. exact Hl.
Qed.

Theorem diag_P_total : forall m,
  stP (dstrata m)
  = csum (map (fun l => (Z.of_nat (dA m m l) * Z.of_nat (dA m m (pinv l)))%Z)
              (gen132 m)).
Proof.
  intro m. unfold dstrata. cbv zeta. rewrite strata_P_total. f_equal.
  apply map_ext_in. intros l Hl. rewrite (dAlook_dAtable m m l Hl).
  rewrite (dAlook_dAtable m m (pinv l)); [reflexivity|].
  apply (Permutation_in _ (pinv_gen132 m)). apply in_map. exact Hl.
Qed.

(* The Chebyshev square at the diagonal, with all three sides cardinalities. *)

Lemma sumAB_map : forall (A : Type) (f : A -> nat * nat) (l : list A),
  sumAB (map f l)
  = fold_right (fun x acc => (fst (f x) * snd (f x) + acc)%nat) 0%nat l.
Proof.
  intros A f. induction l as [|a l IH]; cbn [map sumAB fold_right];
    [reflexivity | rewrite IH; reflexivity].
Qed.

Definition diag_pairs (m : nat) : list (nat * nat) :=
  map (fun b => (dA m m b, dA m m (pinv b))) (gen132 m).

Definition Tcount (m : nat) : nat :=
  fold_right (fun b acc => (dA m m b * dA m m (pinv b) + acc)%nat)
             0%nat (gen132 m).

(* the same total, tabulated, so that one domino build serves every lookup *)
Definition Tcount_tab (m : nat) : nat :=
  let t := dAtable m m in
  fold_right (fun b acc => (natlook t b * natlook t (pinv b) + acc)%nat)
             0%nat (gen132 m).

Theorem Tcount_tab_eq : forall m, Tcount_tab m = Tcount m.
Proof.
  intro m. unfold Tcount_tab, Tcount. cbv zeta.
  apply nfold_ext_in. intros b Hb.
  rewrite (natlook_dAtable m m b Hb).
  rewrite (natlook_dAtable m m (pinv b)); [reflexivity|].
  apply (Permutation_in _ (pinv_gen132 m)). apply in_map. exact Hb.
Qed.

(* and in Z, so the total never exists as a unary nat *)
Definition Tz (m : nat) : Z :=
  let t := dAtable m m in
  fold_right (fun b acc => (Z.of_nat (natlook t b)
                            * Z.of_nat (natlook t (pinv b)) + acc)%Z)
             0%Z (gen132 m).

Lemma foldZ_of_nat : forall (g h : list nat -> nat) (L : list (list nat)),
  fold_right (fun b acc => (Z.of_nat (g b) * Z.of_nat (h b) + acc)%Z) 0%Z L
  = Z.of_nat (fold_right (fun b acc => (g b * h b + acc)%nat) 0%nat L).
Proof.
  intros g h L. induction L as [|a L IH]; cbn [fold_right]; [reflexivity|].
  rewrite IH, Nat2Z.inj_add, Nat2Z.inj_mul. reflexivity.
Qed.

Theorem Tz_eq : forall m, Tz m = Z.of_nat (Tcount m).
Proof.
  intro m. unfold Tz. cbv zeta.
  rewrite (foldZ_of_nat (natlook (dAtable m m))
                        (fun b => natlook (dAtable m m) (pinv b)) (gen132 m)).
  rewrite <- Tcount_tab_eq. unfold Tcount_tab. cbv zeta. reflexivity.
Qed.

Definition chebyshev_holdsZ (m : nat) : bool :=
  Z.leb (Z.of_nat (Dcount m m) * Z.of_nat (Dcount m m))
        (Z.of_nat (card132 m) * Tz m).

Lemma diag_length : forall m, length (diag_pairs m) = card132 m.
Proof. intro m. unfold diag_pairs, card132. apply length_map. Qed.

Lemma diag_sumA : forall m, sumA (diag_pairs m) = Dcount m m.
Proof.
  intro m. unfold diag_pairs. rewrite sumA_map. cbn [fst].
  symmetry. apply Dcount_over_gen132.
Qed.

Lemma diag_sumAB : forall m, sumAB (diag_pairs m) = Tcount m.
Proof.
  intro m. unfold diag_pairs, Tcount. rewrite sumAB_map. reflexivity.
Qed.

Theorem diag_totals_agree : forall m, sumB (diag_pairs m) = sumA (diag_pairs m).
Proof.
  intro m. unfold diag_pairs.
  rewrite sumA_map, sumB_map. cbn [fst snd].
  rewrite <- (nfold_map (list nat) (dA m m) pinv (gen132 m)).
  apply nfold_perm. apply pinv_gen132.
Qed.

Lemma dA_le_Dcount : forall a b l, (dA a b l <= Dcount a b)%nat.
Proof.
  intros a b l. unfold dA, Dcount.
  induction (dominoes a b) as [|w r IH]; cbn [filter length]; [lia|].
  destruct (if list_eq_dec Nat.eq_dec (locell b w) l then true else false);
    cbn [length]; lia.
Qed.

(* The open hypothesis is DIAG_COV below, stated at the strength the square
   needs.  Positive quadrant dependence implies it and is strictly stronger;
   pqd_chebyshev and pqd_square keep that route available over an arbitrary
   list of pairs. *)

(* The square as a decidable test, compared in Z. *)
Definition chebyshev_holds (m : nat) : bool :=
  Z.leb (Z.of_nat (Dcount m m) * Z.of_nat (Dcount m m))
        (Z.of_nat (card132 m) * Z.of_nat (Tcount m)).

Lemma chebyshev_holdsZ_eq : forall m, chebyshev_holdsZ m = chebyshev_holds m.
Proof.
  intro m. unfold chebyshev_holdsZ, chebyshev_holds. rewrite Tz_eq. reflexivity.
Qed.

Lemma chebyshev_holds_spec : forall m,
  chebyshev_holds m = true <->
  (Z.of_nat (Dcount m m) * Z.of_nat (Dcount m m)
   <= Z.of_nat (card132 m) * Z.of_nat (Tcount m))%Z.
Proof. intro m. unfold chebyshev_holds. apply Z.leb_le. Qed.

(* The unconditional instances are proved below, through the mu-based
   enumerators, once genf and gen132f are available. *)


(* Inversion permutes each stratum, so the antisymmetric part sums to zero on each. *)

Lemma invfibre_gen132 : forall m k u, In u (invfibre m k) -> In u (gen132 m).
Proof.
  intros m k u H. unfold invfibre in H. apply filter_In in H. tauto.
Qed.

Theorem pinv_invfibre : forall m k,
  Permutation (map pinv (invfibre m k)) (invfibre m k).
Proof.
  intros m k.
  assert (Hin : forall u, In u (invfibre m k) -> In (pinv u) (invfibre m k)).
  { intros u Hu. assert (Hg := invfibre_gen132 m k u Hu).
    assert (Hp : is_perm u m) by av.
    unfold invfibre in Hu. apply filter_In in Hu. destruct Hu as [_ Hk].
    unfold invfibre. apply filter_In. split.
    - apply (Permutation_in _ (pinv_gen132 m)). apply in_map. exact Hg.
    - rewrite (invcount_pinv u m Hp). exact Hk. }
  apply NoDup_Permutation.
  - apply NoDup_map_inj.
    + unfold invfibre. apply NoDup_filter. apply gen132_nodup.
    + intros x y Hx Hy He.
      assert (Hgx := invfibre_gen132 m k x Hx).
      assert (Hgy := invfibre_gen132 m k y Hy).
      apply gen132_spec in Hgx. apply gen132_spec in Hgy.
      exact (pinv_inj x y m (proj1 Hgx) (proj1 Hgy) He).
  - unfold invfibre. apply NoDup_filter. apply gen132_nodup.
  - intro w. split.
    + intro Hw. apply in_map_iff in Hw. destruct Hw as [u [Hu Huin]].
      subst w. apply Hin. exact Huin.
    + intro Hw. apply in_map_iff. exists (pinv w). split.
      * assert (Hg := invfibre_gen132 m k w Hw).
        assert (Hp : is_perm w m) by av.
        apply (pinv_involutive w m Hp).
      * apply Hin. exact Hw.
Qed.

Lemma csum_map_pinv : forall F m k,
  csum (map (fun b => F (pinv b)) (invfibre m k))
  = csum (map F (invfibre m k)).
Proof.
  intros F m k.
  rewrite <- (map_map pinv F (invfibre m k)).
  apply csum_perm. apply Permutation_map. apply pinv_invfibre.
Qed.

(* The antisymmetric part sums to zero on every stratum. *)
Theorem stratum_antisym_zero : forall F m k,
  csum (map (fun b => (F b - F (pinv b))%Z) (invfibre m k)) = 0%Z.
Proof.
  intros F m k.
  assert (Hs : forall (l : list (list nat)),
            csum (map (fun b => (F b - F (pinv b))%Z) l)
            = (csum (map F l) - csum (map (fun b => F (pinv b)) l))%Z).
  { induction l as [|a l IH]; cbn [map csum]; [reflexivity | rewrite IH; lia]. }
  rewrite Hs, csum_map_pinv. lia.
Qed.

(* Globally too, which is the m-fold sum of the above. *)
Corollary antisym_zero : forall F m,
  csum (map (fun b => (F b - F (pinv b))%Z) (gen132 m)) = 0%Z.
Proof.
  intros F m.
  assert (Hs : forall (l : list (list nat)),
            csum (map (fun b => (F b - F (pinv b))%Z) l)
            = (csum (map F l) - csum (map (fun b => F (pinv b)) l))%Z).
  { induction l as [|a l IH]; cbn [map csum]; [reflexivity | rewrite IH; lia]. }
  rewrite Hs, <- (map_map pinv F (gen132 m)).
  rewrite (csum_perm (map F (map pinv (gen132 m))) (map F (gen132 m))
                     (Permutation_map F (pinv_gen132 m))).
  lia.
Qed.

(* The symmetric and antisymmetric parts, doubled so that they stay in Z. *)
Definition symp (F : list nat -> Z) (b : list nat) : Z := (F b + F (pinv b))%Z.
Definition antip (F : list nat -> Z) (b : list nat) : Z := (F b - F (pinv b))%Z.

Lemma symp_antip_sq : forall F b,
  ((symp F b * symp F b - antip F b * antip F b)
   = 4 * (F b * F (pinv b)))%Z.
Proof. intros F b. unfold symp, antip. ring. Qed.

Lemma sum_symp_gen : forall F (L : list (list nat)),
  Permutation (map pinv L) L ->
  csum (map (symp F) L) = (2 * csum (map F L))%Z.
Proof.
  intros F L H. unfold symp. rewrite csum_map_add.
  rewrite (csum_map_invol (list nat) L F pinv H). ring.
Qed.

Lemma sum_sq_gap : forall F (L : list (list nat)),
  (csum (map (fun b => (symp F b * symp F b)%Z) L)
   = csum (map (fun b => (antip F b * antip F b)%Z) L)
     + 4 * csum (map (fun b => (F b * F (pinv b))%Z) L))%Z.
Proof.
  intros F L.
  assert (H : (csum (map (fun b => (symp F b * symp F b)%Z) L)
               - csum (map (fun b => (antip F b * antip F b)%Z) L)
               = 4 * csum (map (fun b => (F b * F (pinv b))%Z) L))%Z).
  { rewrite <- csum_map_sub.
    rewrite (csum_map_ext (list nat) L
               (fun b => (symp F b * symp F b - antip F b * antip F b)%Z)
               (fun b => (4 * (F b * F (pinv b)))%Z)
               (symp_antip_sq F)).
    apply csum_map_scal. }
  lia.
Qed.

(* Four times the covariance form is the centred symmetric second moment less the
   antisymmetric one, which needs no centring. *)
Theorem cov_is_var_gap : forall F (L : list (list nat)),
  Permutation (map pinv L) L ->
  (4 * (Z.of_nat (length L) * csum (map (fun b => (F b * F (pinv b))%Z) L)
        - csum (map F L) * csum (map F L))
   = (Z.of_nat (length L) * csum (map (fun b => (symp F b * symp F b)%Z) L)
      - csum (map (symp F) L) * csum (map (symp F) L))
     - Z.of_nat (length L)
       * csum (map (fun b => (antip F b * antip F b)%Z) L))%Z.
Proof.
  intros F L H. rewrite (sum_sq_gap F L), (sum_symp_gen F L H). ring.
Qed.

Corollary stratum_hg_identity : forall F m k,
  (4 * (Z.of_nat (length (invfibre m k))
        * csum (map (fun b => (F b * F (pinv b))%Z) (invfibre m k))
        - csum (map F (invfibre m k)) * csum (map F (invfibre m k)))
   = (Z.of_nat (length (invfibre m k))
      * csum (map (fun b => (symp F b * symp F b)%Z) (invfibre m k))
      - csum (map (symp F) (invfibre m k))
        * csum (map (symp F) (invfibre m k)))
     - Z.of_nat (length (invfibre m k))
       * csum (map (fun b => (antip F b * antip F b)%Z) (invfibre m k)))%Z.
Proof. intros F m k. apply cov_is_var_gap. apply pinv_invfibre. Qed.

Corollary global_hg_identity : forall F m,
  (4 * (Z.of_nat (length (gen132 m))
        * csum (map (fun b => (F b * F (pinv b))%Z) (gen132 m))
        - csum (map F (gen132 m)) * csum (map F (gen132 m)))
   = (Z.of_nat (length (gen132 m))
      * csum (map (fun b => (symp F b * symp F b)%Z) (gen132 m))
      - csum (map (symp F) (gen132 m)) * csum (map (symp F) (gen132 m)))
     - Z.of_nat (length (gen132 m))
       * csum (map (fun b => (antip F b * antip F b)%Z) (gen132 m)))%Z.
Proof. intros F m. apply cov_is_var_gap. apply pinv_gen132. Qed.

(* Cov >= 0 exactly when the centred symmetric second moment dominates the
   antisymmetric one. *)
Corollary cov_nonneg_iff_var_gap : forall F (L : list (list nat)),
  Permutation (map pinv L) L ->
  ((0 <= Z.of_nat (length L) * csum (map (fun b => (F b * F (pinv b))%Z) L)
         - csum (map F L) * csum (map F L))%Z
   <-> (Z.of_nat (length L) * csum (map (fun b => (antip F b * antip F b)%Z) L)
        <= Z.of_nat (length L)
             * csum (map (fun b => (symp F b * symp F b)%Z) L)
           - csum (map (symp F) L) * csum (map (symp F) L))%Z).
Proof.
  intros F L H. assert (Hg := cov_is_var_gap F L H). lia.
Qed.

(* Eliminating the symmetric part: the conjecture reads E[(f - f o s)^2] <= 2 Var(f),
   against a free bound of 4 Var(f). *)

Lemma sum_sq_pinv : forall F (L : list (list nat)),
  Permutation (map pinv L) L ->
  csum (map (fun b => (F (pinv b) * F (pinv b))%Z) L)
  = csum (map (fun b => (F b * F b)%Z) L).
Proof.
  intros F L H.
  apply (csum_map_invol (list nat) L (fun x => (F x * F x)%Z) pinv H).
Qed.

Lemma antip_sq_expand : forall F (L : list (list nat)),
  csum (map (fun b => (antip F b * antip F b)%Z) L)
  = (csum (map (fun b => (F b * F b)%Z) L)
     - 2 * csum (map (fun b => (F b * F (pinv b))%Z) L)
     + csum (map (fun b => (F (pinv b) * F (pinv b))%Z) L))%Z.
Proof.
  intros F L. induction L as [|a L IH]; cbn [map csum]; [reflexivity|].
  rewrite IH. unfold antip. ring.
Qed.

Theorem antip_sq_sum : forall F (L : list (list nat)),
  Permutation (map pinv L) L ->
  (csum (map (fun b => (antip F b * antip F b)%Z) L)
   = 2 * (csum (map (fun b => (F b * F b)%Z) L)
          - csum (map (fun b => (F b * F (pinv b))%Z) L)))%Z.
Proof.
  intros F L H. rewrite (antip_sq_expand F L), (sum_sq_pinv F L H). ring.
Qed.

(* so the conjecture, with the symmetric part gone *)
Corollary cov_nonneg_iff_spread : forall F (L : list (list nat)),
  Permutation (map pinv L) L ->
  ((0 <= Z.of_nat (length L) * csum (map (fun b => (F b * F (pinv b))%Z) L)
         - csum (map F L) * csum (map F L))%Z
   <-> (Z.of_nat (length L) * csum (map (fun b => (antip F b * antip F b)%Z) L)
        <= 2 * (Z.of_nat (length L) * csum (map (fun b => (F b * F b)%Z) L)
                - csum (map F L) * csum (map F L)))%Z).
Proof.
  intros F L H. rewrite (antip_sq_sum F L H). lia.
Qed.

Lemma symp_sq_expand : forall F (L : list (list nat)),
  csum (map (fun b => (symp F b * symp F b)%Z) L)
  = (csum (map (fun b => (F b * F b)%Z) L)
     + 2 * csum (map (fun b => (F b * F (pinv b))%Z) L)
     + csum (map (fun b => (F (pinv b) * F (pinv b))%Z) L))%Z.
Proof.
  intros F L. induction L as [|a L IH]; cbn [map csum]; [reflexivity|].
  rewrite IH. unfold symp. ring.
Qed.

Lemma csum_ones : forall (A : Type) (L : list A),
  csum (map (fun _ : A => (1 * 1)%Z) L) = Z.of_nat (length L).
Proof.
  intros A L. induction L as [|a L IH]; cbn [map csum length]; [reflexivity|].
  rewrite IH, Nat2Z.inj_succ. ring.
Qed.

(* Cauchy-Schwarz in scalar form, from the pair form already proved. *)
Lemma csum_sq_bound : forall (A : Type) (u : A -> Z) (L : list A),
  (csum (map u L) * csum (map u L)
   <= Z.of_nat (length L) * csum (map (fun x => (u x * u x)%Z) L))%Z.
Proof.
  intros A u L.
  assert (Hd : dotp (map (fun x => (u x, 1%Z)) L) = csum (map u L)).
  { unfold dotp. rewrite map_map. cbn [fst snd].
    apply csum_map_ext. intro x. ring. }
  assert (Hf : sqf (map (fun x => (u x, 1%Z)) L)
               = csum (map (fun x => (u x * u x)%Z) L)).
  { unfold sqf. rewrite map_map. cbn [fst]. reflexivity. }
  assert (Hs : sqs (map (fun x => (u x, 1%Z)) L) = Z.of_nat (length L)).
  { unfold sqs. rewrite map_map. cbn [snd]. apply csum_ones. }
  assert (H := cauchy_schwarz (map (fun x => (u x, 1%Z)) L)).
  rewrite Hd, Hf, Hs in H. lia.
Qed.

(* Cauchy-Schwarz applied to the symmetric part gives the same statement with a
   4 in place of the 2, unconditionally. *)
Theorem spread_le_four_var : forall F (L : list (list nat)),
  Permutation (map pinv L) L ->
  (Z.of_nat (length L) * csum (map (fun b => (antip F b * antip F b)%Z) L)
   <= 4 * (Z.of_nat (length L) * csum (map (fun b => (F b * F b)%Z) L)
           - csum (map F L) * csum (map F L)))%Z.
Proof.
  intros F L H. rewrite (antip_sq_sum F L H).
  assert (Hcs := csum_sq_bound (list nat) (symp F) L).
  rewrite (sum_symp_gen F L H) in Hcs.
  assert (Hss : csum (map (fun b => (symp F b * symp F b)%Z) L)
                = (2 * (csum (map (fun b => (F b * F b)%Z) L)
                        + csum (map (fun b => (F b * F (pinv b))%Z) L)))%Z).
  { rewrite (symp_sq_expand F L), (sum_sq_pinv F L H). ring. }
  rewrite Hss in Hcs. lia.
Qed.

(* The straight tromino total, d_A against itself; Cauchy-Schwarz bounds it. *)
Definition Tstraight (m : nat) : nat :=
  fold_right (fun b acc => (dA m m b * dA m m b + acc)%nat) 0%nat (gen132 m).

Lemma csum_map_of_nat1 : forall (g : list nat -> nat) (L : list (list nat)),
  csum (map (fun b => Z.of_nat (g b)) L)
  = Z.of_nat (fold_right (fun b acc => (g b + acc)%nat) 0%nat L).
Proof.
  intros g L. induction L as [|a L IH]; cbn [map csum fold_right];
    [reflexivity|].
  rewrite IH, Nat2Z.inj_add. reflexivity.
Qed.

Lemma csum_map_of_nat2 : forall (g h : list nat -> nat) (L : list (list nat)),
  csum (map (fun b => (Z.of_nat (g b) * Z.of_nat (h b))%Z) L)
  = Z.of_nat (fold_right (fun b acc => (g b * h b + acc)%nat) 0%nat L).
Proof.
  intros g h L. induction L as [|a L IH]; cbn [map csum fold_right];
    [reflexivity|].
  rewrite IH, Nat2Z.inj_add, Nat2Z.inj_mul. reflexivity.
Qed.

Theorem straight_chebyshev : forall m,
  (Z.of_nat (Dcount m m) * Z.of_nat (Dcount m m)
   <= Z.of_nat (card132 m) * Z.of_nat (Tstraight m))%Z.
Proof.
  intro m.
  assert (HD : Z.of_nat (Dcount m m)
               = csum (map (fun b => Z.of_nat (dA m m b)) (gen132 m))).
  { rewrite (csum_map_of_nat1 (dA m m) (gen132 m)).
    f_equal. apply Dcount_over_gen132. }
  assert (HT : Z.of_nat (Tstraight m)
               = csum (map (fun b => (Z.of_nat (dA m m b)
                                      * Z.of_nat (dA m m b))%Z) (gen132 m))).
  { unfold Tstraight.
    rewrite (csum_map_of_nat2 (dA m m) (dA m m) (gen132 m)). reflexivity. }
  rewrite HD, HT. unfold card132.
  apply (csum_sq_bound (list nat) (fun b => Z.of_nat (dA m m b)) (gen132 m)).
Qed.

(* the same identity at the diagonal statistic, where the bound consumes it *)
Definition dAz (m : nat) (l : list nat) : Z := Z.of_nat (dA m m l).

Corollary diag_var_gap : forall m,
  (4 * (Z.of_nat (length (gen132 m))
        * csum (map (fun b => (dAz m b * dAz m (pinv b))%Z) (gen132 m))
        - csum (map (dAz m) (gen132 m)) * csum (map (dAz m) (gen132 m)))
   = (Z.of_nat (length (gen132 m))
      * csum (map (fun b => (symp (dAz m) b * symp (dAz m) b)%Z) (gen132 m))
      - csum (map (symp (dAz m)) (gen132 m))
        * csum (map (symp (dAz m)) (gen132 m)))
     - Z.of_nat (length (gen132 m))
       * csum (map (fun b => (antip (dAz m) b * antip (dAz m) b)%Z)
                   (gen132 m)))%Z.
Proof. intro m. apply global_hg_identity. Qed.

(* The open hypothesis, at the pair the tromino bound consumes: the covariance
   of d_A against its transpose is non-negative, which is what the Chebyshev
   square needs.  Positive quadrant dependence implies it by pqd_chebyshev and
   is strictly stronger. *)
Definition DIAG_COV : Prop :=
  forall m,
    (csum (map (dAz m) (gen132 m)) * csum (map (dAz m) (gen132 m))
     <= Z.of_nat (card132 m)
        * csum (map (fun b => (dAz m b * dAz m (pinv b))%Z) (gen132 m)))%Z.

Theorem cov_gives_chebyshev : DIAG_COV ->
  forall m, (Dcount m m * Dcount m m <= card132 m * Tcount m)%nat.
Proof.
  intros HC m. assert (H := HC m).
  assert (HD : csum (map (dAz m) (gen132 m)) = Z.of_nat (Dcount m m)).
  { unfold dAz. rewrite (csum_map_of_nat1 (dA m m) (gen132 m)).
    f_equal. symmetry. apply Dcount_over_gen132. }
  assert (HT : csum (map (fun b => (dAz m b * dAz m (pinv b))%Z) (gen132 m))
               = Z.of_nat (Tcount m)).
  { unfold dAz, Tcount.
    apply (csum_map_of_nat2 (dA m m) (fun b => dA m m (pinv b)) (gen132 m)). }
  rewrite HD, HT in H.
  apply Nat2Z.inj_le. rewrite !Nat2Z.inj_mul. exact H.
Qed.

(* The refined recurrence: legal insertions number one more than the
   right-to-left maxima. *)
Definition safecount (u : list nat) (m : nat) : nat :=
  length (filter (safeb u) (seq 0 (S m))).

Theorem card132_recurrence : forall m,
  card132 (S m)
  = fold_right (fun u acc => (safecount u m + acc)%nat) 0%nat (gen132 m).
Proof.
  intro m. unfold card132, safecount.
  rewrite gen132_S, length_flat_map_gen.
  apply nfold_ext_in. intros u _. apply len_map.
Qed.

Fixpoint rlmax_go (l : list nat) : (nat * nat) :=
  match l with
  | [] => (0%nat, 0%nat)
  | x :: r =>
      let p := rlmax_go r in
      if Nat.eqb (fst p) 0 then (1%nat, x)
      else if Nat.ltb (snd p) x then (S (fst p), x) else p
  end.

Definition rlmax (u : list nat) : nat := fst (rlmax_go u).

(* For a permutation the split point of a legal insertion is forced: the entries
   at or above v are the top m - v values and fill the first m - v positions. *)

Lemma firstn_len_app : forall (l1 l2 : list nat),
  firstn (length l1) (l1 ++ l2) = l1.
Proof.
  induction l1 as [|a l1 IH]; intro l2; cbn [length firstn app];
    [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma filter_all_false : forall (P : nat -> bool) (l : list nat),
  (forall y, In y l -> P y = false) -> filter P l = [].
Proof.
  intros P l. induction l as [|a l IH]; intro H; cbn [filter]; [reflexivity|].
  rewrite (H a (or_introl eq_refl)). apply IH.
  intros y Hy. apply H. right. exact Hy.
Qed.

Lemma count_ge_in_perm : forall u m v, is_perm u m -> (v <= m)%nat ->
  length (filter (fun x => Nat.leb v x) u) = (m - v)%nat.
Proof.
  intros u m v Hp Hv.
  assert (Hnd : NoDup (filter (fun x => Nat.leb v x) u)).
  { apply NoDup_filter. destruct Hp as [_ [H _]]. exact H. }
  assert (H1 : incl (filter (fun x => Nat.leb v x) u) (seq v (m - v))).
  { intros x Hx. apply filter_In in Hx. destruct Hx as [Hin Hge].
    apply Nat.leb_le in Hge. apply in_seq.
    destruct Hp as [_ [_ Hb]]. assert (Hlt := Hb x Hin). lia. }
  assert (H2 : incl (seq v (m - v)) (filter (fun x => Nat.leb v x) u)).
  { intros x Hx. apply in_seq in Hx. apply filter_In. split.
    - apply (perm_full u m Hp). lia.
    - apply Nat.leb_le. lia. }
  assert (L1 := NoDup_incl_length Hnd H1).
  assert (L2 := NoDup_incl_length (seq_NoDup (m - v) v) H2).
  rewrite length_seq in L1, L2. lia.
Qed.

Lemma safe_iff_top_prefix : forall u m v,
  is_perm u m -> (v <= m)%nat ->
  (safe_at u v <-> Forall (fun x => (v <= x)%nat) (firstn (m - v) u)).
Proof.
  intros u m v Hp Hv.
  assert (Hlen : length u = m) by av.
  split.
  - intro Hs. apply safe_iff_split in Hs.
    destruct Hs as [A [B [Heq [HA HB]]]].
    assert (HfA : filter (fun x => Nat.leb v x) A = A).
    { apply filter_all_gen. intros y Hy. apply Nat.leb_le.
      rewrite Forall_forall in HA. apply HA. exact Hy. }
    assert (HfB : filter (fun x => Nat.leb v x) B = []).
    { apply filter_all_false. intros y Hy.
      rewrite Forall_forall in HB. assert (Hy2 := HB y Hy).
      destruct (Nat.leb_spec v y); [lia | reflexivity]. }
    assert (HL : length A = (m - v)%nat).
    { assert (Hc := count_ge_in_perm u m v Hp Hv).
      rewrite Heq, filter_app, HfA, HfB, len_app in Hc.
      cbn [length] in Hc. lia. }
    rewrite Heq, <- HL, firstn_len_app. exact HA.
  - intro HF.
    assert (Heq : u = firstn (m - v) u ++ skipn (m - v) u)
      by (rewrite firstn_skipn; reflexivity).
    assert (HLA : length (firstn (m - v) u) = (m - v)%nat)
      by (rewrite length_firstn; lia).
    assert (HfA : filter (fun x => Nat.leb v x) (firstn (m - v) u)
                  = firstn (m - v) u).
    { apply filter_all_gen. intros y Hy. apply Nat.leb_le.
      rewrite Forall_forall in HF. apply HF. exact Hy. }
    assert (HfB : filter (fun x => Nat.leb v x) (skipn (m - v) u) = []).
    { assert (Hc := count_ge_in_perm u m v Hp Hv).
      rewrite Heq in Hc. rewrite filter_app, HfA, len_app, HLA in Hc.
      destruct (filter (fun x => Nat.leb v x) (skipn (m - v) u)) eqn:E;
        [reflexivity|]. cbn [length] in Hc. lia. }
    apply safe_iff_split. exists (firstn (m - v) u), (skipn (m - v) u).
    split; [exact Heq | split; [exact HF|]].
    rewrite Forall_forall. intros y Hy.
    assert (Hn : Nat.leb v y = false).
    { destruct (Nat.leb v y) eqn:E; [|reflexivity].
      exfalso. assert (In y (filter (fun x => Nat.leb v x) (skipn (m - v) u))).
      { apply filter_In. split; [exact Hy | exact E]. }
      rewrite HfB in H. contradiction. }
    apply Nat.leb_nle in Hn. lia.
Qed.

Definition topsplit (u : list nat) (m k : nat) : bool :=
  forallb (fun x => Nat.leb (m - k) x) (firstn k u).

Theorem safeb_topsplit : forall u m v,
  is_perm u m -> (v <= m)%nat -> safeb u v = topsplit u m (m - v).
Proof.
  intros u m v Hp Hv. unfold topsplit.
  replace (m - (m - v))%nat with v by lia.
  destruct (safeb u v) eqn:E.
  - symmetry. apply forallb_forall. intros x Hx. apply Nat.leb_le.
    assert (Hs : safe_at u v) by (apply safeb_spec; exact E).
    assert (H := proj1 (safe_iff_top_prefix u m v Hp Hv) Hs).
    rewrite Forall_forall in H. apply H. exact Hx.
  - symmetry.
    destruct (forallb (fun x => Nat.leb v x) (firstn (m - v) u)) eqn:F;
      [|reflexivity].
    exfalso.
    assert (Hs : safe_at u v).
    { apply (safe_iff_top_prefix u m v Hp Hv). rewrite Forall_forall.
      intros x Hx. apply Nat.leb_le. rewrite forallb_forall in F.
      apply F. exact Hx. }
    apply safeb_spec in Hs. rewrite E in Hs. discriminate.
Qed.

Lemma filter_ext_in_nat : forall (P Q : nat -> bool) (l : list nat),
  (forall x, In x l -> P x = Q x) -> filter P l = filter Q l.
Proof.
  intros P Q l. induction l as [|a l IH]; intro H; cbn [filter]; [reflexivity|].
  rewrite (H a (or_introl eq_refl)).
  destruct (Q a); [f_equal|]; apply IH; intros x Hx; apply H; right; exact Hx.
Qed.

Lemma length_filter_map : forall (A B : Type) (f : A -> B) (P : B -> bool)
    (l : list A),
  length (filter P (map f l)) = length (filter (fun x => P (f x)) l).
Proof.
  intros A B f P. induction l as [|a l IH]; cbn [map filter]; [reflexivity|].
  destruct (P (f a)); cbn [length]; rewrite IH; reflexivity.
Qed.

Lemma perm_filter_length : forall (P : nat -> bool) (l1 l2 : list nat),
  Permutation l1 l2 -> length (filter P l1) = length (filter P l2).
Proof.
  intros P l1 l2 H. induction H; cbn [filter]; try reflexivity.
  - destruct (P x); cbn [length]; rewrite IHPermutation; reflexivity.
  - destruct (P x); destruct (P y); cbn [length]; reflexivity.
  - rewrite IHPermutation1. exact IHPermutation2.
Qed.

Lemma seq_sub_perm : forall m,
  Permutation (map (fun v => (m - v)%nat) (seq 0 (S m))) (seq 0 (S m)).
Proof.
  intro m. apply NoDup_Permutation.
  - apply NoDup_map_inj; [apply seq_NoDup|].
    intros x y Hx Hy He. apply in_seq in Hx. apply in_seq in Hy. lia.
  - apply seq_NoDup.
  - intro x. split.
    + intro H. apply in_map_iff in H. destruct H as [v [Hv Hin]].
      apply in_seq in Hin. apply in_seq. lia.
    + intro H. apply in_seq in H. apply in_map_iff.
      exists (m - x)%nat. split; [lia|]. apply in_seq. lia.
Qed.

(* The legal insertion values are exactly the skew-decomposition split points. *)
Definition sccount (u : list nat) (m : nat) : nat :=
  length (filter (topsplit u m) (seq 0 (S m))).

Theorem safecount_sccount : forall u m,
  is_perm u m -> safecount u m = sccount u m.
Proof.
  intros u m Hp. unfold safecount, sccount.
  rewrite (filter_ext_in_nat (safeb u) (fun v => topsplit u m (m - v))
             (seq 0 (S m))).
  - rewrite <- (length_filter_map nat nat (fun v => (m - v)%nat)
                  (topsplit u m) (seq 0 (S m))).
    apply perm_filter_length. apply seq_sub_perm.
  - intros v Hv. apply in_seq in Hv. apply safeb_topsplit; [exact Hp | lia].
Qed.

(* so the class recurrence is over split points rather than over insertions *)
Theorem card132_sccount : forall m,
  card132 (S m)
  = fold_right (fun u acc => (sccount u m + acc)%nat) 0%nat (gen132 m).
Proof.
  intro m. rewrite card132_recurrence. apply nfold_ext_in.
  intros u Hu. apply safecount_sccount. av.
Qed.

(* Extending by v keeps the split points at or below m - v and gains the full one. *)

Lemma NoDup_app_l : forall (l1 l2 : list nat),
  NoDup (l1 ++ l2) -> NoDup l1.
Proof.
  induction l1 as [|a l1 IH]; intros l2 H; cbn [app] in H; [constructor|].
  inversion H as [|x xs Hni Hnd]; subst.
  constructor; [| exact (IH l2 Hnd)].
  intro C. apply Hni. apply in_or_app. left. exact C.
Qed.

Lemma NoDup_firstn : forall n (l : list nat), NoDup l -> NoDup (firstn n l).
Proof.
  intros n l H. apply (NoDup_app_l (firstn n l) (skipn n l)).
  rewrite firstn_skipn. exact H.
Qed.

Lemma firstn_app_le : forall n (l1 l2 : list nat),
  (n <= length l1)%nat -> firstn n (l1 ++ l2) = firstn n l1.
Proof.
  induction n as [|n IH]; intros l1 l2 H; [reflexivity|].
  destruct l1 as [|a l1]; cbn [length] in H; [lia|].
  cbn [app firstn]. rewrite IH; [reflexivity | lia].
Qed.

Lemma firstn_map_nat : forall (f : nat -> nat) n (l : list nat),
  firstn n (map f l) = map f (firstn n l).
Proof.
  intros f. induction n as [|n IH]; intro l; [reflexivity|].
  destruct l as [|a l]; cbn [map firstn]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma forallb_false_ex : forall (P : nat -> bool) (l : list nat),
  forallb P l = false -> exists x, In x l /\ P x = false.
Proof.
  intros P l. induction l as [|a l IH]; intro H; cbn [forallb] in H;
    [discriminate|].
  apply Bool.andb_false_iff in H. destruct H as [H | H].
  - exists a. split; [left; reflexivity | exact H].
  - destruct (IH H) as [x [Hx Hp]]. exists x. split; [right; exact Hx | exact Hp].
Qed.

Lemma In_firstn_nat : forall x n (l : list nat), In x (firstn n l) -> In x l.
Proof.
  intros x n l H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H.
Qed.

Lemma topsplit_in_firstn : forall u m j, is_perm u m -> (j <= m)%nat ->
  topsplit u m j = true ->
  forall t, (m - j <= t)%nat -> (t < m)%nat -> In t (firstn j u).
Proof.
  intros u m j Hp Hj Ht t Hlo Hhi.
  assert (Hlen : length u = m) by av.
  assert (HLj : length (firstn j u) = j) by (rewrite length_firstn; lia).
  assert (Hnd : NoDup (firstn j u)).
  { apply NoDup_firstn. destruct Hp as [_ [H _]]. exact H. }
  assert (Hincl : incl (firstn j u) (seq (m - j) j)).
  { intros x Hx. apply in_seq.
    assert (Hin : In x u).
    { apply (In_firstn_nat x j u). exact Hx. }
    destruct Hp as [_ [_ Hb]]. assert (Hxb := Hb x Hin).
    unfold topsplit in Ht. rewrite forallb_forall in Ht.
    assert (Hge := Ht x Hx). apply Nat.leb_le in Hge. lia. }
  assert (Hrev : incl (seq (m - j) j) (firstn j u)).
  { apply (NoDup_length_incl Hnd); [rewrite length_seq; lia | exact Hincl]. }
  apply Hrev. apply in_seq. lia.
Qed.

Theorem topsplit_ext : forall u m v j,
  is_perm u m -> (v <= m)%nat -> (j <= m)%nat ->
  topsplit (ext u v) (S m) j = andb (Nat.leb j (m - v)) (topsplit u m j).
Proof.
  intros u m v j Hp Hv Hj.
  assert (Hlen : length u = m) by av.
  assert (Hfe : firstn j (ext u v) = map (bump v) (firstn j u)).
  { unfold ext. rewrite firstn_app_le, firstn_map_nat;
      [reflexivity | rewrite len_map; lia]. }
  unfold topsplit at 1. rewrite Hfe.
  destruct (topsplit u m j) eqn:E.
  - rewrite Bool.andb_true_r.
    destruct (Nat.leb_spec j (m - v)) as [Hle | Hgt]; cbn [andb].
    + apply forallb_forall. intros y Hy. apply in_map_iff in Hy.
      destruct Hy as [x [Hx Hin]]. subst y.
      unfold topsplit in E. rewrite forallb_forall in E.
      assert (Hge := E x Hin). apply Nat.leb_le in Hge.
      apply Nat.leb_le. unfold bump.
      destruct (Nat.leb_spec v x); lia.
    + destruct (forallb (fun x => Nat.leb (S m - j) x)
                  (map (bump v) (firstn j u))) eqn:F; [exfalso | reflexivity].
      assert (Hjpos : (1 <= j)%nat) by lia.
      assert (Hin := topsplit_in_firstn u m j Hp Hj E (m - j)
                       (Nat.le_refl _) ltac:(lia)).
      rewrite forallb_forall in F.
      assert (HF := F (bump v (m - j)) (in_map _ _ _ Hin)).
      apply Nat.leb_le in HF. unfold bump in HF.
      destruct (Nat.leb_spec v (m - j)); lia.
  - rewrite Bool.andb_false_r.
    destruct (forallb (fun x => Nat.leb (S m - j) x)
                (map (bump v) (firstn j u))) eqn:F; [exfalso | reflexivity].
    unfold topsplit in E.
    destruct (forallb_false_ex (fun x => Nat.leb (m - j) x) (firstn j u) E)
      as [x [Hx Hlt]].
    apply Nat.leb_nle in Hlt.
    rewrite forallb_forall in F.
    assert (HF := F (bump v x) (in_map _ _ _ Hx)).
    apply Nat.leb_le in HF. unfold bump in HF.
    destruct (Nat.leb_spec v x); lia.
Qed.

Lemma topsplit_full : forall w n, topsplit w n n = true.
Proof.
  intros w n. unfold topsplit. rewrite Nat.sub_diag.
  apply forallb_forall. intros x _. apply Nat.leb_le. lia.
Qed.

Theorem sccount_ext : forall u m v,
  is_perm u m -> (v <= m)%nat ->
  sccount (ext u v) (S m)
  = (length (filter (fun j => andb (Nat.leb j (m - v)) (topsplit u m j))
                    (seq 0 (S m))) + 1)%nat.
Proof.
  intros u m v Hp Hv. unfold sccount.
  rewrite (seq_S (S m) 0), filter_app, len_app.
  cbn [filter length]. rewrite Nat.add_0_l.
  rewrite (topsplit_full (ext u v) (S m)). cbn [length].
  f_equal.
  rewrite (filter_ext_in_nat (topsplit (ext u v) (S m))
             (fun j => andb (Nat.leb j (m - v)) (topsplit u m j))
             (seq 0 (S m))); [reflexivity|].
  intros j Hj. apply in_seq in Hj.
  apply topsplit_ext; [exact Hp | exact Hv | lia].
Qed.

(* Filtering an initial segment gives an increasing list, so counting the elements
   at or below each member enumerates 1, 2, ..., length. *)

Definition splits (u : list nat) (m : nat) : list nat :=
  filter (topsplit u m) (seq 0 (S m)).

Definition cntle (l : list nat) (k : nat) : nat :=
  length (filter (fun j => Nat.leb j k) l).

Lemma sccount_splits : forall u m, sccount u m = length (splits u m).
Proof. reflexivity. Qed.

Lemma map_app_ext : forall (f g : nat -> nat) (l : list nat) (x : nat),
  (forall k, In k l -> f k = g k) ->
  map f (l ++ [x]) = map g l ++ [f x].
Proof.
  intros f g l x H. rewrite map_app. cbn [map]. f_equal.
  apply map_ext_in. exact H.
Qed.

Theorem cntle_filter_seq : forall (P : nat -> bool) n,
  map (cntle (filter P (seq 0 n))) (filter P (seq 0 n))
  = seq 1 (length (filter P (seq 0 n))).
Proof.
  intros P. induction n as [|n IH]; [reflexivity|].
  rewrite (seq_S n 0), Nat.add_0_l, filter_app.
  assert (Hlt : forall x, In x (filter P (seq 0 n)) -> (x < n)%nat).
  { intros x Hx. apply filter_In in Hx. destruct Hx as [Hs _].
    apply in_seq in Hs. lia. }
  cbn [filter].
  destruct (P n) eqn:E.
  - assert (Hkeep : forall k, In k (filter P (seq 0 n)) ->
      cntle (filter P (seq 0 n) ++ [n]) k = cntle (filter P (seq 0 n)) k).
    { intros k Hk. unfold cntle. rewrite filter_app. cbn [filter].
      assert (Hn : Nat.leb n k = false)
        by (apply Nat.leb_nle; assert (Hk2 := Hlt k Hk); lia).
      rewrite Hn. rewrite app_nil_r. reflexivity. }
    assert (Hlast : cntle (filter P (seq 0 n) ++ [n]) n
                    = S (length (filter P (seq 0 n)))).
    { unfold cntle. rewrite (filter_all_gen nat (fun j => Nat.leb j n)).
      - rewrite len_app. cbn [length]. lia.
      - intros y Hy. apply in_app_or in Hy. apply Nat.leb_le.
        destruct Hy as [Hy | [Hy | []]]; [assert (H := Hlt y Hy); lia | lia]. }
    rewrite (map_app_ext (cntle (filter P (seq 0 n) ++ [n]))
               (cntle (filter P (seq 0 n))) (filter P (seq 0 n)) n Hkeep).
    rewrite IH, Hlast, len_app. cbn [length].
    replace (length (filter P (seq 0 n)) + 1)%nat
      with (S (length (filter P (seq 0 n)))) by lia.
    rewrite (seq_S (length (filter P (seq 0 n))) 1).
    replace (1 + length (filter P (seq 0 n)))%nat
      with (S (length (filter P (seq 0 n)))) by lia.
    reflexivity.
  - rewrite app_nil_r. exact IH.
Qed.

Corollary cntle_splits : forall u m,
  map (cntle (splits u m)) (splits u m) = seq 1 (sccount u m).
Proof. intros u m. unfold splits, sccount. apply cntle_filter_seq. Qed.

Lemma flat_map_ext_in : forall (A B : Type) (f g : A -> list B) (l : list A),
  (forall x, In x l -> f x = g x) -> flat_map f l = flat_map g l.
Proof.
  intros A B f g l H. induction l as [|a l IH]; cbn [flat_map]; [reflexivity|].
  rewrite (H a (or_introl eq_refl)), IH;
    [reflexivity | intros x Hx; apply H; right; exact Hx].
Qed.

(* mu as a computable value: the least '3' of a 132 occurrence, or None. *)

Definition threevals (u : list nat) : list nat :=
  flat_map (fun i =>
    flat_map (fun j =>
      if existsb (fun k => andb (Nat.ltb (nth i u 0%nat) (nth k u 0%nat))
                                (Nat.ltb (nth k u 0%nat) (nth j u 0%nat)))
                 (idxs u (S j))
      then [nth j u 0%nat] else [])
      (idxs u (S i)))
    (idxs u 0).

Lemma threevals_spec : forall u w, In w (threevals u) <-> three_value u w.
Proof.
  intros u w. unfold threevals. split.
  - intro H. apply in_flat_map in H. destruct H as [i [Hi H]].
    apply in_flat_map in H. destruct H as [j [Hj H]].
    destruct (existsb (fun k => andb (Nat.ltb (nth i u 0%nat) (nth k u 0%nat))
                                     (Nat.ltb (nth k u 0%nat) (nth j u 0%nat)))
                      (idxs u (S j))) eqn:E; [|contradiction].
    destruct H as [Hw | []].
    apply existsb_exists in E. destruct E as [k [Hk Hc]].
    apply in_idxs in Hi. apply in_idxs in Hj. apply in_idxs in Hk.
    apply andb_true_iff in Hc. destruct Hc as [C1 C2].
    apply Nat.ltb_lt in C1. apply Nat.ltb_lt in C2.
    exists i, j, k. split; [| exact Hw].
    unfold has_132_at. cbv zeta. repeat split; lia.
  - intros [i [j [k [H132 Hw]]]].
    unfold has_132_at in H132. cbv zeta in H132.
    destruct H132 as [Hij [Hjk [Hk [H1 H2]]]].
    apply in_flat_map. exists i. split; [apply in_idxs; lia|].
    apply in_flat_map. exists j. split; [apply in_idxs; lia|].
    assert (E : existsb (fun k' => andb (Nat.ltb (nth i u 0%nat) (nth k' u 0%nat))
                                        (Nat.ltb (nth k' u 0%nat) (nth j u 0%nat)))
                        (idxs u (S j)) = true).
    { apply existsb_exists. exists k. split; [apply in_idxs; lia|].
      apply andb_true_iff. split; apply Nat.ltb_lt; assumption. }
    rewrite E. left. exact Hw.
Qed.

Definition minopt (l : list nat) : option nat :=
  fold_right (fun w acc => match acc with
                           | None => Some w
                           | Some a => Some (Nat.min a w)
                           end) None l.

Lemma minopt_nil_iff : forall l, minopt l = None <-> l = [].
Proof.
  intro l. destruct l as [|a l]; cbn [minopt fold_right].
  - split; reflexivity.
  - fold (minopt l). destruct (minopt l); split; discriminate.
Qed.

Lemma minopt_in : forall l v, minopt l = Some v -> In v l.
Proof.
  induction l as [|a l IH]; intros v H; cbn [minopt fold_right] in H;
    [discriminate|].
  fold (minopt l) in H. destruct (minopt l) as [b|] eqn:E.
  - injection H as H. subst v.
    destruct (Nat.min_dec b a) as [M|M]; rewrite M;
      [right; apply IH; reflexivity | left; reflexivity].
  - injection H as H. subst v. left. reflexivity.
Qed.

Lemma minopt_le : forall l v w, minopt l = Some v -> In w l -> (v <= w)%nat.
Proof.
  induction l as [|a l IH]; intros v w H Hin; [contradiction|].
  cbn [minopt fold_right] in H. fold (minopt l) in H.
  destruct (minopt l) as [b|] eqn:E; injection H as H; subst v.
  - destruct Hin as [<- | Hin]; [lia|].
    assert (Hb := IH b w eq_refl Hin). lia.
  - destruct Hin as [<- | Hin]; [lia|].
    exfalso. rewrite (proj1 (minopt_nil_iff l) E) in Hin. contradiction.
Qed.

Definition mub (u : list nat) : option nat := minopt (threevals u).

Lemma mub_is_mu : forall u d, mub u = Some d -> is_mu u d.
Proof.
  intros u d H. unfold mub in H. split.
  - apply threevals_spec. apply minopt_in. exact H.
  - intros w Hw. apply (minopt_le (threevals u) d w H).
    apply threevals_spec. exact Hw.
Qed.

Lemma mub_none_132free : forall u, mub u = None -> ~ contains_132 u.
Proof.
  intros u H. apply profile_empty_iff. intros w Hw.
  apply threevals_spec in Hw. unfold mub in H.
  rewrite (proj1 (minopt_nil_iff (threevals u)) H) in Hw. contradiction.
Qed.

Definition legalf (u : list nat) (y : nat) : bool :=
  match mub u with None => true | Some d => Nat.leb y d end.

Theorem legalf_legalb : forall u y, ~ contains_1324 u -> legalf u y = legalb u y.
Proof.
  intros u y Hu. unfold legalf. destruct (mub u) as [d|] eqn:E.
  - assert (Hmu : is_mu u d) by (apply mub_is_mu; exact E).
    destruct (Nat.leb_spec y d) as [Hle|Hgt].
    + symmetry. apply legalb_spec. apply (legal_iff_le_mu u d Hu Hmu). exact Hle.
    + symmetry. destruct (legalb u y) eqn:F; [|reflexivity].
      exfalso. apply legalb_spec in F.
      apply (legal_iff_le_mu u d Hu Hmu) in F. lia.
  - symmetry. apply legalb_spec. apply legal_all_when_132_free.
    apply mub_none_132free. exact E.
Qed.

(* The branching recurrence with the fibre count evaluated: each word of the
   level below contributes min(mu, m) + 1 successors, and a 132-free word
   contributes m + 1.  This is card_succ with fibre_count substituted, so the
   level ratio card (m+1) / card m is the mean of that statistic. *)
Definition mucount (u : list nat) (m : nat) : nat :=
  match mub u with None => S m | Some d => S (Nat.min d m) end.

Theorem card_succ_mu : forall m,
  card (S m) = fold_right (fun u acc => (mucount u m + acc)%nat) 0%nat (gen m).
Proof.
  intro m. rewrite card_succ. apply nfold_ext_in. intros u Hu.
  assert (Hav : ~ contains_1324 u) by av.
  unfold mucount. destruct (mub u) as [d|] eqn:E.
  - apply (fibre_count u m d Hav). apply mub_is_mu. exact E.
  - apply fibre_count_free. apply mub_none_132free. exact E.
Qed.

(* The enumerator with mu hoisted out of the inner loop. *)
Fixpoint genf (m : nat) : list (list nat) :=
  match m with
  | 0%nat => [[]]
  | S m' => flat_map (fun u =>
              let d := mub u in
              map (ext u)
                  (filter (fun y => match d with
                                    | None => true
                                    | Some a => Nat.leb y a
                                    end) (seq 0 (S m'))))
              (genf m')
  end.

Theorem genf_eq : forall m, genf m = gen m.
Proof.
  induction m as [|m IH]; [reflexivity|].
  cbn [genf]. rewrite IH, gen_S.
  apply flat_map_ext_in. intros u Hu. cbv zeta. f_equal.
  apply filter_ext_in_nat. intros y _.
  change (match mub u with None => true | Some a => Nat.leb y a end)
    with (legalf u y).
  apply legalf_legalb. av.
Qed.

(* The same enumerator with the O(n^2) safety decider replaced by the O(n)
   prefix test, which safeb_topsplit proves equal on permutations. *)

Fixpoint gen132f (m : nat) : list (list nat) :=
  match m with
  | 0%nat => [[]]
  | S m' => flat_map (fun u => map (ext u)
                       (filter (fun v => topsplit u m' (m' - v)) (seq 0 (S m'))))
                     (gen132f m')
  end.

Theorem gen132f_eq : forall m, gen132f m = gen132 m.
Proof.
  induction m as [|m IH]; [reflexivity|].
  cbn [gen132f]. rewrite IH, gen132_S.
  apply flat_map_ext_in. intros u Hu. f_equal.
  symmetry. apply filter_ext_in_nat. intros v Hv. apply in_seq in Hv.
  apply safeb_topsplit; [av | lia].
Qed.

(* The domino layer over the fast enumerators, each equal to its original. *)

Definition dominoesf (a b : nat) : list (list nat) :=
  filter (dominob b) (genf (a + b)).

Lemma dominoesf_eq : forall a b, dominoesf a b = dominoes a b.
Proof. intros a b. unfold dominoesf, dominoes. rewrite genf_eq. reflexivity. Qed.

Definition Dcountf (a b : nat) : nat := length (dominoesf a b).

Lemma Dcountf_eq : forall a b, Dcountf a b = Dcount a b.
Proof. intros a b. unfold Dcountf, Dcount. rewrite dominoesf_eq. reflexivity. Qed.

Definition dAtablef (a b : nat) : list (list nat * nat) :=
  let D := dominoesf a b in
  map (fun l => (l, length (filter (fun w => if list_eq_dec Nat.eq_dec (locell b w) l
                                             then true else false) D)))
      (gen132f b).

Lemma dAtablef_eq : forall a b, dAtablef a b = dAtable a b.
Proof.
  intros a b. unfold dAtablef, dAtable. cbv zeta.
  rewrite dominoesf_eq, gen132f_eq. reflexivity.
Qed.

Definition Tzf (m : nat) : Z :=
  let t := dAtablef m m in
  fold_right (fun b acc => (Z.of_nat (natlook t b)
                            * Z.of_nat (natlook t (pinv b)) + acc)%Z)
             0%Z (gen132f m).

Lemma Tzf_eq : forall m, Tzf m = Tz m.
Proof.
  intro m. unfold Tzf, Tz. cbv zeta. rewrite dAtablef_eq, gen132f_eq. reflexivity.
Qed.

Definition chebyshev_holdsZf (m : nat) : bool :=
  Z.leb (Z.of_nat (Dcountf m m) * Z.of_nat (Dcountf m m))
        (Z.of_nat (length (gen132f m)) * Tzf m).

Lemma chebyshev_holdsZf_eq : forall m, chebyshev_holdsZf m = chebyshev_holdsZ m.
Proof.
  intro m. unfold chebyshev_holdsZf, chebyshev_holdsZ.
  rewrite Dcountf_eq, Tzf_eq, gen132f_eq. reflexivity.
Qed.

(* A tromino is the fibre product of a vertical domino over its lower cell with
   a horizontal domino beside that same cell, which tromino_fibre licenses: no
   1324 occurrence uses points of both outer cells, so once the shared cell is
   fixed the two factors are independent.  Transposing a domino turns vertical
   into horizontal and inverts the shared cell, so the horizontal factor is a
   vertical domino whose lower cell is the inverse of the first one's.
   `glued m` is that set of pairs at m points per cell, and Tcount_glued says
   Tcount is its cardinality. *)

Definition glued (m : nat) : list (list nat * list nat) :=
  filter (fun p => if list_eq_dec Nat.eq_dec
                       (locell m (snd p)) (pinv (locell m (fst p)))
                   then true else false)
         (list_prod (dominoes m m) (dominoes m m)).

Lemma length_filter_prod : forall (A B : Type) (P : A * B -> bool)
    (L1 : list A) (L2 : list B),
  length (filter P (list_prod L1 L2))
  = fold_right (fun v acc => (length (filter (fun h => P (v, h)) L2) + acc)%nat)
               0%nat L1.
Proof.
  intros A B P L1 L2. induction L1 as [|a L1 IH]; [reflexivity|].
  cbn [list_prod fold_right]. rewrite filter_app, len_app_gen, IH. f_equal.
  apply (length_filter_map B (A * B) (fun y => (a, y)) P L2).
Qed.

Lemma glued_fold : forall m,
  length (glued m)
  = fold_right (fun v acc => (dA m m (pinv (locell m v)) + acc)%nat) 0%nat
               (dominoes m m).
Proof.
  intro m. unfold glued. rewrite length_filter_prod.
  apply nfold_ext_in. intros v _. reflexivity.
Qed.

Lemma csum_map_ext_in : forall (A : Type) (L : list A) (u v : A -> Z),
  (forall x, In x L -> u x = v x) -> csum (map u L) = csum (map v L).
Proof.
  intros A L u v H. induction L as [|a L IH]; cbn [map csum]; [reflexivity|].
  rewrite (H a (or_introl eq_refl)), IH; [reflexivity|].
  intros x Hx. apply H. right. exact Hx.
Qed.

Lemma csum_const : forall (A : Type) (L : list A) (c : Z),
  csum (map (fun _ : A => c) L) = (Z.of_nat (length L) * c)%Z.
Proof.
  intros A L c. induction L as [|a L IH]; cbn [map csum length]; [ring|].
  rewrite IH, Nat2Z.inj_succ. ring.
Qed.

Lemma foldZ_csum : forall (A : Type) (h : A -> Z) (l : list A),
  foldZ h l = csum (map h l).
Proof.
  intros A h l. induction l as [|a l IH]; cbn [map csum]; [reflexivity|].
  rewrite foldZ_cons, IH. reflexivity.
Qed.

Theorem Tcount_glued : forall m, Tcount m = length (glued m).
Proof.
  intro m. apply Nat2Z.inj. rewrite glued_fold.
  rewrite <- (csum_map_of_nat1
                (fun v => dA m m (pinv (locell m v))) (dominoes m m)).
  rewrite (csum_fibres (list nat) (list nat) (list_eq_dec Nat.eq_dec)
             (locell m) (gen132 m) (dominoes m m)
             (fun v => Z.of_nat (dA m m (pinv (locell m v))))
             (gen132_nodup m)
             (fun w Hw => dominoes_locell_gen132 m m w Hw)).
  unfold Tcount.
  rewrite <- (csum_map_of_nat2 (dA m m) (fun b => dA m m (pinv b)) (gen132 m)).
  rewrite foldZ_csum. f_equal. apply map_ext. intro b.
  (* on the fibre over b the summand is constant, so the inner sum is the fibre
     size times that constant, and the fibre size is dA m m b by definition *)
  rewrite (csum_map_ext_in (list nat)
             (filter (fun x => if list_eq_dec Nat.eq_dec (locell m x) b
                               then true else false) (dominoes m m))
             (fun v => Z.of_nat (dA m m (pinv (locell m v))))
             (fun _ => Z.of_nat (dA m m (pinv b)))).
  - rewrite csum_const. reflexivity.
  - intros x Hx. apply filter_In in Hx. destruct Hx as [_ He].
    destruct (list_eq_dec Nat.eq_dec (locell m x) b) as [E|E];
      [rewrite E; reflexivity | discriminate].
Qed.

Corollary Tz_glued : forall m, Tz m = Z.of_nat (length (glued m)).
Proof. intro m. rewrite Tz_eq, Tcount_glued. reflexivity. Qed.

(* The counts, evaluated through the fast enumerators.  Routing the reduction
   through Dcountf_eq and Tzf_eq is what makes these affordable: the same four
   statements over dominoes and Tcount directly do not terminate here. *)

Theorem domino_4 : Z.of_nat (Dcount 4 4) = 9751%Z.
Proof. rewrite <- Dcountf_eq. vm_compute. reflexivity. Qed.

Theorem tromino_4 : Tz 4 = 6949612%Z.
Proof. rewrite <- Tzf_eq. vm_compute. reflexivity. Qed.

(* The test read off values already computed, so the enumeration is not
   repeated inside it. *)
Lemma chebyshevZ_of_vals : forall m D T c,
  Z.of_nat (Dcount m m) = D -> Tz m = T -> card132 m = c ->
  Z.leb (D * D) (Z.of_nat c * T) = true -> chebyshev_holdsZ m = true.
Proof.
  intros m D T c HD HT Hc H. unfold chebyshev_holdsZ.
  rewrite HD, HT, Hc. exact H.
Qed.

Lemma card132_4_val : card132 4 = 14%nat.
Proof. vm_compute. reflexivity. Qed.

(* 9751^2 = 95082001 against 14 * 6949612 = 97294568 *)
Lemma chebyshevZ_4 : chebyshev_holdsZ 4 = true.
Proof.
  apply (chebyshevZ_of_vals 4 9751 6949612 14
           domino_4 tromino_4 card132_4_val).
  reflexivity.
Qed.

Theorem chebyshev_upto_4 : forall m, (m <= 4)%nat -> chebyshev_holds m = true.
Proof.
  intros m Hm. rewrite <- chebyshev_holdsZ_eq.
  destruct m as [|[|[|[|[|m]]]]]; try lia.
  - rewrite <- chebyshev_holdsZf_eq; vm_compute; reflexivity.
  - rewrite <- chebyshev_holdsZf_eq; vm_compute; reflexivity.
  - rewrite <- chebyshev_holdsZf_eq; vm_compute; reflexivity.
  - rewrite <- chebyshev_holdsZf_eq; vm_compute; reflexivity.
  - exact chebyshevZ_4.
Qed.

Corollary chebyshev_le_4 : forall m, (m <= 4)%nat ->
  (Z.of_nat (Dcount m m) * Z.of_nat (Dcount m m)
   <= Z.of_nat (card132 m) * Z.of_nat (Tcount m))%Z.
Proof.
  intros m Hm. apply chebyshev_holds_spec. apply chebyshev_upto_4. exact Hm.
Qed.

(* One size further takes minutes to evaluate and lives in Av1324_big.v. *)

(* The Catalan triangle: a word with s split points has s children, carrying
   2, 3, ..., s + 1 split points, one each. *)

Lemma map_filter_comm : forall (f : nat -> nat) (Q : nat -> bool) (l : list nat),
  map f (filter (fun x => Q (f x)) l) = filter Q (map f l).
Proof.
  intros f Q. induction l as [|a l IH]; cbn [map filter]; [reflexivity|].
  destruct (Q (f a)); cbn [map]; rewrite IH; reflexivity.
Qed.

Definition children (u : list nat) (m : nat) : list (list nat) :=
  map (ext u) (filter (safeb u) (seq 0 (S m))).

Lemma children_gen132 : forall m,
  gen132 (S m) = flat_map (fun u => children u m) (gen132 m).
Proof. intro m. rewrite gen132_S. reflexivity. Qed.

Theorem children_sccounts : forall u m, is_perm u m ->
  Permutation (map (fun w => sccount w (S m)) (children u m))
              (seq 2 (sccount u m)).
Proof.
  intros u m Hp. unfold children. rewrite map_map.
  assert (Hval : map (fun v => sccount (ext u v) (S m))
                     (filter (safeb u) (seq 0 (S m)))
                 = map (fun v => (cntle (splits u m) (m - v) + 1)%nat)
                       (filter (safeb u) (seq 0 (S m)))).
  { apply map_ext_in. intros v Hv. apply filter_In in Hv.
    destruct Hv as [Hs _]. apply in_seq in Hs.
    rewrite (sccount_ext u m v Hp ltac:(lia)). f_equal.
    unfold cntle, splits. rewrite filter_filter.
    apply (f_equal (@length nat)). apply filter_ext_in_nat.
    intros j _. apply Bool.andb_comm. }
  rewrite Hval.
  assert (Hsel : filter (safeb u) (seq 0 (S m))
                 = filter (fun v => topsplit u m (m - v)) (seq 0 (S m))).
  { apply filter_ext_in_nat. intros v Hv. apply in_seq in Hv.
    apply safeb_topsplit; [exact Hp | lia]. }
  rewrite Hsel.
  rewrite <- (map_map (fun v => (m - v)%nat)
                      (fun k => (cntle (splits u m) k + 1)%nat)).
  apply (Permutation_trans
           (l' := map (fun k => (cntle (splits u m) k + 1)%nat) (splits u m))).
  - apply Permutation_map.
    rewrite (map_filter_comm (fun v => (m - v)%nat) (topsplit u m)).
    unfold splits. apply perm_filter. apply seq_sub_perm.
  - rewrite <- (map_map (cntle (splits u m)) (fun x => (x + 1)%nat)).
    rewrite cntle_splits.
    assert (Hs1 : forall x : nat, (x + 1)%nat = S x) by (intro x; lia).
    rewrite (map_ext (fun x : nat => (x + 1)%nat) S Hs1).
    rewrite seq_shift. apply Permutation_refl.
Qed.

(* Checked exhaustively at every size the enumeration reaches. *)
Theorem safecount_rlmax_upto_6 : forall m, (m <= 6)%nat ->
  forallb (fun u => Nat.eqb (safecount u m) (S (rlmax u))) (gen132 m) = true.
Proof.
  intros m Hm. destruct m as [|[|[|[|[|[|[|m]]]]]]]; try lia;
    vm_compute; reflexivity.
Qed.

Corollary card132_rlmax_upto_6 : forall m, (m <= 6)%nat ->
  card132 (S m)
  = fold_right (fun u acc => (S (rlmax u) + acc)%nat) 0%nat (gen132 m).
Proof.
  intros m Hm. rewrite card132_recurrence. apply nfold_ext_in.
  intros u Hu. assert (H := safecount_rlmax_upto_6 m Hm).
  rewrite forallb_forall in H. apply Nat.eqb_eq. apply H. exact Hu.
Qed.

(* The d = 1 column: appending to a 132-free word cannot create a 1324, so the
   avoidance filter is vacuous and the column is (M+1)*Cat(M). *)

Lemma filter_flat_map : forall (A B : Type) (P : B -> bool) (f : A -> list B)
    (l : list A),
  filter P (flat_map f l) = flat_map (fun x => filter P (f x)) l.
Proof.
  intros A B P f. induction l as [|a l IH]; cbn [flat_map]; [reflexivity|].
  rewrite filter_app, IH. reflexivity.
Qed.

Lemma firstn_ext : forall u v, firstn (length u) (ext u v) = map (bump v) u.
Proof.
  intros u v. unfold ext.
  replace (length u) with (length (map (bump v) u)) by apply len_map.
  apply firstn_len_app.
Qed.

Lemma legalb_of_avoids132 : forall u v, ~ contains_132 u -> legalb u v = true.
Proof.
  intros u v H. apply legalb_spec. unfold legal.
  intro C. apply H. apply (tail_1324_gives_132 u v). exact C.
Qed.

Lemma avoids132b_ext : forall M u v, length u = M ->
  avoids132b (firstn M (ext u v)) = avoids132b u.
Proof.
  intros M u v HL. rewrite <- HL, firstn_ext. unfold avoids132b.
  destruct (contains_132_dec (map (bump v) u)) as [H|H];
  destruct (contains_132_dec u) as [H2|H2]; try reflexivity.
  - exfalso. apply H2. apply (contains_132_map v u). exact H.
  - exfalso. apply H. apply (contains_132_map v u). exact H2.
Qed.

Lemma filter_map_ext : forall M u S, length u = M ->
  filter (fun w => avoids132b (firstn M w)) (map (ext u) S)
  = (if avoids132b u then map (ext u) S else []).
Proof.
  intros M u S HL. induction S as [|v S IH]; cbn [map filter].
  - destruct (avoids132b u); reflexivity.
  - rewrite (avoids132b_ext M u v HL), IH.
    destruct (avoids132b u); reflexivity.
Qed.

Lemma filter_gen_gen132 : forall M,
  Permutation (filter (fun u => avoids132b u) (gen M)) (gen132 M).
Proof.
  intro M. apply NoDup_Permutation.
  - apply NoDup_filter. apply gen_nodup.
  - apply gen132_nodup.
  - intro w. rewrite filter_In. split.
    + intros [Hg Ha]. apply gen132_spec. split.
      * av.
      * apply avoids132b_true. exact Ha.
    + intro Hw. split; [apply gen132_incl; exact Hw|].
      apply avoids132b_intro. av.
Qed.

Theorem Ddiag_one : forall M, Ddiag 1 M = (S M * card132 M)%nat.
Proof.
  intro M. unfold Ddiag.
  replace (M + 1)%nat with (S M) by lia.
  rewrite gen_S, filter_flat_map, length_flat_map_gen.
  assert (Key : forall u, In u (gen M) ->
    length (filter (fun w => avoids132b (firstn M w))
              (map (ext u) (filter (legalb u) (seq 0 (S M)))))
    = (if avoids132b u then S M else 0)%nat).
  { intros u Hu.
    assert (HL : length u = M).
    { av. }
    rewrite (filter_map_ext M u _ HL).
    destruct (avoids132b u) eqn:E; [|reflexivity].
    assert (HF : filter (legalb u) (seq 0 (S M)) = seq 0 (S M)).
    { apply filter_all_gen. intros y _. apply legalb_of_avoids132.
      apply avoids132b_true. exact E. }
    rewrite HF, len_map. apply length_seq. }
  rewrite (nfold_ext_in (list nat)
             (fun u => length (filter (fun w => avoids132b (firstn M w))
                          (map (ext u) (filter (legalb u) (seq 0 (S M))))))
             (fun u => if avoids132b u then S M else 0%nat)
             (gen M) Key).
  assert (Sum : forall (l : list (list nat)),
    fold_right (fun u acc => ((if avoids132b u then S M else 0) + acc)%nat)
               0%nat l
    = (S M * length (filter (fun u => avoids132b u) l))%nat).
  { induction l as [|a l IH]; cbn [fold_right filter length]; [lia|].
    destruct (avoids132b a) eqn:E; cbn [length]; rewrite IH; lia. }
  rewrite Sum. f_equal. unfold card132.
  apply Permutation_length. apply filter_gen_gen132.
Qed.

(* The Catalan triangle as a statement about the class rather than about one
   word.  children_sccounts says a 132-avoider with s split points has children
   carrying 2, 3, ..., s+1 split points, one each.  Summing that over the class
   turns it into the row recurrence

       T(m+1, j) = # { u in Av(132)_m : sccount u >= j - 1 },

   so each row is the cumulative sum of the one above it, read from the right.
   The rows are 1; 1,1; 2,2,1; 5,5,3,1; 14,14,9,4,1, the ballot triangle. *)

Definition Ttri (m j : nat) : nat :=
  length (filter (fun u => Nat.eqb (sccount u m) j) (gen132 m)).

Lemma count_eqb_seq_out : forall n s j, (j < s)%nat \/ (s + n <= j)%nat ->
  length (filter (fun v => Nat.eqb v j) (seq s n)) = 0%nat.
Proof.
  induction n as [|n IH]; intros s j H; [reflexivity|].
  cbn [seq filter]. destruct (Nat.eqb_spec s j) as [E|E]; [lia|].
  apply IH. lia.
Qed.

Lemma count_eqb_seq_in : forall n s j, (s <= j)%nat -> (j < s + n)%nat ->
  length (filter (fun v => Nat.eqb v j) (seq s n)) = 1%nat.
Proof.
  induction n as [|n IH]; intros s j H1 H2; [lia|].
  cbn [seq filter]. destruct (Nat.eqb_spec s j) as [E|E].
  - subst j. cbn [length]. f_equal. apply count_eqb_seq_out. left. lia.
  - apply IH; lia.
Qed.

Lemma length_filter_fold : forall (A : Type) (P : A -> bool) (l : list A),
  length (filter P l)
  = fold_right (fun x acc => ((if P x then 1 else 0) + acc)%nat) 0%nat l.
Proof.
  intros A P. induction l as [|a l IH]; cbn [filter fold_right]; [reflexivity|].
  destruct (P a); cbn [length]; rewrite IH; reflexivity.
Qed.

Lemma length_filter_eqb_map : forall (A : Type) (g : A -> nat) (j : nat)
    (l : list A),
  length (filter (fun x => Nat.eqb (g x) j) l)
  = length (filter (fun v => Nat.eqb v j) (map g l)).
Proof.
  intros A g j. induction l as [|a l IH]; cbn [map filter]; [reflexivity|].
  destruct (Nat.eqb (g a) j); cbn [length]; rewrite IH; reflexivity.
Qed.

(* One word contributes exactly one child at each split count from 2 to s+1. *)
Lemma children_count : forall u m j, is_perm u m -> (2 <= j)%nat ->
  length (filter (fun w => Nat.eqb (sccount w (S m)) j) (children u m))
  = (if Nat.leb j (S (sccount u m)) then 1 else 0)%nat.
Proof.
  intros u m j Hp Hj.
  rewrite (length_filter_eqb_map (list nat) (fun w => sccount w (S m)) j
             (children u m)).
  rewrite (perm_filter_length (fun v => Nat.eqb v j)
             (map (fun w => sccount w (S m)) (children u m))
             (seq 2 (sccount u m)) (children_sccounts u m Hp)).
  destruct (Nat.leb_spec j (S (sccount u m))) as [H|H].
  - apply count_eqb_seq_in; lia.
  - apply count_eqb_seq_out. right. lia.
Qed.

Theorem Ttri_rec : forall m j, (2 <= j)%nat ->
  Ttri (S m) j
  = length (filter (fun u => Nat.leb (j - 1) (sccount u m)) (gen132 m)).
Proof.
  intros m j Hj. unfold Ttri.
  rewrite children_gen132, filter_flat_map, length_flat_map_gen.
  rewrite (length_filter_fold (list nat)
             (fun u => Nat.leb (j - 1) (sccount u m)) (gen132 m)).
  apply nfold_ext_in. intros u Hu.
  assert (Hp : is_perm u m) by av.
  rewrite (children_count u m j Hp Hj).
  destruct (Nat.leb_spec j (S (sccount u m)));
    destruct (Nat.leb_spec (j - 1) (sccount u m));
    solve [reflexivity | lia].
Qed.

(* The row above the first is empty below j = 2, so the recurrence covers every
   entry that occurs. *)
Theorem Ttri_low : forall m j, (j <= 1)%nat -> Ttri (S m) j = 0%nat.
Proof.
  intros m j Hj. unfold Ttri.
  rewrite children_gen132, filter_flat_map, length_flat_map_gen.
  transitivity (fold_right (fun (_ : list nat) acc => (0 + acc)%nat) 0%nat
                           (gen132 m)).
  - apply nfold_ext_in. intros u Hu.
    assert (Hp : is_perm u m) by av.
    rewrite (length_filter_eqb_map (list nat) (fun w => sccount w (S m)) j
               (children u m)).
    rewrite (perm_filter_length (fun v => Nat.eqb v j)
               (map (fun w => sccount w (S m)) (children u m))
               (seq 2 (sccount u m)) (children_sccounts u m Hp)).
    apply count_eqb_seq_out. left. lia.
  - clear. induction (gen132 m) as [|a l IH]; cbn [fold_right];
      [reflexivity | exact IH].
Qed.

Lemma filter_le_split : forall (A : Type) (g : A -> nat) (k : nat) (l : list A),
  length (filter (fun x => Nat.leb k (g x)) l)
  = (length (filter (fun x => Nat.leb (S k) (g x)) l)
     + length (filter (fun x => Nat.eqb (g x) k) l))%nat.
Proof.
  intros A g k. induction l as [|a l IH]; cbn [filter]; [reflexivity|].
  destruct (Nat.leb_spec k (g a));
    destruct (Nat.leb_spec (S k) (g a));
    destruct (Nat.eqb_spec (g a) k);
    cbn [length]; lia.
Qed.

(* Differencing the cumulative recurrence in j gives the ballot recurrence: an
   entry is the entry to its right plus the entry above and to its left. *)
Theorem Ttri_step : forall m j, (2 <= j)%nat ->
  Ttri (S m) j = (Ttri (S m) (S j) + Ttri m (j - 1))%nat.
Proof.
  intros m j Hj.
  rewrite (Ttri_rec m j Hj), (Ttri_rec m (S j) ltac:(lia)).
  replace (S j - 1)%nat with (S (j - 1))%nat by lia.
  unfold Ttri.
  apply (filter_le_split (list nat) (fun u => sccount u m) (j - 1) (gen132 m)).
Qed.

Lemma filter_ext_gen : forall (A : Type) (P Q : A -> bool) (l : list A),
  (forall x, P x = Q x) -> filter P l = filter Q l.
Proof.
  intros A P Q l H. induction l as [|a l IH]; cbn [filter]; [reflexivity|].
  rewrite (H a), IH. reflexivity.
Qed.

Lemma length_filter_le_gen : forall (A : Type) (P : A -> bool) (l : list A),
  (length (filter P l) <= length l)%nat.
Proof.
  intros A P. induction l as [|a l IH]; cbn [filter length]; [lia|].
  destruct (P a); cbn [length]; lia.
Qed.

Lemma eqdec_eqb : forall a b : nat,
  (if Nat.eq_dec a b then true else false) = Nat.eqb a b.
Proof.
  intros a b. destruct (Nat.eq_dec a b) as [E|E].
  - subst. symmetry. apply Nat.eqb_refl.
  - symmetry. apply Nat.eqb_neq. exact E.
Qed.

(* The row sums are the class sizes: every avoider has a split count, and it is
   at most m + 1, so the whole row lies in [0, m+2). *)
Theorem Ttri_row : forall m,
  fold_right (fun j acc => (Ttri m j + acc)%nat) 0%nat (seq 0 (S (S m)))
  = card132 m.
Proof.
  intro m.
  assert (Hcov : forall u, In u (gen132 m) ->
                   In (sccount u m) (seq 0 (S (S m)))).
  { intros u _. apply in_seq. split; [lia|].
    unfold sccount.
    assert (K := length_filter_le_gen nat (topsplit u m) (seq 0 (S m))).
    rewrite length_seq in K. lia. }
  unfold card132.
  rewrite (length_fibres nat (list nat) Nat.eq_dec (fun u => sccount u m)
             (seq 0 (S (S m))) (gen132 m) (seq_NoDup (S (S m)) 0) Hcov).
  apply nfold_ext_in. intros j _. unfold Ttri. f_equal.
  apply filter_ext_gen. intro u. symmetry. apply eqdec_eqb.
Qed.

(* card132 m = Cat m, from Segner's convolution alone.

   Writing a = card132 and W(m) = sum_{k=0}^{m} (k+1) a(k) a(m-k), reversing the
   summation index carries the weight k+1 to m-k+1, so the two readings of W
   give 2 W(m) = (m+2) a(m+1).  Reading W(m) the other way, by substituting the
   ratio at every k <= m and reversing once more, gives W(m) = (2m+1) a(m).  The
   two together are CARD132_RATIO, and card132_binom_of_ratio then supplies the
   closed count.  Every step is a sum over seq 0 (S m) reversed by seq_sub_perm,
   so no division and no Vandermonde enters. *)

Lemma nfold_rev_seq : forall (h : nat -> nat) (m : nat),
  fold_right (fun k acc => (h (m - k)%nat + acc)%nat) 0%nat (seq 0 (S m))
  = fold_right (fun k acc => (h k + acc)%nat) 0%nat (seq 0 (S m)).
Proof.
  intros h m.
  transitivity (fold_right (fun k acc => (h k + acc)%nat) 0%nat
                  (map (fun v => (m - v)%nat) (seq 0 (S m)))).
  - symmetry. apply (nfold_map nat h (fun v => (m - v)%nat) (seq 0 (S m))).
  - apply nfold_perm. apply seq_sub_perm.
Qed.

Lemma card132_0 : card132 0 = 1%nat.
Proof. reflexivity. Qed.

(* The convolution of the class with itself, weighted by w. *)
Definition wsum (w : nat -> nat) (m : nat) : nat :=
  fold_right (fun k acc => (w k * (card132 k * card132 (m - k)) + acc)%nat)
             0%nat (seq 0 (S m)).

Lemma wsum_ext : forall w1 w2 m,
  (forall k, (k <= m)%nat -> w1 k = w2 k) -> wsum w1 m = wsum w2 m.
Proof.
  intros w1 w2 m H. unfold wsum. apply nfold_ext_in.
  intros k Hk. apply in_seq in Hk. rewrite (H k ltac:(lia)). reflexivity.
Qed.

Lemma wsum_add : forall w1 w2 m,
  (wsum w1 m + wsum w2 m)%nat = wsum (fun k => (w1 k + w2 k)%nat) m.
Proof.
  intros w1 w2 m. unfold wsum. cbn beta.
  generalize (seq 0 (S m)) as l. intro l.
  induction l as [|a l IH]; cbn [fold_right]; [lia | rewrite <- IH; ring].
Qed.

Lemma wsum_scal : forall c w m,
  wsum (fun k => (c * w k)%nat) m = (c * wsum w m)%nat.
Proof.
  intros c w m. unfold wsum. cbn beta.
  generalize (seq 0 (S m)) as l. intro l.
  induction l as [|a l IH]; cbn [fold_right]; [lia | rewrite IH; ring].
Qed.

Lemma wsum_const : forall c m, wsum (fun _ => c) m = (c * card132 (S m))%nat.
Proof.
  intros c m. unfold wsum. cbn beta. rewrite (card132_convolution m).
  generalize (seq 0 (S m)) as l. intro l.
  induction l as [|a l IH]; cbn [fold_right]; [lia | rewrite IH; ring].
Qed.

(* Reversing the index carries the weight w to w o (m - .). *)
Lemma wsum_rev : forall w m, wsum w m = wsum (fun k => w (m - k)%nat) m.
Proof.
  intros w m. symmetry. unfold wsum. cbn beta.
  transitivity (fold_right (fun k acc =>
      ((fun t => (w t * (card132 t * card132 (m - t)))%nat) (m - k)%nat
       + acc)%nat) 0%nat (seq 0 (S m))).
  - apply nfold_ext_in. intros k Hk. apply in_seq in Hk. cbn beta.
    replace (m - (m - k))%nat with k by lia. ring.
  - apply (nfold_rev_seq (fun t => (w t * (card132 t * card132 (m - t)))%nat) m).
Qed.

(* The first reading: the weights k+1 and m-k+1 add to m+2 on every term. *)
Lemma wsum_S_sym : forall m, (2 * wsum S m = S (S m) * card132 (S m))%nat.
Proof.
  intro m.
  assert (A1 : wsum S m = wsum (fun k => S (m - k)%nat) m) by apply wsum_rev.
  assert (A2 : (wsum S m + wsum (fun k => S (m - k)%nat) m)%nat
             = wsum (fun k => (S k + S (m - k))%nat) m) by apply wsum_add.
  assert (A3 : wsum (fun k => (S k + S (m - k))%nat) m
             = wsum (fun _ => S (S m)) m)
    by (apply wsum_ext; intros k Hk; lia).
  rewrite wsum_const in A3. lia.
Qed.

(* The second reading: substituting the ratio at every k <= m collapses the
   weighted convolution to a multiple of card132 m. *)
Lemma wsum_S_ratio : forall m,
  (forall k, (k < m)%nat ->
     (S (S k) * card132 (S k) = 2 * (2 * k + 1) * card132 k)%nat) ->
  wsum S m = ((2 * m + 1) * card132 m)%nat.
Proof.
  intros m IH. destruct m as [|m']; [vm_compute; reflexivity|].
  assert (Hhead : wsum S (S m')
    = (card132 (S m') + wsum (fun j => (4 * j + 2)%nat) m')%nat).
  { unfold wsum. cbn beta.
    change (seq 0 (S (S m'))) with (0%nat :: seq 1 (S m')).
    cbn [fold_right].
    rewrite card132_0, Nat.sub_0_r.
    f_equal; [lia|].
    rewrite <- (seq_shift (S m') 0).
    transitivity (fold_right (fun j acc =>
        ((fun k => (S k * (card132 k * card132 (S m' - k)))%nat) (S j)
         + acc)%nat) 0%nat (seq 0 (S m'))).
    - apply (nfold_map nat
        (fun k => (S k * (card132 k * card132 (S m' - k)))%nat) S
        (seq 0 (S m'))).
    - apply nfold_ext_in. intros j Hj. apply in_seq in Hj. cbn beta.
      replace (S m' - S j)%nat with (m' - j)%nat by lia.
      assert (E := IH j ltac:(lia)).
      transitivity ((S (S j) * card132 (S j)) * card132 (m' - j))%nat;
        [ring | rewrite E; ring]. }
  assert (Hsplit : wsum (fun j => (4 * j + 2)%nat) m'
    = (wsum (fun j => (4 * j)%nat) m' + wsum (fun _ => 2%nat) m')%nat).
  { rewrite wsum_add. apply wsum_ext. intros k _. cbn beta. lia. }
  rewrite wsum_const in Hsplit.
  assert (Hscal := wsum_scal 4%nat (fun j => j) m'). cbn beta in Hscal.
  assert (HU : (2 * wsum (fun j => j) m')%nat = (m' * card132 (S m'))%nat).
  { assert (A1 : wsum (fun j => j) m' = wsum (fun j => (m' - j)%nat) m')
      by apply wsum_rev.
    assert (A2 : (wsum (fun j => j) m' + wsum (fun j => (m' - j)%nat) m')%nat
               = wsum (fun j => (j + (m' - j))%nat) m') by apply wsum_add.
    assert (A3 : wsum (fun j => (j + (m' - j))%nat) m' = wsum (fun _ => m') m')
      by (apply wsum_ext; intros k Hk; lia).
    rewrite wsum_const in A3. lia. }
  replace ((2 * S m' + 1) * card132 (S m'))%nat
    with ((2 * (m' * card132 (S m')) + 3 * card132 (S m'))%nat) by ring.
  lia.
Qed.

Lemma card132_ratio_upto : forall n m, (m <= n)%nat ->
  (S (S m) * card132 (S m) = 2 * (2 * m + 1) * card132 m)%nat.
Proof.
  induction n as [|n IHn]; intros m Hm.
  - assert (E : m = 0%nat) by lia. subst m. vm_compute. reflexivity.
  - destruct (le_lt_dec m n) as [Hle|Hlt]; [apply IHn; exact Hle|].
    assert (Em : m = S n) by lia. subst m.
    assert (IH : forall k, (k < S n)%nat ->
      (S (S k) * card132 (S k) = 2 * (2 * k + 1) * card132 k)%nat)
      by (intros k Hk; apply IHn; lia).
    assert (A := wsum_S_sym (S n)).
    rewrite (wsum_S_ratio (S n) IH) in A.
    rewrite <- A. ring.
Qed.

(* The class obeys the central binomial ratio. *)
Theorem card132_ratio : CARD132_RATIO.
Proof. intro m. apply (card132_ratio_upto m m). lia. Qed.

(* and hence the closed count, unconditionally *)
Corollary card132_binom : forall m, (S m * card132 m)%nat = binomN (2 * m) m.
Proof. apply card132_binom_of_ratio. exact card132_ratio. Qed.

(* With Ddiag_one this is the d = 1 column of the two-term law outright. *)
Corollary Ddiag_one_binom : forall M, Ddiag 1 M = binomN (2 * M) M.
Proof. intro M. rewrite Ddiag_one. apply card132_binom. Qed.

(* The other cell class of the staircase, carried across by rc.  Av(213) is the
   image of Av(132) under an involution, so it is enumerated, duplicate-free and
   Catalan for the same reason. *)

Definition gen213 (m : nat) : list (list nat) := map (rc m) (gen132 m).

Theorem gen213_spec : forall m w,
  In w (gen213 m) <-> (is_perm w m /\ ~ contains_213 w).
Proof.
  intros m w. unfold gen213. split.
  - intro H. apply in_map_iff in H. destruct H as [u [Hu Huin]].
    apply gen132_spec in Huin. destruct Huin as [Hp H132]. subst w.
    split; [apply rc_perm; exact Hp|].
    apply (rc_avoid_213 m u (proj2 (proj2 Hp))). exact H132.
  - intros [Hp H213]. apply in_map_iff. exists (rc m w). split.
    + apply rc_involutive. exact (proj2 (proj2 Hp)).
    + apply gen132_spec. split; [apply rc_perm; exact Hp|].
      apply (rc_avoid_213 m (rc m w) (rc_bound m w (proj2 (proj2 Hp)))).
      rewrite (rc_involutive m w (proj2 (proj2 Hp))). exact H213.
Qed.

Theorem gen213_nodup : forall m, NoDup (gen213 m).
Proof.
  intro m. unfold gen213. apply NoDup_map_inj; [apply gen132_nodup|].
  intros x y Hx Hy He.
  apply gen132_spec in Hx. apply gen132_spec in Hy.
  rewrite <- (rc_involutive m x (proj2 (proj2 (proj1 Hx)))).
  rewrite <- (rc_involutive m y (proj2 (proj2 (proj1 Hy)))).
  rewrite He. reflexivity.
Qed.

Definition card213 (m : nat) : nat := length (gen213 m).

Theorem card213_card132 : forall m, card213 m = card132 m.
Proof. intro m. unfold card213, gen213, card132. apply len_map_gen. Qed.

Corollary card213_binom : forall m, (S m * card213 m)%nat = binomN (2 * m) m.
Proof. intro m. rewrite card213_card132. apply card132_binom. Qed.

(* ------------------------------------------------------------------ *)
(* Interleaving two cells.  A mask says which positions carry the upper cell;
   mrg plants the two words into it, and filtering by value recovers them.
   Masks of length n with a true entries number binomN n a, so an interleaving
   count is a binomial times the two cell counts. *)

Fixpoint countt (P : list bool) : nat :=
  match P with
  | nil => 0%nat
  | true :: r => S (countt r)
  | false :: r => countt r
  end.

Lemma countt_le : forall P, (countt P <= length P)%nat.
Proof.
  induction P as [|x P IH]; cbn [countt length]; [lia|].
  destruct x; lia.
Qed.

Lemma countt_map : forall (t : nat -> bool) (w : list nat),
  countt (map t w) = length (filter t w).
Proof.
  intros t w. induction w as [|x w IH]; [reflexivity|].
  simpl. destruct (t x); simpl; rewrite IH; reflexivity.
Qed.

Fixpoint bwords (n a : nat) : list (list bool) :=
  match n with
  | 0%nat => match a with 0%nat => (nil : list bool) :: nil | S _ => nil end
  | S n' => match a with
            | 0%nat => map (cons false) (bwords n' 0%nat)
            | S a' => map (cons true) (bwords n' a')
                      ++ map (cons false) (bwords n' (S a'))
            end
  end.

Lemma binomN_0 : forall n, binomN n 0 = 1%nat.
Proof. destruct n; reflexivity. Qed.

Theorem bwords_length : forall n a, length (bwords n a) = binomN n a.
Proof.
  induction n as [|n IH]; intro a.
  - destruct a; reflexivity.
  - destruct a as [|a].
    + change (bwords (S n) 0%nat) with (map (cons false) (bwords n 0%nat)).
      rewrite len_map_gen, (IH 0%nat), !binomN_0. reflexivity.
    + change (bwords (S n) (S a))
        with (map (cons true) (bwords n a) ++ map (cons false) (bwords n (S a))).
      change (binomN (S n) (S a)) with (binomN n a + binomN n (S a))%nat.
      rewrite len_app_gen, !len_map_gen, (IH a), (IH (S a)). reflexivity.
Qed.

Theorem bwords_spec : forall n a P,
  In P (bwords n a) <-> (length P = n /\ countt P = a).
Proof.
  induction n as [|n IH]; intros a P.
  - destruct a as [|a]; cbn [bwords].
    + split.
      * intros [He | []]. subst P. split; reflexivity.
      * intros [Hl _]. destruct P as [|x P]; [left; reflexivity|].
        cbn [length] in Hl. discriminate.
    + split; [contradiction|].
      intros [Hl Hc]. destruct P as [|x P]; [cbn [countt] in Hc; discriminate|].
      cbn [length] in Hl. discriminate.
  - destruct a as [|a].
    + change (bwords (S n) 0%nat) with (map (cons false) (bwords n 0%nat)).
      split.
      * intro H. apply in_map_iff in H. destruct H as [Q [HQ Hin]].
        apply IH in Hin. destruct Hin as [Hl Hc]. subst P.
        cbn [length countt]. split; [lia | exact Hc].
      * intros [Hl Hc]. destruct P as [|x P]; [cbn [length] in Hl; discriminate|].
        destruct x; [cbn [countt] in Hc; discriminate|].
        apply in_map_iff. exists P. split; [reflexivity|].
        apply IH. cbn [length countt] in Hl, Hc. split; [lia | exact Hc].
    + change (bwords (S n) (S a))
        with (map (cons true) (bwords n a) ++ map (cons false) (bwords n (S a))).
      split.
      * intro H. apply in_app_or in H. destruct H as [H | H];
          apply in_map_iff in H; destruct H as [Q [HQ Hin]]; apply IH in Hin;
          destruct Hin as [Hl Hc]; subst P; cbn [length countt];
          split; lia.
      * intros [Hl Hc]. destruct P as [|x P]; [cbn [length] in Hl; discriminate|].
        cbn [length countt] in Hl, Hc.
        apply in_or_app. destruct x.
        -- left. apply in_map_iff. exists P. split; [reflexivity|].
           apply IH. split; lia.
        -- right. apply in_map_iff. exists P. split; [reflexivity|].
           apply IH. split; lia.
Qed.

Theorem bwords_nodup : forall n a, NoDup (bwords n a).
Proof.
  induction n as [|n IH]; intro a.
  - destruct a; cbn [bwords];
      [constructor; [intros [] | constructor] | constructor].
  - destruct a as [|a].
    + change (bwords (S n) 0%nat) with (map (cons false) (bwords n 0%nat)).
      apply NoDup_map_inj; [apply IH|].
      intros x y _ _ He. injection He as He. exact He.
    + change (bwords (S n) (S a))
        with (map (cons true) (bwords n a) ++ map (cons false) (bwords n (S a))).
      apply NoDup_app_disj.
      * apply NoDup_map_inj; [apply IH|].
        intros x y _ _ He. injection He as He. exact He.
      * apply NoDup_map_inj; [apply IH|].
        intros x y _ _ He. injection He as He. exact He.
      * intros p Hp Hq.
        apply in_map_iff in Hp. destruct Hp as [x [Hx _]].
        apply in_map_iff in Hq. destruct Hq as [y [Hy _]].
        subst p. discriminate.
Qed.

(* Planting the two words into the mask. *)
Fixpoint mrg (P : list bool) (hi lo : list nat) : list nat :=
  match P with
  | nil => nil
  | true :: P' => match hi with
                  | nil => nil
                  | x :: hi' => x :: mrg P' hi' lo
                  end
  | false :: P' => match lo with
                   | nil => nil
                   | y :: lo' => y :: mrg P' hi lo'
                   end
  end.

(* Under matching lengths and a test separating the two cells, the merge is
   recovered by filtering, and the mask by mapping the test. *)
Lemma mrg_spec : forall (t : nat -> bool) P hi lo,
  length hi = countt P ->
  length lo = (length P - countt P)%nat ->
  (forall x, In x hi -> t x = true) ->
  (forall y, In y lo -> t y = false) ->
  filter t (mrg P hi lo) = hi
  /\ filter (fun x => negb (t x)) (mrg P hi lo) = lo
  /\ map t (mrg P hi lo) = P.
Proof.
  intros t P. induction P as [|x P IH]; intros hi lo H1 H2 Ht Hf.
  - cbn [countt length] in H1, H2.
    destruct hi as [|h hi]; [|cbn [length] in H1; discriminate].
    destruct lo as [|l lo]; [|cbn [length] in H2; discriminate].
    cbn [mrg filter map]. repeat split; reflexivity.
  - destruct x.
    + cbn [countt] in H1, H2.
      destruct hi as [|h hi]; [cbn [length] in H1; discriminate|].
      cbn [length] in H1.
      assert (Hh : t h = true) by (apply Ht; left; reflexivity).
      assert (K1 : length hi = countt P) by lia.
      assert (K2 : length lo = (length P - countt P)%nat)
        by (cbn [length] in H2; lia).
      destruct (IH hi lo K1 K2
                   ltac:(intros z Hz; apply Ht; right; exact Hz) Hf)
        as [E1 [E2 E3]].
      cbn [mrg filter map]. rewrite Hh. cbn [negb].
      rewrite E1, E2, E3. repeat split; reflexivity.
    + cbn [countt] in H1, H2.
      assert (Hcl := countt_le P).
      destruct lo as [|l lo]; [cbn [length] in H2; lia|].
      cbn [length] in H2.
      assert (Hl : t l = false) by (apply Hf; left; reflexivity).
      assert (K2 : length lo = (length P - countt P)%nat) by lia.
      destruct (IH hi lo H1 K2 Ht
                   ltac:(intros z Hz; apply Hf; right; exact Hz))
        as [E1 [E2 E3]].
      cbn [mrg filter map]. rewrite Hl. cbn [negb].
      rewrite E1, E2, E3. repeat split; reflexivity.
Qed.

(* Splitting any word by the test and replanting returns it. *)
Lemma mrg_split : forall (t : nat -> bool) (w : list nat),
  mrg (map t w) (filter t w) (filter (fun x => negb (t x)) w) = w.
Proof.
  intros t w. induction w as [|x w IH]; [reflexivity|].
  simpl. destruct (t x); simpl; rewrite IH; reflexivity.
Qed.

Lemma perm_filter_split : forall (t : nat -> bool) (w : list nat),
  Permutation w (filter t w ++ filter (fun x => negb (t x)) w).
Proof.
  intros t w. induction w as [|x w IH]; simpl; [apply Permutation_refl|].
  destruct (t x); simpl.
  - apply perm_skip. exact IH.
  - eapply Permutation_trans;
      [apply perm_skip; exact IH | apply Permutation_middle].
Qed.

Lemma negb_leb_ltb : forall b x, negb (Nat.leb b x) = Nat.ltb x b.
Proof. intros b x. natb. Qed.

Lemma length_list_prod : forall (A B : Type) (l1 : list A) (l2 : list B),
  length (list_prod l1 l2) = (length l1 * length l2)%nat.
Proof.
  intros A B. induction l1 as [|a l1 IH]; intro l2; cbn [list_prod];
    [reflexivity|].
  rewrite len_app_gen, len_map_gen, IH. reflexivity.
Qed.

Lemma NoDup_list_prod : forall (A B : Type) (l1 : list A) (l2 : list B),
  NoDup l1 -> NoDup l2 -> NoDup (list_prod l1 l2).
Proof.
  intros A B l1 l2 H1 H2. induction l1 as [|a l1 IH]; cbn [list_prod];
    [constructor|].
  inversion H1 as [|x xs Hax Hl1]; subst.
  apply NoDup_app_disj.
  - apply NoDup_map_inj; [exact H2|].
    intros x y _ _ He. injection He as He. exact He.
  - apply IH. exact Hl1.
  - intros p Hp Hq. apply in_map_iff in Hp. destruct Hp as [y [Hy _]].
    subst p. apply in_prod_iff in Hq. destruct Hq as [Ha _]. contradiction.
Qed.

(* Facts about the decreasing pattern, as a cell. *)

Lemma decpat_bound : forall b x, In x (decpat b) -> (x < b)%nat.
Proof.
  intros b x H. unfold decpat in H. apply in_map_iff in H.
  destruct H as [t [Ht Hin]]. apply in_seq in Hin. lia.
Qed.

Lemma decpat_nodup : forall b, NoDup (decpat b).
Proof.
  intro b. unfold decpat. apply NoDup_map_inj; [apply seq_NoDup|].
  intros x y Hx Hy He. apply in_seq in Hx. apply in_seq in Hy. lia.
Qed.

Lemma decpat_is_perm : forall b, is_perm (decpat b) b.
Proof.
  intro b. split; [apply decpat_length | split;
    [apply decpat_nodup | apply decpat_bound]].
Qed.

#[export] Hint Resolve decpat_length decpat_nodup decpat_bound decpat_is_perm
  decpat_avoids_132 : av1324.

Lemma contains_213_addc : forall c l,
  contains_213 (map (fun x => (x + c)%nat) l) <-> contains_213 l.
Proof.
  intros c l. split; intros [i [j [k H]]]; unfold has_213_at in H;
    destruct H as [Hij [Hjk [Hk [H1 H2]]]]; exists i, j, k; unfold has_213_at.
  - rewrite len_map_add in Hk.
    assert (Ai : (i < length l)%nat) by lia.
    assert (Aj : (j < length l)%nat) by lia.
    assert (Ak : (k < length l)%nat) by lia.
    rewrite (nth_map_add c l i Ai) in H1, H2.
    rewrite (nth_map_add c l j Aj) in H1.
    rewrite (nth_map_add c l k Ak) in H2.
    repeat split; lia.
  - rewrite len_map_add.
    rewrite (nth_map_add c l i ltac:(lia)), (nth_map_add c l j ltac:(lia)),
            (nth_map_add c l k ltac:(lia)).
    repeat split; lia.
Qed.

Lemma map_sub_add : forall b (l : list nat),
  (forall x, In x l -> (b <= x)%nat) ->
  map (fun x => ((x - b) + b)%nat) l = l.
Proof.
  intros b l H. rewrite <- (map_id l) at 2. apply map_ext_in.
  intros a Ha. specialize (H a Ha). lia.
Qed.

(* The decreasing lower cell, counted.  By dec_cell_iff the domino condition
   over that cell is exactly "the upper cell avoids 213", so a domino there is a
   choice of which a of the a+b positions carry the upper cell together with the
   213-avoiding pattern it takes, and nothing else.  That makes d_A a free
   product, C(a+b,a) times the Catalan number, rather than a fitted value. *)

Lemma decdom_spec : forall a b P h,
  In P (bwords (a + b) a) -> In h (gen213 a) ->
  is_perm (mrg P (map (fun x => (x + b)%nat) h) (decpat b)) (a + b)
  /\ locell b (mrg P (map (fun x => (x + b)%nat) h) (decpat b)) = decpat b
  /\ hicell b (mrg P (map (fun x => (x + b)%nat) h) (decpat b))
     = map (fun x => (x + b)%nat) h
  /\ map (fun x => Nat.leb b x)
         (mrg P (map (fun x => (x + b)%nat) h) (decpat b)) = P.
Proof.
  intros a b P h HP Hh.
  apply bwords_spec in HP. destruct HP as [HPlen HPcnt].
  apply gen213_spec in Hh. destruct Hh as [Hhp Hh213].
  assert (Hhlen : length h = a) by av.
  assert (Hhnd : NoDup h) by av.
  assert (Hhb : forall x, In x h -> (x < a)%nat)
    by av.
  assert (Hhilen : length (map (fun x => (x + b)%nat) h) = a)
    by (rewrite len_map_add; exact Hhlen).
  assert (Hhihigh : forall x, In x (map (fun x => (x + b)%nat) h) ->
                    Nat.leb b x = true).
  { intros x Hx. apply in_map_iff in Hx. destruct Hx as [y [Hy _]].
    destruct (Nat.leb_spec b x); [reflexivity | exfalso; lia]. }
  assert (Hlolow : forall y, In y (decpat b) -> Nat.leb b y = false).
  { intros y Hy. assert (Hy2 := decpat_bound b y Hy).
    destruct (Nat.leb_spec b y); [exfalso; lia | reflexivity]. }
  assert (K1 : length (map (fun x => (x + b)%nat) h) = countt P)
    by (rewrite Hhilen, HPcnt; reflexivity).
  assert (K2 : length (decpat b) = (length P - countt P)%nat)
    by (rewrite decpat_length, HPlen, HPcnt; lia).
  destruct (mrg_spec (fun x => Nat.leb b x) P
              (map (fun x => (x + b)%nat) h) (decpat b) K1 K2 Hhihigh Hlolow)
    as [Ehi [Elo Emask]].
  set (w := mrg P (map (fun x => (x + b)%nat) h) (decpat b)) in *.
  assert (Hwlen : length w = (a + b)%nat).
  { rewrite <- HPlen, <- Emask. symmetry. apply len_map_gen. }
  assert (Hperm : Permutation w (map (fun x => (x + b)%nat) h ++ decpat b)).
  { assert (Q := perm_filter_split (fun x => Nat.leb b x) w).
    cbn beta in Q. rewrite Ehi, Elo in Q. exact Q. }
  assert (Hnd : NoDup w).
  { apply (Permutation_NoDup (Permutation_sym Hperm)).
    apply NoDup_app_disj.
    - apply NoDup_map_inj; [exact Hhnd|]. intros x y _ _ He. lia.
    - apply decpat_nodup.
    - intros z Hz1 Hz2.
      assert (Hb1 : Nat.leb b z = true) by (apply Hhihigh; exact Hz1).
      assert (Hb2 : Nat.leb b z = false) by (apply Hlolow; exact Hz2).
      rewrite Hb1 in Hb2. discriminate. }
  assert (Hbound : forall x, In x w -> (x < a + b)%nat).
  { intros x Hx.
    assert (Hx2 : In x (map (fun x => (x + b)%nat) h ++ decpat b))
      by (apply (Permutation_in _ Hperm); exact Hx).
    apply in_app_or in Hx2. destruct Hx2 as [Hx2 | Hx2].
    - apply in_map_iff in Hx2. destruct Hx2 as [y [Hy Hyin]].
      assert (Hy2 := Hhb y Hyin). lia.
    - assert (Hy2 := decpat_bound b x Hx2). lia. }
  split; [| split; [| split]].
  - split; [exact Hwlen | split; [exact Hnd | exact Hbound]].
  - unfold locell. rewrite <- Elo. apply filter_ext_gen.
    intro x. symmetry. apply negb_leb_ltb.
  - unfold hicell. exact Ehi.
  - exact Emask.
Qed.

Lemma decdom_in_dominoes : forall a b P h,
  In P (bwords (a + b) a) -> In h (gen213 a) ->
  In (mrg P (map (fun x => (x + b)%nat) h) (decpat b)) (dominoes a b).
Proof.
  intros a b P h HP Hh.
  assert (Hh' := Hh). apply gen213_spec in Hh'. destruct Hh' as [_ Hh213].
  destruct (decdom_spec a b P h HP Hh) as [Hp [Hlo [Hhi _]]].
  apply (dec_cell_domino a b _ Hp Hlo).
  rewrite Hhi. intro C. apply Hh213. apply (contains_213_addc b h). exact C.
Qed.

Lemma dec_cell_recover : forall a b w,
  In w (dominoes a b) -> locell b w = decpat b ->
  exists P h, In P (bwords (a + b) a) /\ In h (gen213 a) /\
              w = mrg P (map (fun x => (x + b)%nat) h) (decpat b).
Proof.
  intros a b w Hw Hlo.
  apply dominoes_spec in Hw. destruct Hw as [Hp [_ [_ H213]]].
  assert (Hwlen : length w = (a + b)%nat) by av.
  assert (Hwnd : NoDup w) by av.
  assert (Hwb : forall x, In x w -> (x < a + b)%nat)
    by av.
  assert (Elo : filter (fun x => negb (Nat.leb b x)) w = decpat b).
  { rewrite <- Hlo. unfold locell. apply filter_ext_gen.
    intro x. apply negb_leb_ltb. }
  assert (Hperm : Permutation w (filter (fun x => Nat.leb b x) w ++ decpat b)).
  { assert (Q := perm_filter_split (fun x => Nat.leb b x) w).
    cbn beta in Q. rewrite Elo in Q. exact Q. }
  assert (Hhilen : length (filter (fun x => Nat.leb b x) w) = a).
  { assert (L := Permutation_length Hperm).
    rewrite len_app, decpat_length, Hwlen in L. lia. }
  assert (Hhihigh : forall x, In x (filter (fun x => Nat.leb b x) w) ->
                    (b <= x)%nat).
  { intros x Hx. apply filter_In in Hx. destruct Hx as [_ Hx].
    destruct (Nat.leb_spec b x); [assumption | discriminate]. }
  set (h := map (fun x => (x - b)%nat) (filter (fun x => Nat.leb b x) w)).
  assert (Ehi2 : map (fun x => (x + b)%nat) h
                 = filter (fun x => Nat.leb b x) w).
  { unfold h. rewrite map_map. apply map_sub_add. exact Hhihigh. }
  exists (map (fun x => Nat.leb b x) w), h.
  split; [| split].
  - apply bwords_spec. split.
    + rewrite len_map_gen. exact Hwlen.
    + rewrite countt_map. exact Hhilen.
  - apply gen213_spec. split.
    + split; [| split].
      * unfold h. rewrite len_map_gen. exact Hhilen.
      * unfold h. apply NoDup_map_inj.
        -- apply NoDup_filter. exact Hwnd.
        -- intros x y Hx Hy He.
           assert (Bx := Hhihigh x Hx). assert (By := Hhihigh y Hy). lia.
      * intros x Hx. unfold h in Hx. apply in_map_iff in Hx.
        destruct Hx as [y [Hy Hyin]].
        assert (By := Hhihigh y Hyin).
        assert (Cy : In y w) by (apply filter_In in Hyin; tauto).
        assert (Dy := Hwb y Cy). lia.
    + intro C. apply H213.
      assert (E : hicell b w = map (fun x => (x + b)%nat) h)
        by (unfold hicell; symmetry; exact Ehi2).
      rewrite E. apply (contains_213_addc b h). exact C.
  - rewrite Ehi2, <- Elo. symmetry. apply mrg_split.
Qed.

Theorem dA_dec : forall a b,
  dA a b (decpat b) = (binomN (a + b) a * card213 a)%nat.
Proof.
  intros a b. unfold dA.
  set (L2 := map (fun p => mrg (fst p) (map (fun x => (x + b)%nat) (snd p))
                               (decpat b))
                 (list_prod (bwords (a + b) a) (gen213 a))).
  assert (HL2 : length L2 = (binomN (a + b) a * card213 a)%nat).
  { unfold L2. rewrite len_map_gen, length_list_prod, bwords_length.
    reflexivity. }
  rewrite <- HL2.
  apply Nat.le_antisymm.
  - apply NoDup_incl_length.
    + apply NoDup_filter. apply dominoes_nodup.
    + intros w Hw. apply filter_In in Hw. destruct Hw as [Hw He].
      destruct (list_eq_dec Nat.eq_dec (locell b w) (decpat b)) as [E|E];
        [| discriminate].
      destruct (dec_cell_recover a b w Hw E) as [P [h [HP [Hh Hwe]]]].
      unfold L2. apply in_map_iff. exists (P, h). split.
      * cbn [fst snd]. symmetry. exact Hwe.
      * apply in_prod; assumption.
  - apply NoDup_incl_length.
    + unfold L2. apply NoDup_map_inj.
      * apply NoDup_list_prod; [apply bwords_nodup | apply gen213_nodup].
      * intros p q Hp Hq He. cbn beta in He.
        destruct p as [P1 h1]; destruct q as [P2 h2]. cbn [fst snd] in He.
        apply in_prod_iff in Hp. destruct Hp as [HP1 Hh1].
        apply in_prod_iff in Hq. destruct Hq as [HP2 Hh2].
        destruct (decdom_spec a b P1 h1 HP1 Hh1) as [_ [_ [Eh1 Em1]]].
        destruct (decdom_spec a b P2 h2 HP2 Hh2) as [_ [_ [Eh2 Em2]]].
        assert (EP : P1 = P2) by (rewrite <- Em1, <- Em2, He; reflexivity).
        assert (Eh : h1 = h2).
        { apply (map_add_inj b). rewrite <- Eh1, <- Eh2, He. reflexivity. }
        subst. reflexivity.
    + intros z Hz. unfold L2 in Hz. apply in_map_iff in Hz.
      destruct Hz as [p [Hpz Hpin]]. destruct p as [P h].
      cbn [fst snd] in Hpz. subst z.
      apply in_prod_iff in Hpin. destruct Hpin as [HP Hh].
      apply filter_In. split.
      * apply decdom_in_dominoes; assumption.
      * destruct (decdom_spec a b P h HP Hh) as [_ [Hlo _]].
        destruct (list_eq_dec Nat.eq_dec
                    (locell b (mrg P (map (fun x => (x + b)%nat) h) (decpat b)))
                    (decpat b)) as [E|E]; [reflexivity | contradiction].
Qed.

(* and in Catalan form, since card213 a = card132 a and (a+1) card132 a = C(2a,a) *)
Corollary dA_dec_catalan : forall a b,
  (S a * dA a b (decpat b))%nat
  = (binomN (a + b) a * binomN (2 * a) a)%nat.
Proof.
  intros a b. rewrite dA_dec, <- card213_binom. ring.
Qed.

Lemma locell_as_negb : forall b u,
  locell b u = filter (fun x => negb (Nat.leb b x)) u.
Proof.
  intros b u. unfold locell. apply filter_ext_gen.
  intro x. symmetry. apply negb_leb_ltb.
Qed.

(* A word is determined by its mask and its two cells: mrg_split replants it
   from exactly those three, so every injectivity argument over a value cut is
   this one lemma. *)
Lemma cell_reconstruct : forall b x y,
  map (fun z => Nat.leb b z) x = map (fun z => Nat.leb b z) y ->
  hicell b x = hicell b y ->
  locell b x = locell b y ->
  x = y.
Proof.
  intros b x y Hm Hh Hl.
  assert (Gx := mrg_split (fun z => Nat.leb b z) x).
  assert (Gy := mrg_split (fun z => Nat.leb b z) y).
  cbn beta in Gx, Gy.
  assert (Fx : filter (fun z => negb (Nat.leb b z)) x = locell b x)
    by (symmetry; apply locell_as_negb).
  assert (Fy : filter (fun z => negb (Nat.leb b z)) y = locell b y)
    by (symmetry; apply locell_as_negb).
  rewrite Fx in Gx. rewrite Fy in Gy.
  change (filter (fun z => Nat.leb b z) x) with (hicell b x) in Gx.
  change (filter (fun z => Nat.leb b z) y) with (hicell b y) in Gy.
  rewrite <- Gx, <- Gy, Hm, Hh, Hl. reflexivity.
Qed.

Ltac cells b := apply (cell_reconstruct b); congruence.

Lemma hicell_perm_length : forall n b u, is_perm u n -> (b <= n)%nat ->
  length (hicell b u) = (n - b)%nat.
Proof.
  intros n b u Hp Hb. unfold hicell.
  apply (count_ge_in_perm u n b Hp Hb).
Qed.

(* The decreasing lower cell is the largest fibre of d_A.  Replacing the lower
   cell of a domino by the decreasing pattern, keeping its positions and its
   upper cell, lands in the class again: by dec_cell_domino nothing is left to
   check but the 213 condition on the upper cell, which is untouched.  The map
   is injective on each fibre because the mask and the upper cell are recovered
   from the image and the lower pattern is fixed along the fibre. *)

Definition flatlo (b : nat) (w : list nat) : list nat :=
  mrg (map (fun x => Nat.leb b x) w) (hicell b w) (decpat b).

Lemma flatlo_spec : forall a b w,
  In w (dominoes a b) ->
  locell b (flatlo b w) = decpat b
  /\ hicell b (flatlo b w) = hicell b w
  /\ map (fun x => Nat.leb b x) (flatlo b w) = map (fun x => Nat.leb b x) w.
Proof.
  intros a b w Hw. apply dominoes_spec in Hw. destruct Hw as [Hp _].
  assert (Hhi : length (hicell b w) = a).
  { rewrite (hicell_perm_length (a + b) b w Hp ltac:(lia)). lia. }
  assert (Hcnt : countt (map (fun x => Nat.leb b x) w) = a)
    by (rewrite countt_map; exact Hhi).
  assert (Hlen : length (map (fun x => Nat.leb b x) w) = (a + b)%nat)
    by (rewrite len_map_gen; destruct Hp as [K _]; exact K).
  assert (H1 : length (hicell b w) = countt (map (fun x => Nat.leb b x) w))
    by (rewrite Hhi, Hcnt; reflexivity).
  assert (H2 : length (decpat b)
               = (length (map (fun x => Nat.leb b x) w)
                  - countt (map (fun x => Nat.leb b x) w))%nat)
    by (rewrite decpat_length, Hlen, Hcnt; lia).
  assert (Hhib : forall x, In x (hicell b w) -> Nat.leb b x = true).
  { intros x Hx. unfold hicell in Hx. apply filter_In in Hx.
    exact (proj2 Hx). }
  assert (Hlob : forall y, In y (decpat b) -> Nat.leb b y = false).
  { intros y Hy. assert (K := decpat_bound b y Hy).
    destruct (Nat.leb_spec b y); [exfalso; lia | reflexivity]. }
  destruct (mrg_spec (fun x => Nat.leb b x) (map (fun x => Nat.leb b x) w)
              (hicell b w) (decpat b) H1 H2 Hhib Hlob) as [Ehi [Elo Emask]].
  unfold flatlo.
  split; [| split; [exact Ehi | exact Emask]].
  rewrite locell_as_negb. exact Elo.
Qed.

Lemma flatlo_in : forall a b w,
  In w (dominoes a b) -> In (flatlo b w) (dominoes a b).
Proof.
  intros a b w Hw. assert (Hw' := Hw). apply dominoes_spec in Hw'.
  destruct Hw' as [Hp [_ [_ H213]]].
  destruct (flatlo_spec a b w Hw) as [Elo [Ehi Emask]].
  assert (Hip : is_perm (flatlo b w) (a + b)).
  { assert (Hperm : Permutation (flatlo b w) (hicell b w ++ decpat b)).
    { assert (Q := perm_filter_split (fun x => Nat.leb b x) (flatlo b w)).
      cbn beta in Q.
      assert (K1 : filter (fun x => Nat.leb b x) (flatlo b w) = hicell b w)
        by exact Ehi.
      assert (K2 : filter (fun x => negb (Nat.leb b x)) (flatlo b w)
                   = decpat b) by (rewrite <- locell_as_negb; exact Elo).
      rewrite K1, K2 in Q. exact Q. }
    assert (Hlw : length (flatlo b w) = (a + b)%nat).
    { rewrite <- (len_map_gen _ _ (fun x => Nat.leb b x)), Emask,
              len_map_gen. destruct Hp as [K _]. exact K. }
    split; [exact Hlw | split].
    - apply (Permutation_NoDup (Permutation_sym Hperm)).
      apply NoDup_app_disj.
      + unfold hicell. apply NoDup_filter. destruct Hp as [_ [K _]]. exact K.
      + apply decpat_nodup.
      + intros z Hz1 Hz2.
        assert (K1 : (b <= z)%nat).
        { unfold hicell in Hz1. apply filter_In in Hz1.
          apply Nat.leb_le. exact (proj2 Hz1). }
        assert (K2 := decpat_bound b z Hz2). lia.
    - intros x Hx.
      assert (K : In x (hicell b w ++ decpat b))
        by (apply (Permutation_in _ Hperm); exact Hx).
      apply in_app_or in K. destruct K as [K|K].
      + unfold hicell in K. apply filter_In in K.
        destruct Hp as [_ [_ Hb]]. apply Hb. exact (proj1 K).
      + assert (Q := decpat_bound b x K). lia. }
  apply (dec_cell_domino a b _ Hip Elo). rewrite Ehi. exact H213.
Qed.

Theorem dA_le_dec : forall a b l, (dA a b l <= dA a b (decpat b))%nat.
Proof.
  intros a b l. unfold dA.
  rewrite <- (len_map_gen _ _ (flatlo b)
    (filter (fun w => if list_eq_dec Nat.eq_dec (locell b w) l
                      then true else false) (dominoes a b))).
  apply NoDup_incl_length.
  - apply NoDup_map_inj.
    + apply NoDup_filter. apply dominoes_nodup.
    + intros x y Hx Hy He.
      apply filter_In in Hx. destruct Hx as [Hxd Hxl].
      apply filter_In in Hy. destruct Hy as [Hyd Hyl].
      destruct (list_eq_dec Nat.eq_dec (locell b x) l) as [Ex|]; [|discriminate].
      destruct (list_eq_dec Nat.eq_dec (locell b y) l) as [Ey|]; [|discriminate].
      destruct (flatlo_spec a b x Hxd) as [_ [Ehx Emx]].
      destruct (flatlo_spec a b y Hyd) as [_ [Ehy Emy]].
      assert (Ehi : hicell b x = hicell b y)
        by (rewrite <- Ehx, <- Ehy, He; reflexivity).
      assert (Ema : map (fun z => Nat.leb b z) x = map (fun z => Nat.leb b z) y)
        by (rewrite <- Emx, <- Emy, He; reflexivity).
      cells b.
  - intros z Hz. apply in_map_iff in Hz. destruct Hz as [w [Hwz Hwin]].
    subst z. apply filter_In in Hwin. destruct Hwin as [Hwd _].
    apply filter_In. split; [apply flatlo_in; exact Hwd|].
    destruct (flatlo_spec a b w Hwd) as [Elo _].
    destruct (list_eq_dec Nat.eq_dec (locell b (flatlo b w)) (decpat b));
      [reflexivity | contradiction].
Qed.

(* so every cell is bounded by the free product *)
Corollary dA_le_free : forall a b l,
  (dA a b l <= binomN (a + b) a * card213 a)%nat.
Proof. intros a b l. rewrite <- dA_dec. apply dA_le_dec. Qed.

(* The decreasing cell is its own inverse, so the up-set it spans is closed
   under the involution. *)
Theorem decpat_pinv : forall b, pinv (decpat b) = decpat b.
Proof.
  intro b. apply (nth_ext (pinv (decpat b)) (decpat b) 0%nat 0%nat).
  - rewrite pinv_length. reflexivity.
  - intros v Hv. rewrite pinv_length, decpat_length in Hv.
    rewrite (pinv_nth (decpat b) v ltac:(rewrite decpat_length; exact Hv)).
    assert (Hp : (b - 1 - v < b)%nat) by lia.
    assert (E : nth (b - 1 - v)%nat (decpat b) 0%nat = v)
      by (rewrite (decpat_nth b (b - 1 - v)%nat Hp); lia).
    rewrite <- E at 1.
    rewrite (nth_idx (decpat b) (decpat_nodup b) (b - 1 - v)%nat
               ltac:(rewrite decpat_length; exact Hp)).
    rewrite (decpat_nth b v Hv). reflexivity.
Qed.

(* At a threshold whose up-set is closed under the involution, positive
   quadrant dependence is unconditional: the up-sets of one function are
   nested, so the intersection is the smaller one and the product of the two
   sizes is at most the length times it.  The top threshold is such a place,
   because the maximum of d_A sits at the decreasing cell and that cell is an
   involution; the tight case of PQD is therefore not where the difficulty is. *)

Lemma filter_ext_in_gen : forall (A : Type) (P Q : A -> bool) (l : list A),
  (forall x, In x l -> P x = Q x) -> filter P l = filter Q l.
Proof.
  intros A P Q l. induction l as [|a l IH]; intro H; cbn [filter]; [reflexivity|].
  rewrite (H a (or_introl eq_refl)).
  destruct (Q a); [f_equal|]; apply IH; intros x Hx; apply H; right; exact Hx.
Qed.

Lemma cntA_map_count : forall (A : Type) (f : A -> nat * nat) (l : list A) a,
  cntA a (map f l) = length (filter (fun x => Nat.ltb a (fst (f x))) l).
Proof.
  intros A f l a. induction l as [|x l IH]; cbn [map cntA filter]; [reflexivity|].
  unfold gtb1. destruct (Nat.ltb a (fst (f x))); cbn [length]; rewrite IH; lia.
Qed.

Lemma cntB_map_count : forall (A : Type) (f : A -> nat * nat) (l : list A) b,
  cntB b (map f l) = length (filter (fun x => Nat.ltb b (snd (f x))) l).
Proof.
  intros A f l b. induction l as [|x l IH]; cbn [map cntB filter]; [reflexivity|].
  unfold gtb1. destruct (Nat.ltb b (snd (f x))); cbn [length]; rewrite IH; lia.
Qed.

Lemma cnt2_map_count : forall (A : Type) (f : A -> nat * nat) (l : list A) a b,
  cnt2 a b (map f l)
  = length (filter (fun x => andb (Nat.ltb a (fst (f x)))
                                  (Nat.ltb b (snd (f x)))) l).
Proof.
  intros A f l a b. induction l as [|x l IH]; cbn [map cnt2 filter];
    [reflexivity|].
  unfold gtb1.
  destruct (Nat.ltb a (fst (f x))); destruct (Nat.ltb b (snd (f x)));
    cbn [andb length]; rewrite IH; lia.
Qed.

Lemma count_max_bound : forall (A : Type) (g : A -> nat) (l : list A) a b,
  (length (filter (fun x => Nat.ltb a (g x)) l)
   * length (filter (fun x => Nat.ltb b (g x)) l)
   <= length l * length (filter (fun x => Nat.ltb (Nat.max a b) (g x)) l))%nat.
Proof.
  intros A g l a b.
  assert (Ha := length_filter_le_gen A (fun x => Nat.ltb a (g x)) l).
  assert (Hb := length_filter_le_gen A (fun x => Nat.ltb b (g x)) l).
  destruct (Nat.le_ge_cases a b) as [H|H].
  - assert (E : Nat.max a b = b) by lia. rewrite E. nia.
  - assert (E : Nat.max a b = a) by lia. rewrite E. nia.
Qed.

Theorem pqd_diag_closed : forall m a b,
  (forall l, In l (gen132 m) ->
     ((b < dA m m (pinv l))%nat <-> (b < dA m m l)%nat)) ->
  (cntA a (diag_pairs m) * cntB b (diag_pairs m)
   <= length (diag_pairs m) * cnt2 a b (diag_pairs m))%nat.
Proof.
  intros m a b Hclosed. unfold diag_pairs.
  rewrite cntA_map_count, cntB_map_count, cnt2_map_count, len_map_gen.
  cbn [fst snd].
  assert (EB : filter (fun l => Nat.ltb b (dA m m (pinv l))) (gen132 m)
               = filter (fun l => Nat.ltb b (dA m m l)) (gen132 m)).
  { apply filter_ext_in_gen. intros l Hl.
    assert (K := Hclosed l Hl).
    destruct (Nat.ltb_spec b (dA m m (pinv l)));
      destruct (Nat.ltb_spec b (dA m m l));
      solve [reflexivity | exfalso; lia]. }
  assert (E2 : filter (fun l => andb (Nat.ltb a (dA m m l))
                                     (Nat.ltb b (dA m m (pinv l)))) (gen132 m)
               = filter (fun l => Nat.ltb (Nat.max a b) (dA m m l))
                        (gen132 m)).
  { apply filter_ext_in_gen. intros l Hl.
    assert (K := Hclosed l Hl).
    destruct (Nat.ltb_spec a (dA m m l));
      destruct (Nat.ltb_spec b (dA m m (pinv l)));
      destruct (Nat.ltb_spec (Nat.max a b) (dA m m l));
      solve [reflexivity | exfalso; lia]. }
  rewrite EB, E2.
  apply (count_max_bound (list nat) (fun l => dA m m l) (gen132 m) a b).
Qed.

(* ------------------------------------------------------------------ *)
(* Increasing lists, standardisation and its inverse.  A strictly increasing
   list is determined by its elements, and the rank of an entry is its index,
   so relabelling undoes standardisation. *)

Lemma incr_cons_min : forall a l, incr (a :: l) -> forall x, In x l -> (a < x)%nat.
Proof.
  intros a l H x Hx. apply In_nth with (d := 0%nat) in Hx.
  destruct Hx as [t [Ht Hnth]].
  assert (K := H 0%nat (S t) ltac:(lia) ltac:(cbn [length]; lia)).
  cbn [nth] in K. rewrite Hnth in K. exact K.
Qed.

Lemma incr_tl : forall a l, incr (a :: l) -> incr l.
Proof.
  intros a l H p q Hpq Hq.
  assert (K := H (S p) (S q) ltac:(lia) ltac:(cbn [length]; lia)).
  cbn [nth] in K. exact K.
Qed.

Lemma incr_seq : forall n, incr (seq 0 n).
Proof.
  intros n a b Hab Hb. rewrite length_seq in Hb.
  rewrite !seq_nth by lia. lia.
Qed.

Lemma incr_filter : forall Q l, incr l -> incr (filter Q l).
Proof.
  intros Q l Hl a b Hab Hb.
  destruct (subseq_index (filter Q l) l (filter_subseq Q l)) as [f [Hmono Hval]].
  destruct (Hval a ltac:(lia)) as [Ha1 Ha2].
  destruct (Hval b Hb) as [Hb1 Hb2].
  rewrite Ha2, Hb2. apply Hl; [apply Hmono; assumption | exact Hb1].
Qed.

Lemma incr_eq : forall l l', incr l -> incr l' -> NoDup l -> NoDup l' ->
  (forall x, In x l <-> In x l') -> l = l'.
Proof.
  induction l as [|a l IH]; intros l' Hl Hl' Hnd Hnd' Hsame.
  - destruct l' as [|b l']; [reflexivity|].
    exfalso.
    assert (Hb : In b (@nil nat))
      by (apply (proj2 (Hsame b)); left; reflexivity).
    contradiction.
  - destruct l' as [|b l'].
    + exfalso.
      assert (Ha : In a (@nil nat))
        by (apply (proj1 (Hsame a)); left; reflexivity).
      contradiction.
    + assert (Hab : a = b).
      { destruct (Nat.lt_trichotomy a b) as [K|[K|K]]; [| exact K |].
        - exfalso.
          assert (Ha : In a (b :: l'))
            by (apply (proj1 (Hsame a)); left; reflexivity).
          destruct Ha as [Ha | Ha]; [lia|].
          assert (b < a)%nat by (apply (incr_cons_min b l' Hl'); exact Ha). lia.
        - exfalso.
          assert (Hb : In b (a :: l))
            by (apply (proj2 (Hsame b)); left; reflexivity).
          destruct Hb as [Hb | Hb]; [lia|].
          assert (a < b)%nat by (apply (incr_cons_min a l Hl); exact Hb). lia. }
      subst b. f_equal.
      inversion Hnd as [|z zs Hna Hndl]; subst.
      inversion Hnd' as [|z zs Hna' Hndl']; subst.
      apply IH.
      * apply (incr_tl a). exact Hl.
      * apply (incr_tl a). exact Hl'.
      * exact Hndl.
      * exact Hndl'.
      * intro x. split.
        -- intro Hx.
           assert (Hx2 : In x (a :: l'))
             by (apply (proj1 (Hsame x)); right; exact Hx).
           destruct Hx2 as [Hx2 | Hx2]; [| exact Hx2].
           exfalso. apply Hna. rewrite Hx2. exact Hx.
        -- intro Hx.
           assert (Hx2 : In x (a :: l))
             by (apply (proj2 (Hsame x)); right; exact Hx).
           destruct Hx2 as [Hx2 | Hx2]; [| exact Hx2].
           exfalso. apply Hna'. rewrite Hx2. exact Hx.
Qed.

Lemma length_filter_lt : forall (Q : nat -> bool) l x,
  In x l -> Q x = false -> (length (filter Q l) < length l)%nat.
Proof.
  intros Q l. induction l as [|a l IH]; intros x Hx HQ; [contradiction|].
  cbn [filter length]. destruct Hx as [Hx | Hx].
  - subst a. rewrite HQ. assert (K := length_filter_le_gen nat Q l). lia.
  - assert (K := IH x Hx HQ). destruct (Q a); cbn [length]; lia.
Qed.

(* In an increasing list the rank of an entry is its index. *)
Lemma incr_rank : forall V, incr V -> NoDup V ->
  forall t, (t < length V)%nat -> rankin V (nth t V 0%nat) = t.
Proof.
  induction V as [|a V IH]; intros Hi Hnd t Ht; cbn [length] in Ht; [lia|].
  inversion Hnd as [|z zs Hna Hndv]; subst.
  destruct t as [|t].
  - unfold rankin. cbn [nth filter]. rewrite Nat.ltb_irrefl.
    rewrite (filter_all_false (fun y => Nat.ltb y a) V); [reflexivity|].
    intros y Hy. assert (Hay : (a < y)%nat)
      by (apply (incr_cons_min a V Hi); exact Hy).
    destruct (Nat.ltb_spec y a); [exfalso; lia | reflexivity].
  - cbn [nth]. unfold rankin. cbn [filter].
    assert (Hlt : (a < nth t V 0%nat)%nat)
      by (apply (incr_cons_min a V Hi); apply nth_In; lia).
    destruct (Nat.ltb_spec a (nth t V 0%nat)); [|exfalso; lia].
    cbn [length].
    change (length (filter (fun y => Nat.ltb y (nth t V 0%nat)) V))
      with (rankin V (nth t V 0%nat)).
    rewrite (IH (incr_tl a V Hi) Hndv t ltac:(lia)). reflexivity.
Qed.

Lemma incr_nth_rank : forall V x, incr V -> NoDup V -> In x V ->
  nth (rankin V x) V 0%nat = x.
Proof.
  intros V x Hi Hnd Hx.
  apply In_nth with (d := 0%nat) in Hx. destruct Hx as [t [Ht Hnth]].
  rewrite <- Hnth, (incr_rank V Hi Hnd t Ht). reflexivity.
Qed.

Lemma rankin_lt_length : forall l x, In x l -> (rankin l x < length l)%nat.
Proof.
  intros l x Hx. unfold rankin.
  apply (length_filter_lt (fun y => Nat.ltb y x) l x Hx).
  apply Nat.ltb_irrefl.
Qed.

Lemma std_is_perm : forall l, NoDup l -> is_perm (std l) (length l).
Proof.
  intros l Hnd. split; [apply len_map_gen | split].
  - unfold std. apply NoDup_map_inj; [exact Hnd|].
    intros x y Hx Hy He. exact (rankin_inj l x y Hnd Hx Hy He).
  - intros x Hx. unfold std in Hx. apply in_map_iff in Hx.
    destruct Hx as [y [Hy Hyin]]. subst x. apply rankin_lt_length. exact Hyin.
Qed.

(* Relabelling through the increasing arrangement undoes standardisation. *)
Lemma relab_std : forall V l, incr V -> NoDup V -> Permutation l V ->
  relab V (std l) = l.
Proof.
  intros V l Hi Hnd Hp. unfold relab, std. rewrite map_map.
  transitivity (map (fun x => x) l).
  - apply map_ext_in. intros x Hx.
    assert (Hxv : In x V) by (apply (Permutation_in _ Hp); exact Hx).
    rewrite (rankin_perm l V Hp x). apply incr_nth_rank; assumption.
  - apply map_id.
Qed.

Lemma relab_inj : forall V u u' m,
  incr V -> is_perm u m -> is_perm u' m -> length V = m ->
  relab V u = relab V u' -> u = u'.
Proof.
  intros V u u' m Hi Hu Hu' Hlen He.
  destruct Hu as [Hlu [_ Hbu]]. destruct Hu' as [Hlu' [_ Hbu']].
  apply (nth_ext u u' 0%nat 0%nat); [lia|].
  intros t Ht.
  assert (Et : nth t (relab V u) 0%nat = nth t (relab V u') 0%nat)
    by (rewrite He; reflexivity).
  rewrite (relab_nth V u t Ht) in Et.
  rewrite (relab_nth V u' t ltac:(lia)) in Et.
  assert (Bu : (nth t u 0%nat < length V)%nat)
    by (rewrite Hlen; apply Hbu; apply nth_In; lia).
  assert (Bu' : (nth t u' 0%nat < length V)%nat)
    by (rewrite Hlen; apply Hbu'; apply nth_In; lia).
  destruct (Nat.lt_trichotomy (nth t u 0%nat) (nth t u' 0%nat)) as [K|[K|K]];
    [| exact K |].
  - exfalso. assert (Hi2 := Hi _ _ K Bu'). lia.
  - exfalso. assert (Hi2 := Hi _ _ K Bu). lia.
Qed.

Lemma map_nth_seq : forall (A : Type) (d : A) (l : list A),
  map (fun i => nth i l d) (seq 0 (length l)) = l.
Proof.
  intros A d. induction l as [|a l IH]; [reflexivity|].
  cbn [length]. change (seq 0 (S (length l))) with (0%nat :: seq 1 (length l)).
  cbn [map nth]. f_equal.
  rewrite <- (seq_shift (length l) 0), map_map. cbn [nth]. exact IH.
Qed.

Lemma skipn_len_app : forall (l1 l2 : list nat),
  skipn (length l1) (l1 ++ l2) = l2.
Proof.
  induction l1 as [|a l1 IH]; intro l2; cbn [length app skipn];
    [reflexivity | apply IH].
Qed.

Lemma nth_rev_nat : forall (l : list nat) t, (t < length l)%nat ->
  nth t (rev l) 0%nat = nth (length l - S t)%nat l 0%nat.
Proof. intros l t H. rewrite rev_nth by exact H. reflexivity. Qed.

Lemma rev_decreasing : forall l, incr l ->
  forall t t', (t < t')%nat -> (t' < length (rev l))%nat ->
    (nth t' (rev l) 0%nat < nth t (rev l) 0%nat)%nat.
Proof.
  intros l Hi t t' Htt Ht'. rewrite length_rev in Ht'.
  rewrite (nth_rev_nat l t' ltac:(lia)), (nth_rev_nat l t ltac:(lia)).
  apply Hi; lia.
Qed.

Lemma is_perm_of_perm_seq : forall w m, Permutation w (seq 0 m) -> is_perm w m.
Proof.
  intros w m H. split; [| split].
  - rewrite (Permutation_length H), length_seq. reflexivity.
  - apply (Permutation_NoDup (Permutation_sym H)). apply seq_NoDup.
  - intros x Hx.
    assert (Hx2 : In x (seq 0 m)) by (apply (Permutation_in _ H); exact Hx).
    apply in_seq in Hx2. lia.
Qed.

Lemma perm_seq_of_is_perm : forall u m, is_perm u m -> Permutation u (seq 0 m).
Proof.
  intros u m Hp. assert (Hp' := Hp). destruct Hp as [Hlen [Hnd Hb]].
  apply NoDup_Permutation; [exact Hnd | apply seq_NoDup |].
  intro x. split.
  - intro Hx. apply in_seq. split; [lia | apply Hb; exact Hx].
  - intro Hx. apply in_seq in Hx. apply (perm_full u m Hp'). lia.
Qed.

Lemma relab_perm : forall V u m, is_perm u m -> length V = m ->
  Permutation (relab V u) V.
Proof.
  intros V u m Hp Hlen. unfold relab.
  transitivity (map (fun t => nth t V 0%nat) (seq 0 (length V))).
  - apply Permutation_map. rewrite Hlen. apply (perm_seq_of_is_perm u m Hp).
  - rewrite (map_nth_seq nat 0%nat V). apply Permutation_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* The decreasing suffix fibre is a free product.  A word counted by
   N_sigma(M) at the decreasing pattern is a choice of which d of the M+d
   values form the suffix, arranged the one way they may be, together with a
   132-avoiding pattern for the prefix carried onto the remaining values.  So
   N_dec(M) = Cat(M) C(M+d,d), which is what makes the decreasing sigma the
   unique level-0 pattern. *)

Definition hiv (P : list bool) : list nat :=
  filter (fun v => nth v P false) (seq 0 (length P)).
Definition lov (P : list bool) : list nat :=
  filter (fun v => negb (nth v P false)) (seq 0 (length P)).

Lemma hiv_lov_perm : forall P, Permutation (seq 0 (length P)) (hiv P ++ lov P).
Proof.
  intro P. unfold hiv, lov.
  assert (Q := perm_filter_split (fun v => nth v P false) (seq 0 (length P))).
  cbn beta in Q. exact Q.
Qed.

Lemma hiv_length : forall P, length (hiv P) = countt P.
Proof.
  intro P. unfold hiv.
  rewrite <- (countt_map (fun v => nth v P false) (seq 0 (length P))).
  rewrite (map_nth_seq bool false P). reflexivity.
Qed.

Lemma lov_length : forall P, length (lov P) = (length P - countt P)%nat.
Proof.
  intro P. assert (L := Permutation_length (hiv_lov_perm P)).
  rewrite length_seq, len_app, hiv_length in L. lia.
Qed.

Lemma hiv_incr : forall P, incr (hiv P).
Proof. intro P. unfold hiv. apply incr_filter. apply incr_seq. Qed.

Lemma lov_incr : forall P, incr (lov P).
Proof. intro P. unfold lov. apply incr_filter. apply incr_seq. Qed.

Lemma hiv_nodup : forall P, NoDup (hiv P).
Proof. intro P. unfold hiv. apply NoDup_filter. apply seq_NoDup. Qed.

Lemma lov_nodup : forall P, NoDup (lov P).
Proof. intro P. unfold lov. apply NoDup_filter. apply seq_NoDup. Qed.

Lemma hiv_bound : forall P x, In x (hiv P) -> (x < length P)%nat.
Proof.
  intros P x H. unfold hiv in H. apply filter_In in H. destruct H as [H _].
  apply in_seq in H. lia.
Qed.

Lemma nth_hiv : forall P v, (v < length P)%nat ->
  (In v (hiv P) <-> nth v P false = true).
Proof.
  intros P v Hv. unfold hiv. rewrite filter_In. split.
  - intros [_ H]. exact H.
  - intro H. split; [apply in_seq; lia | exact H].
Qed.

Lemma nth_lov : forall P v, (v < length P)%nat ->
  (In v (lov P) <-> nth v P false = false).
Proof.
  intros P v Hv. unfold lov. rewrite filter_In. split.
  - intros [_ H]. destruct (nth v P false); [discriminate | reflexivity].
  - intro H. split; [apply in_seq; lia |]. rewrite H. reflexivity.
Qed.

Lemma hiv_inj : forall P P', length P = length P' -> hiv P = hiv P' -> P = P'.
Proof.
  intros P P' Hlen He.
  apply (nth_ext P P' false false); [exact Hlen|].
  intros v Hv.
  destruct (nth v P false) eqn:E1; destruct (nth v P' false) eqn:E2;
    try reflexivity.
  - exfalso.
    assert (H : In v (hiv P)) by (apply (proj2 (nth_hiv P v Hv)); exact E1).
    rewrite He in H.
    assert (H2 : nth v P' false = true)
      by (apply (proj1 (nth_hiv P' v ltac:(lia))); exact H).
    rewrite E2 in H2. discriminate.
  - exfalso.
    assert (H : In v (hiv P'))
      by (apply (proj2 (nth_hiv P' v ltac:(lia))); exact E2).
    rewrite <- He in H.
    assert (H2 : nth v P false = true)
      by (apply (proj1 (nth_hiv P v Hv)); exact H).
    rewrite E1 in H2. discriminate.
Qed.

Lemma map_nth_defb : forall (f : nat -> bool) l t, (t < length l)%nat ->
  nth t (map f l) false = f (nth t l 0%nat).
Proof.
  intros f l t H.
  erewrite nth_indep by (rewrite len_map_gen; exact H).
  rewrite map_nth. reflexivity.
Qed.

Lemma existsb_eqb_In : forall v S, existsb (Nat.eqb v) S = true <-> In v S.
Proof.
  intros v S. rewrite existsb_exists. split.
  - intros [x [Hx He]]. apply Nat.eqb_eq in He. subst x. exact Hx.
  - intro H. exists v. split; [exact H | apply Nat.eqb_refl].
Qed.

Lemma existsb_eqb_notIn : forall v S, existsb (Nat.eqb v) S = false <-> ~ In v S.
Proof.
  intros v S. split.
  - intros H C.
    assert (K : existsb (Nat.eqb v) S = true)
      by (apply existsb_eqb_In; exact C).
    rewrite H in K. discriminate.
  - intro H. destruct (existsb (Nat.eqb v) S) eqn:E; [|reflexivity].
    exfalso. apply H. apply existsb_eqb_In. exact E.
Qed.

Lemma rev_incr : forall l,
  (forall t t', (t < t')%nat -> (t' < length l)%nat ->
     (nth t' l 0%nat < nth t l 0%nat)%nat) -> incr (rev l).
Proof.
  intros l H a b Hab Hb. rewrite length_rev in Hb.
  rewrite (nth_rev_nat l a ltac:(lia)), (nth_rev_nat l b ltac:(lia)).
  apply H; lia.
Qed.

Lemma in_firstn_w : forall (w : list nat) M x, In x (firstn M w) -> In x w.
Proof.
  intros w M x H. rewrite <- (firstn_skipn M w).
  apply in_app_iff. left. exact H.
Qed.

Lemma in_skipn_w : forall (w : list nat) M x, In x (skipn M w) -> In x w.
Proof.
  intros w M x H. rewrite <- (firstn_skipn M w).
  apply in_app_iff. right. exact H.
Qed.

Lemma in_firstn_or_skipn : forall (w : list nat) M x,
  In x w -> (In x (firstn M w) \/ In x (skipn M w)).
Proof.
  intros w M x H. apply in_app_iff. rewrite (firstn_skipn M w). exact H.
Qed.

Lemma nodup_firstn_skipn : forall (w : list nat) M x,
  NoDup w -> In x (firstn M w) -> In x (skipn M w) -> False.
Proof.
  intros w M x Hnd H1 H2.
  rewrite <- (firstn_skipn M w) in Hnd.
  apply (nodup_app_disjoint (firstn M w) (skipn M w) x Hnd H1 H2).
Qed.

Definition decword (P : list bool) (u : list nat) : list nat :=
  relab (lov P) u ++ rev (hiv P).

Lemma decword_spec : forall M d P u,
  In P (bwords (M + d) d) -> In u (gen132 M) ->
  is_perm (decword P u) (M + d)
  /\ ~ contains_1324 (decword P u)
  /\ firstn M (decword P u) = relab (lov P) u
  /\ skipn M (decword P u) = rev (hiv P)
  /\ suffix_pat d (decword P u) = decpat d
  /\ ~ contains_132 (firstn M (decword P u)).
Proof.
  intros M d P u HP Hu.
  apply bwords_spec in HP. destruct HP as [HPlen HPcnt].
  apply gen132_spec in Hu. destruct Hu as [Hup Hu132].
  assert (Hulen : length u = M) by av.
  assert (HlovM : length (lov P) = M)
    by (rewrite lov_length, HPlen, HPcnt; lia).
  assert (HhivD : length (hiv P) = d) by (rewrite hiv_length; exact HPcnt).
  assert (Hb' : forall x, In x u -> (x < length (lov P))%nat).
  { intros x Hx. rewrite HlovM. destruct Hup as [_ [_ Hb]]. apply Hb. exact Hx. }
  assert (Hrelablen : length (relab (lov P) u) = M)
    by (rewrite relab_length; exact Hulen).
  assert (Hfst : firstn M (decword P u) = relab (lov P) u).
  { unfold decword. rewrite <- Hrelablen. apply firstn_len_app. }
  assert (Hskp : skipn M (decword P u) = rev (hiv P)).
  { unfold decword. rewrite <- Hrelablen. apply skipn_len_app. }
  assert (Hperm : Permutation (decword P u) (seq 0 (M + d))).
  { unfold decword.
    transitivity (lov P ++ hiv P).
    - apply Permutation_app.
      + apply (relab_perm (lov P) u M Hup HlovM).
      + apply Permutation_sym. apply Permutation_rev.
    - apply Permutation_sym. rewrite <- HPlen.
      transitivity (hiv P ++ lov P);
        [apply hiv_lov_perm | apply Permutation_app_comm]. }
  assert (Hip : is_perm (decword P u) (M + d))
    by (apply is_perm_of_perm_seq; exact Hperm).
  assert (Hnd : NoDup (decword P u)) by av.
  assert (Hlen : length (decword P u) = (M + d)%nat)
    by av.
  assert (Hdec : forall t t', (t < t')%nat -> (t' < d)%nat ->
    (nth t' (skipn M (decword P u)) 0%nat
     < nth t (skipn M (decword P u)) 0%nat)%nat).
  { intros t t' H1 H2. rewrite Hskp.
    apply rev_decreasing; [apply hiv_incr | exact H1 |].
    rewrite length_rev, HhivD. exact H2. }
  assert (Hpre : ~ contains_132 (relab (lov P) u)).
  { intro C. apply Hu132.
    apply (proj1 (relab_132 (lov P) u (lov_incr P) Hb')). exact C. }
  assert (H1324 : ~ contains_1324 (decword P u)).
  { unfold decword. apply (dec_fibre_free (lov P) u (rev (hiv P))).
    - apply lov_incr.
    - exact Hb'.
    - exact Hu132.
    - intros t t' H1 H2.
      apply rev_decreasing; [apply hiv_incr | exact H1 | exact H2]. }
  assert (Hsp : suffix_pat d (decword P u) = decpat d)
    by (apply (proj2 (dec_fibre_iff d M (decword P u) Hlen Hnd)); exact Hdec).
  split; [exact Hip | split; [exact H1324 | split; [exact Hfst |
    split; [exact Hskp | split; [exact Hsp |]]]]].
  rewrite Hfst. exact Hpre.
Qed.

Lemma decword_recover : forall M d w,
  In w (gen (M + d)) -> ~ contains_132 (firstn M w) ->
  suffix_pat d w = decpat d ->
  exists P u, In P (bwords (M + d) d) /\ In u (gen132 M) /\ w = decword P u.
Proof.
  intros M d w Hw Hpre Hsp.
  apply gen_spec in Hw. destruct Hw as [Hip H1324].
  assert (Hlen : length w = (M + d)%nat) by av.
  assert (Hnd : NoDup w) by av.
  assert (Hwb : forall x, In x w -> (x < M + d)%nat)
    by av.
  assert (Hdec := proj1 (dec_fibre_iff d M w Hlen Hnd) Hsp).
  assert (Hsklen : length (skipn M w) = d)
    by (rewrite length_skipn, Hlen; lia).
  assert (Hsknd : NoDup (skipn M w)) by (apply NoDup_skipn; exact Hnd).
  set (S := rev (skipn M w)).
  assert (HSincr : incr S).
  { unfold S. apply rev_incr. intros t t' H1 H2.
    apply Hdec; [exact H1 | rewrite Hsklen in H2; exact H2]. }
  assert (HSnd : NoDup S)
    by (unfold S; apply (Permutation_NoDup (Permutation_rev _)); exact Hsknd).
  assert (HSin : forall x, In x S <-> In x (skipn M w)).
  { intro x. unfold S. split; intro H.
    - apply (Permutation_in _ (Permutation_sym (Permutation_rev _))). exact H.
    - apply (Permutation_in _ (Permutation_rev _)). exact H. }
  set (P := map (fun v => existsb (Nat.eqb v) S) (seq 0 (M + d))).
  assert (HPlen : length P = (M + d)%nat)
    by (unfold P; rewrite len_map_gen, length_seq; reflexivity).
  assert (HPnth : forall v, (v < M + d)%nat ->
                  nth v P false = existsb (Nat.eqb v) S).
  { intros v Hv. unfold P.
    rewrite (map_nth_defb (fun v => existsb (Nat.eqb v) S) (seq 0 (M + d)) v)
      by (rewrite length_seq; exact Hv).
    rewrite seq_nth by exact Hv. reflexivity. }
  assert (HhivS : hiv P = S).
  { apply incr_eq;
      [apply hiv_incr | exact HSincr | apply hiv_nodup | exact HSnd |].
    intro x. split.
    - intro Hx.
      assert (Hxb : (x < M + d)%nat) by (rewrite <- HPlen; apply hiv_bound; exact Hx).
      assert (K : nth x P false = true)
        by (apply (proj1 (nth_hiv P x ltac:(lia))); exact Hx).
      rewrite (HPnth x Hxb) in K. apply existsb_eqb_In. exact K.
    - intro Hx.
      assert (Hxb : (x < M + d)%nat).
      { apply Hwb. apply (in_skipn_w w M). apply HSin. exact Hx. }
      apply (proj2 (nth_hiv P x ltac:(lia))).
      rewrite (HPnth x Hxb). apply existsb_eqb_In. exact Hx. }
  assert (Hrevhiv : rev (hiv P) = skipn M w)
    by (rewrite HhivS; unfold S; apply rev_involutive).
  assert (Hlovpre : forall x, In x (lov P) <-> In x (firstn M w)).
  { intro x. split.
    - intro Hx.
      assert (Hxb : (x < M + d)%nat).
      { unfold lov in Hx. apply filter_In in Hx. destruct Hx as [Hx _].
        apply in_seq in Hx. lia. }
      assert (K : nth x P false = false)
        by (apply (proj1 (nth_lov P x ltac:(lia))); exact Hx).
      rewrite (HPnth x Hxb) in K.
      assert (Hns : ~ In x S) by (apply existsb_eqb_notIn; exact K).
      assert (Hinw : In x w).
      { apply (perm_full w (M + d) Hip). exact Hxb. }
      destruct (in_firstn_or_skipn w M x Hinw) as [Hf | Hs];
        [exact Hf | exfalso; apply Hns; apply HSin; exact Hs].
    - intro Hx.
      assert (Hinw : In x w) by (apply (in_firstn_w w M); exact Hx).
      assert (Hxb : (x < M + d)%nat) by (apply Hwb; exact Hinw).
      assert (Hns : ~ In x S).
      { intro C. apply (nodup_firstn_skipn w M x Hnd Hx). apply HSin. exact C. }
      apply (proj2 (nth_lov P x ltac:(lia))).
      rewrite (HPnth x Hxb). apply existsb_eqb_notIn. exact Hns. }
  assert (Hfstlen : length (firstn M w) = M)
    by (rewrite length_firstn, Hlen; lia).
  assert (Hpermlov : Permutation (firstn M w) (lov P)).
  { apply NoDup_Permutation;
      [apply NoDup_firstn; exact Hnd | apply lov_nodup |].
    intro x. split; [apply Hlovpre | apply Hlovpre]. }
  assert (Hrel : relab (lov P) (std (firstn M w)) = firstn M w)
    by (apply relab_std; [apply lov_incr | apply lov_nodup | exact Hpermlov]).
  exists P, (std (firstn M w)).
  split; [| split].
  - apply bwords_spec. split; [exact HPlen|].
    rewrite <- hiv_length, HhivS. unfold S.
    rewrite length_rev. exact Hsklen.
  - assert (Hstd : is_perm (std (firstn M w)) M).
    { assert (Hs := std_is_perm (firstn M w) (NoDup_firstn M w Hnd)).
      rewrite Hfstlen in Hs. exact Hs. }
    assert (HlovM : length (lov P) = M).
    { rewrite lov_length, HPlen, <- hiv_length, HhivS.
      unfold S. rewrite length_rev, Hsklen. lia. }
    assert (Hbnd : forall x, In x (std (firstn M w)) ->
                   (x < length (lov P))%nat).
    { intros x Hx. rewrite HlovM. destruct Hstd as [_ [_ Hb]].
      apply Hb. exact Hx. }
    apply gen132_spec. split; [exact Hstd|].
    intro C. apply Hpre. rewrite <- Hrel.
    apply (proj2 (relab_132 (lov P) (std (firstn M w)) (lov_incr P) Hbnd)).
    exact C.
  - unfold decword. rewrite Hrel, Hrevhiv. symmetry. apply firstn_skipn.
Qed.

Theorem Nsig_dec : forall d M,
  Nsig d M (decpat d) = (binomN (M + d) d * card132 M)%nat.
Proof.
  intros d M. unfold Nsig.
  set (L2 := map (fun p => decword (fst p) (snd p))
                 (list_prod (bwords (M + d) d) (gen132 M))).
  assert (HL2 : length L2 = (binomN (M + d) d * card132 M)%nat).
  { unfold L2. rewrite len_map_gen, length_list_prod, bwords_length.
    reflexivity. }
  rewrite <- HL2.
  apply Nat.le_antisymm.
  - apply NoDup_incl_length.
    + apply NoDup_filter. apply gen_nodup.
    + intros w Hw. apply filter_In in Hw. destruct Hw as [Hw He].
      apply andb_true_iff in He. destruct He as [He1 He2].
      destruct (list_eq_dec Nat.eq_dec (suffix_pat d w) (decpat d)) as [E|E];
        [| discriminate].
      destruct (decword_recover M d w Hw (avoids132b_true _ He1) E)
        as [P [u [HP [Hu Hwe]]]].
      unfold L2. apply in_map_iff. exists (P, u). split.
      * cbn [fst snd]. symmetry. exact Hwe.
      * apply in_prod; assumption.
  - apply NoDup_incl_length.
    + unfold L2. apply NoDup_map_inj.
      * apply NoDup_list_prod; [apply bwords_nodup | apply gen132_nodup].
      * intros p q Hp Hq He. cbn beta in He.
        destruct p as [P1 u1]; destruct q as [P2 u2]. cbn [fst snd] in He.
        apply in_prod_iff in Hp. destruct Hp as [HP1 Hu1].
        apply in_prod_iff in Hq. destruct Hq as [HP2 Hu2].
        destruct (decword_spec M d P1 u1 HP1 Hu1) as [_ [_ [Ef1 [Es1 _]]]].
        destruct (decword_spec M d P2 u2 HP2 Hu2) as [_ [_ [Ef2 [Es2 _]]]].
        assert (EP : P1 = P2).
        { apply (hiv_inj P1 P2).
          - assert (K1 := proj1 (proj1 (bwords_spec (M + d) d P1) HP1)).
            assert (K2 := proj1 (proj1 (bwords_spec (M + d) d P2) HP2)).
            lia.
          - assert (K : rev (hiv P1) = rev (hiv P2))
              by (rewrite <- Es1, <- Es2, He; reflexivity).
            apply (f_equal (@rev nat)) in K.
            rewrite !rev_involutive in K. exact K. }
        subst P2.
        assert (Eu : u1 = u2).
        { apply (relab_inj (lov P1) u1 u2 M (lov_incr P1)).
          - exact (proj1 (proj1 (gen132_spec M u1) Hu1)).
          - exact (proj1 (proj1 (gen132_spec M u2) Hu2)).
          - assert (K := proj1 (bwords_spec (M + d) d P1) HP1).
            destruct K as [Hl Hc]. rewrite lov_length, Hl, Hc. lia.
          - rewrite <- Ef1, <- Ef2, He. reflexivity. }
        subst. reflexivity.
    + intros z Hz. unfold L2 in Hz. apply in_map_iff in Hz.
      destruct Hz as [p [Hpz Hpin]]. destruct p as [P u].
      cbn [fst snd] in Hpz. subst z.
      apply in_prod_iff in Hpin. destruct Hpin as [HP Hu].
      destruct (decword_spec M d P u HP Hu)
        as [Hip [H1324 [Hf [Hs [Hsp Hp132]]]]].
      apply filter_In. split.
      * apply gen_spec. split; [exact Hip | exact H1324].
      * apply andb_true_iff. split.
        -- apply avoids132b_intro. exact Hp132.
        -- destruct (list_eq_dec Nat.eq_dec (suffix_pat d (decword P u))
                       (decpat d)) as [E|E]; [reflexivity | contradiction].
Qed.

(* In Catalan form: N_dec(M) = Cat(M) C(M+d,d), the free product. *)
Corollary Nsig_dec_catalan : forall d M,
  (S M * Nsig d M (decpat d))%nat
  = (binomN (M + d) d * binomN (2 * M) M)%nat.
Proof.
  intros d M. rewrite Nsig_dec, <- card132_binom. ring.
Qed.

(* With Nsig_le_dec the free product bounds every fibre, so no suffix pattern
   contributes more than the decreasing one, and the diagonal is bounded below
   by that one pattern alone. *)
Corollary Nsig_le_free : forall d M sg,
  (Nsig d M sg <= binomN (M + d) d * card132 M)%nat.
Proof. intros d M sg. rewrite <- Nsig_dec. apply Nsig_le_dec. Qed.

Corollary Ddiag_ge_free : forall d M,
  (binomN (M + d) d * card132 M <= Ddiag d M)%nat.
Proof.
  intros d M. rewrite <- Nsig_dec. unfold Nsig, Ddiag.
  rewrite <- (filter_filter (list nat)
                (fun w => avoids132b (firstn M w))
                (fun w => if list_eq_dec Nat.eq_dec (suffix_pat d w) (decpat d)
                          then true else false)
                (gen (M + d))).
  apply length_filter_le_gen.
Qed.

(* ------------------------------------------------------------------ *)
(* Standardisation as a class map.  Relabelling reflects every pattern, and a
   duplicate-free list is the relabelling of its own standardisation through
   the increasing arrangement of its values, so std preserves and reflects
   avoidance.  It also commutes with a value cut, which is what carries a
   gridded word to a domino. *)

Lemma subseq_refl : forall (l : list nat), subseq l l.
Proof. induction l as [|a l IH]; [apply ss_nil | apply ss_keep; exact IH]. Qed.

Lemma firstn_subseq : forall k (w : list nat), subseq (firstn k w) w.
Proof.
  induction k as [|k IH]; intro w; [apply ss_nil|].
  destruct w as [|a w]; cbn [firstn]; [apply ss_nil | apply ss_keep; apply IH].
Qed.

Lemma skipn_subseq : forall k (w : list nat), subseq (skipn k w) w.
Proof.
  induction k as [|k IH]; intro w; cbn [skipn]; [apply subseq_refl|].
  destruct w as [|a w]; [apply ss_nil | apply ss_skip; apply IH].
Qed.

Theorem subseq_132 : forall v u, subseq v u -> contains_132 v -> contains_132 u.
Proof.
  intros v u Hss [i [j [k H]]].
  destruct (subseq_index v u Hss) as [f [Hmono Hval]].
  unfold has_132_at in H. destruct H as [Hij [Hjk [Hk [Hik Hkj]]]].
  destruct (Hval i ltac:(lia)) as [Hfi Ei].
  destruct (Hval j ltac:(lia)) as [Hfj Ej].
  destruct (Hval k Hk) as [Hfk Ek].
  exists (f i), (f j), (f k). unfold has_132_at.
  rewrite <- Ei, <- Ej, <- Ek.
  repeat split; try assumption; apply Hmono; lia.
Qed.

Theorem subseq_1324 : forall v u,
  subseq v u -> contains_1324 v -> contains_1324 u.
Proof.
  intros v u Hss [i [j [k [l H]]]].
  destruct (subseq_index v u Hss) as [f [Hmono Hval]].
  unfold has_1324_at in H. destruct H as [Hij [Hjk [Hkl [Hl [Hik [Hkj Hjl]]]]]].
  destruct (Hval i ltac:(lia)) as [Hfi Ei].
  destruct (Hval j ltac:(lia)) as [Hfj Ej].
  destruct (Hval k ltac:(lia)) as [Hfk Ek].
  destruct (Hval l Hl) as [Hfl El].
  exists (f i), (f j), (f k), (f l). unfold has_1324_at.
  rewrite <- Ei, <- Ej, <- Ek, <- El.
  repeat split; try assumption; apply Hmono; lia.
Qed.

Theorem relab_213 : forall vals u,
  incr vals -> (forall x, In x u -> (x < length vals)%nat) ->
  (contains_213 (relab vals u) <-> contains_213 u).
Proof.
  intros vals u Hi Hb. split.
  - intros [i [j [k H]]]. unfold has_213_at in H.
    destruct H as [Hij [Hjk [Hk [Hji Hik]]]].
    rewrite relab_length in Hk.
    exists i, j, k. unfold has_213_at. repeat split; try lia.
    + apply (relab_lt vals u j i Hi Hb ltac:(lia) ltac:(lia)). exact Hji.
    + apply (relab_lt vals u i k Hi Hb ltac:(lia) ltac:(lia)). exact Hik.
  - intros [i [j [k H]]]. unfold has_213_at in H.
    destruct H as [Hij [Hjk [Hk [Hji Hik]]]].
    exists i, j, k. unfold has_213_at. rewrite relab_length.
    repeat split; try lia.
    + apply (relab_lt vals u j i Hi Hb ltac:(lia) ltac:(lia)). exact Hji.
    + apply (relab_lt vals u i k Hi Hb ltac:(lia) ltac:(lia)). exact Hik.
Qed.

Theorem relab_1324 : forall vals u,
  incr vals -> (forall x, In x u -> (x < length vals)%nat) ->
  (contains_1324 (relab vals u) <-> contains_1324 u).
Proof.
  intros vals u Hi Hb. split.
  - intros [i [j [k [l H]]]]. unfold has_1324_at in H.
    destruct H as [Hij [Hjk [Hkl [Hl [Hik [Hkj Hjl]]]]]].
    rewrite relab_length in Hl.
    exists i, j, k, l. unfold has_1324_at. repeat split; try lia.
    + apply (relab_lt vals u i k Hi Hb ltac:(lia) ltac:(lia)). exact Hik.
    + apply (relab_lt vals u k j Hi Hb ltac:(lia) ltac:(lia)). exact Hkj.
    + apply (relab_lt vals u j l Hi Hb ltac:(lia) ltac:(lia)). exact Hjl.
  - intros [i [j [k [l H]]]]. unfold has_1324_at in H.
    destruct H as [Hij [Hjk [Hkl [Hl [Hik [Hkj Hjl]]]]]].
    exists i, j, k, l. unfold has_1324_at. rewrite relab_length.
    repeat split; try lia.
    + apply (relab_lt vals u i k Hi Hb ltac:(lia) ltac:(lia)). exact Hik.
    + apply (relab_lt vals u k j Hi Hb ltac:(lia) ltac:(lia)). exact Hkj.
    + apply (relab_lt vals u j l Hi Hb ltac:(lia) ltac:(lia)). exact Hjl.
Qed.

(* The increasing arrangement of a bounded duplicate-free list, without a sort. *)
Definition sortset (n : nat) (l : list nat) : list nat :=
  filter (fun v => existsb (Nat.eqb v) l) (seq 0 n).

Lemma sortset_incr : forall n l, incr (sortset n l).
Proof. intros n l. unfold sortset. apply incr_filter. apply incr_seq. Qed.

Lemma sortset_nodup : forall n l, NoDup (sortset n l).
Proof. intros n l. unfold sortset. apply NoDup_filter. apply seq_NoDup. Qed.

Lemma sortset_In : forall n l x,
  (forall y, In y l -> (y < n)%nat) -> (In x (sortset n l) <-> In x l).
Proof.
  intros n l x Hb. unfold sortset. rewrite filter_In. split.
  - intros [_ H]. apply existsb_eqb_In. exact H.
  - intro H. split; [apply in_seq; split; [lia | apply Hb; exact H]|].
    apply existsb_eqb_In. exact H.
Qed.

Lemma sortset_perm : forall n l, NoDup l -> (forall y, In y l -> (y < n)%nat) ->
  Permutation l (sortset n l).
Proof.
  intros n l Hnd Hb. apply NoDup_Permutation; [exact Hnd | apply sortset_nodup|].
  intro x. symmetry. apply sortset_In. exact Hb.
Qed.

Lemma sortset_length : forall n l, NoDup l ->
  (forall y, In y l -> (y < n)%nat) -> length (sortset n l) = length l.
Proof.
  intros n l Hnd Hb. symmetry.
  apply Permutation_length. apply sortset_perm; assumption.
Qed.

Lemma relab_std_set : forall n l, NoDup l -> (forall y, In y l -> (y < n)%nat) ->
  relab (sortset n l) (std l) = l.
Proof.
  intros n l Hnd Hb. apply relab_std;
    [apply sortset_incr | apply sortset_nodup | apply sortset_perm; assumption].
Qed.

Lemma std_bound_sortset : forall n l, NoDup l ->
  (forall y, In y l -> (y < n)%nat) ->
  forall x, In x (std l) -> (x < length (sortset n l))%nat.
Proof.
  intros n l Hnd Hb x Hx. rewrite (sortset_length n l Hnd Hb).
  destruct (std_is_perm l Hnd) as [_ [_ Hbb]]. apply Hbb. exact Hx.
Qed.

Theorem std_132 : forall n l, NoDup l -> (forall y, In y l -> (y < n)%nat) ->
  (contains_132 (std l) <-> contains_132 l).
Proof.
  intros n l Hnd Hb.
  rewrite <- (relab_std_set n l Hnd Hb) at 2.
  symmetry. apply relab_132;
    [apply sortset_incr | apply std_bound_sortset; assumption].
Qed.

Theorem std_213 : forall n l, NoDup l -> (forall y, In y l -> (y < n)%nat) ->
  (contains_213 (std l) <-> contains_213 l).
Proof.
  intros n l Hnd Hb.
  rewrite <- (relab_std_set n l Hnd Hb) at 2.
  symmetry. apply relab_213;
    [apply sortset_incr | apply std_bound_sortset; assumption].
Qed.

Theorem std_1324 : forall n l, NoDup l -> (forall y, In y l -> (y < n)%nat) ->
  (contains_1324 (std l) <-> contains_1324 l).
Proof.
  intros n l Hnd Hb.
  rewrite <- (relab_std_set n l Hnd Hb) at 2.
  symmetry. apply relab_1324;
    [apply sortset_incr | apply std_bound_sortset; assumption].
Qed.

(* Standardisation commutes with a value cut: the rank of an entry below the
   cut counts only entries below the cut, and the rank of one above it counts
   the whole lower cell first. *)

Lemma length_filter_mono : forall (P Q : nat -> bool) l,
  (forall x, P x = true -> Q x = true) ->
  (length (filter P l) <= length (filter Q l))%nat.
Proof.
  intros P Q l H. induction l as [|a l IH]; cbn [filter]; [lia|].
  destruct (P a) eqn:E1; destruct (Q a) eqn:E2; cbn [length]; try lia.
  exfalso. rewrite (H a E1) in E2. discriminate.
Qed.

Lemma rankin_cut : forall n L x, (x <= n)%nat ->
  rankin L x = rankin (locell n L) x.
Proof.
  intros n L x Hx. unfold rankin, locell. f_equal.
  rewrite (filter_filter nat (fun y => Nat.ltb y n) (fun y => Nat.ltb y x) L).
  apply filter_ext_gen. intro y.
  destruct (Nat.ltb_spec y n); destruct (Nat.ltb_spec y x);
    solve [reflexivity | exfalso; lia].
Qed.

Lemma cell_split_perm : forall n L,
  Permutation L (hicell n L ++ locell n L).
Proof.
  intros n L. unfold hicell, locell.
  assert (Q := perm_filter_split (fun x => Nat.leb n x) L). cbn beta in Q.
  assert (E : filter (fun x => negb (Nat.leb n x)) L
              = filter (fun x => Nat.ltb x n) L)
    by (apply filter_ext_gen; intro x; apply negb_leb_ltb).
  rewrite E in Q. exact Q.
Qed.

Lemma rankin_cut_hi : forall n L x, (n <= x)%nat ->
  rankin L x = (length (locell n L) + rankin (hicell n L) x)%nat.
Proof.
  intros n L x Hx. unfold rankin.
  assert (Hsplit : length (filter (fun y => Nat.ltb y x) L)
    = (length (filter (fun y => Nat.ltb y x) (hicell n L))
       + length (filter (fun y => Nat.ltb y x) (locell n L)))%nat).
  { rewrite <- len_app, <- filter_app.
    apply perm_filter_length. apply cell_split_perm. }
  assert (Hlo : filter (fun y => Nat.ltb y x) (locell n L) = locell n L).
  { apply filter_all_gen. intros y Hy.
    assert (Hy2 : (y < n)%nat).
    { unfold locell in Hy. apply filter_In in Hy. destruct Hy as [_ Hy].
      apply Nat.ltb_lt. exact Hy. }
    apply Nat.ltb_lt. lia. }
  rewrite Hsplit, Hlo. lia.
Qed.

Lemma std_cut_test : forall n L x, In x L ->
  (Nat.ltb (rankin L x) (length (locell n L)) = Nat.ltb x n).
Proof.
  intros n L x Hx.
  destruct (Nat.ltb_spec x n) as [Hlt|Hge].
  - assert (Hin : In x (locell n L))
      by (unfold locell; apply filter_In; split;
          [exact Hx | apply Nat.ltb_lt; exact Hlt]).
    rewrite (rankin_cut n L x ltac:(lia)).
    destruct (Nat.ltb_spec (rankin (locell n L) x) (length (locell n L)));
      [reflexivity |].
    exfalso. assert (K := rankin_lt_length (locell n L) x Hin). lia.
  - rewrite (rankin_cut_hi n L x Hge).
    destruct (Nat.ltb_spec (length (locell n L) + rankin (hicell n L) x)
                           (length (locell n L)));
      [exfalso; lia | reflexivity].
Qed.

Theorem std_locell : forall n L, NoDup L ->
  locell (length (locell n L)) (std L) = std (locell n L).
Proof.
  intros n L Hnd. unfold locell at 1, std.
  rewrite <- (map_filter_comm (rankin L)
                (fun y => Nat.ltb y (length (locell n L))) L).
  rewrite (filter_ext_in_nat
             (fun x => Nat.ltb (rankin L x) (length (locell n L)))
             (fun x => Nat.ltb x n) L
             (fun x Hx => std_cut_test n L x Hx)).
  unfold std. apply map_ext_in. intros x Hx.
  assert (Hx2 : (x < n)%nat).
  { unfold locell in Hx. apply filter_In in Hx. destruct Hx as [_ Hx].
    apply Nat.ltb_lt. exact Hx. }
  apply (rankin_cut n L x). lia.
Qed.

Theorem std_hicell : forall n L, NoDup L ->
  hicell (length (locell n L)) (std L)
  = map (fun z => (z + length (locell n L))%nat) (std (hicell n L)).
Proof.
  intros n L Hnd. unfold hicell at 1, std.
  rewrite <- (map_filter_comm (rankin L)
                (fun y => Nat.leb (length (locell n L)) y) L).
  rewrite (filter_ext_in_nat
             (fun x => Nat.leb (length (locell n L)) (rankin L x))
             (fun x => Nat.leb n x) L).
  - unfold std. rewrite map_map. apply map_ext_in. intros x Hx.
    assert (Hx2 : (n <= x)%nat).
    { unfold hicell in Hx. apply filter_In in Hx. destruct Hx as [_ Hx].
      apply Nat.leb_le. exact Hx. }
    rewrite (rankin_cut_hi n L x Hx2). lia.
  - intros x Hx. assert (K := std_cut_test n L x Hx). natb.
Qed.

(* ------------------------------------------------------------------ *)
(* Balanced trominoes as gridded permutations of [0,3m).  The dividers sit at
   position 2m and value 2m, so the three cells are

     A = positions < 2m, values >= 2m        upper left,  avoids 213
     B = positions < 2m, values < 2m         lower left,  avoids 132
     C = positions >= 2m, values < 2m        lower right, avoids 213

   and the fourth cell, positions >= 2m with values >= 2m, is empty.  That last
   condition is the hypothesis of tromino_fibre, and it forces the cell sizes:
   the m positions at or past 2m all carry values below 2m, so C has m points
   and the m values at or above 2m all sit before 2m, so A has m points. *)

Definition trominob (m : nat) (w : list nat) : bool :=
  andb (andb (forallb (fun x => Nat.ltb x (2 * m)) (skipn (2 * m) w))
             (negb (contains132b (locell (2 * m) (firstn (2 * m) w)))))
       (andb (negb (contains213b (hicell (2 * m) (firstn (2 * m) w))))
             (negb (contains213b (skipn (2 * m) w)))).

Definition trominoes (m : nat) : list (list nat) :=
  filter (trominob m) (gen (3 * m)).

Definition Tromino (m : nat) : nat := length (trominoes m).

Theorem trominoes_spec : forall m w,
  In w (trominoes m) <->
  (is_perm w (3 * m) /\ ~ contains_1324 w
   /\ (forall x, In x (skipn (2 * m) w) -> (x < 2 * m)%nat)
   /\ ~ contains_132 (locell (2 * m) (firstn (2 * m) w))
   /\ ~ contains_213 (hicell (2 * m) (firstn (2 * m) w))
   /\ ~ contains_213 (skipn (2 * m) w)).
Proof.
  intros m w. unfold trominoes. rewrite filter_In. split.
  - intros [Hg Ht]. apply gen_spec in Hg. destruct Hg as [Hp Hav].
    unfold trominob in Ht.
    apply andb_true_iff in Ht. destruct Ht as [Ht1 Ht2].
    apply andb_true_iff in Ht1. destruct Ht1 as [He Hb].
    apply andb_true_iff in Ht2. destruct Ht2 as [Ha Hc].
    apply negb_true_iff in Hb. apply negb_true_iff in Ha.
    apply negb_true_iff in Hc.
    split; [exact Hp | split; [exact Hav | split; [| split; [| split]]]].
    + intros x Hx. rewrite forallb_forall in He.
      apply Nat.ltb_lt. apply He. exact Hx.
    + intro C. apply contains132b_spec in C. rewrite C in Hb. discriminate.
    + intro C. apply contains213b_spec in C. rewrite C in Ha. discriminate.
    + intro C. apply contains213b_spec in C. rewrite C in Hc. discriminate.
  - intros [Hp [Hav [He [Hb [Ha Hc]]]]]. split.
    + apply gen_spec. split; [exact Hp | exact Hav].
    + unfold trominob. apply andb_true_iff. split; apply andb_true_iff; split.
      * apply forallb_forall. intros x Hx. apply Nat.ltb_lt. apply He. exact Hx.
      * apply negb_true_iff.
        destruct (contains132b (locell (2 * m) (firstn (2 * m) w))) eqn:E;
          [| reflexivity].
        exfalso. apply Hb. apply contains132b_spec. exact E.
      * apply negb_true_iff.
        destruct (contains213b (hicell (2 * m) (firstn (2 * m) w))) eqn:E;
          [| reflexivity].
        exfalso. apply Ha. apply contains213b_spec. exact E.
      * apply negb_true_iff.
        destruct (contains213b (skipn (2 * m) w)) eqn:E; [| reflexivity].
        exfalso. apply Hc. apply contains213b_spec. exact E.
Qed.

Theorem trominoes_nodup : forall m, NoDup (trominoes m).
Proof. intro m. unfold trominoes. apply NoDup_filter. apply gen_nodup. Qed.

(* The upper cell of a tromino is the whole of its high part, because the
   fourth cell is empty; that fixes the three cell sizes at m. *)

Lemma tromino_hicell_left : forall m w,
  (forall x, In x (skipn (2 * m) w) -> (x < 2 * m)%nat) ->
  hicell (2 * m) (firstn (2 * m) w) = hicell (2 * m) w.
Proof.
  intros m w He. unfold hicell.
  transitivity (filter (fun x => Nat.leb (2 * m) x)
                       (firstn (2 * m) w ++ skipn (2 * m) w)).
  - rewrite filter_app.
    rewrite (filter_all_false (fun x => Nat.leb (2 * m) x) (skipn (2 * m) w)).
    + rewrite app_nil_r. reflexivity.
    + intros y Hy. assert (Hy2 := He y Hy).
      destruct (Nat.leb_spec (2 * m) y); [exfalso; lia | reflexivity].
  - rewrite firstn_skipn. reflexivity.
Qed.

Lemma tromino_cellsizes : forall m w,
  is_perm w (3 * m) ->
  (forall x, In x (skipn (2 * m) w) -> (x < 2 * m)%nat) ->
  length (hicell (2 * m) (firstn (2 * m) w)) = m
  /\ length (locell (2 * m) (firstn (2 * m) w)) = m.
Proof.
  intros m w Hp He.
  assert (Hlw : length w = (3 * m)%nat) by av.
  assert (HL : length (firstn (2 * m) w) = (2 * m)%nat)
    by (rewrite length_firstn, Hlw; lia).
  assert (Hhi : length (hicell (2 * m) (firstn (2 * m) w)) = m).
  { rewrite (tromino_hicell_left m w He). unfold hicell.
    rewrite (count_ge_in_perm w (3 * m) (2 * m) Hp ltac:(lia)). lia. }
  split; [exact Hhi|].
  assert (K := Permutation_length (cell_split_perm (2 * m) (firstn (2 * m) w))).
  rewrite len_app, HL, Hhi in K. lia.
Qed.

Theorem tromino_vdomino : forall m w,
  In w (trominoes m) -> In (std (firstn (2 * m) w)) (dominoes m m).
Proof.
  intros m w Hw. apply trominoes_spec in Hw.
  destruct Hw as [Hp [Hav [He [Hb [Ha Hc]]]]].
  assert (Hlw : length w = (3 * m)%nat) by av.
  assert (Hndw : NoDup w) by av.
  assert (Hbw : forall x, In x w -> (x < 3 * m)%nat)
    by av.
  assert (HL : length (firstn (2 * m) w) = (2 * m)%nat)
    by (rewrite length_firstn, Hlw; lia).
  assert (HndL : NoDup (firstn (2 * m) w)) by (apply NoDup_firstn; exact Hndw).
  assert (HbL : forall y, In y (firstn (2 * m) w) -> (y < 3 * m)%nat)
    by (intros y Hy; apply Hbw; apply (in_firstn_w w (2 * m)); exact Hy).
  destruct (tromino_cellsizes m w Hp He) as [Hhi Hlo].
  assert (HndB : NoDup (locell (2 * m) (firstn (2 * m) w)))
    by (unfold locell; apply NoDup_filter; exact HndL).
  assert (HbB : forall y, In y (locell (2 * m) (firstn (2 * m) w)) ->
                (y < 3 * m)%nat).
  { intros y Hy. unfold locell in Hy. apply filter_In in Hy.
    apply HbL. exact (proj1 Hy). }
  assert (HndA : NoDup (hicell (2 * m) (firstn (2 * m) w)))
    by (unfold hicell; apply NoDup_filter; exact HndL).
  assert (HbA : forall y, In y (hicell (2 * m) (firstn (2 * m) w)) ->
                (y < 3 * m)%nat).
  { intros y Hy. unfold hicell in Hy. apply filter_In in Hy.
    apply HbL. exact (proj1 Hy). }
  apply dominoes_spec.
  assert (Elo : locell m (std (firstn (2 * m) w))
                = std (locell (2 * m) (firstn (2 * m) w))).
  { assert (K := std_locell (2 * m) (firstn (2 * m) w) HndL).
    rewrite Hlo in K. exact K. }
  assert (Ehi : hicell m (std (firstn (2 * m) w))
                = map (fun z => (z + m)%nat)
                      (std (hicell (2 * m) (firstn (2 * m) w)))).
  { assert (K := std_hicell (2 * m) (firstn (2 * m) w) HndL).
    rewrite Hlo in K. exact K. }
  split; [| split; [| split]].
  - assert (K := std_is_perm (firstn (2 * m) w) HndL).
    rewrite HL in K. replace (m + m)%nat with (2 * m)%nat by lia. exact K.
  - intro C. apply (proj1 (std_1324 (3 * m) (firstn (2 * m) w) HndL HbL)) in C.
    apply Hav. apply (subseq_1324 (firstn (2 * m) w) w).
    + apply firstn_subseq.
    + exact C.
  - rewrite Elo. intro C.
    apply Hb. apply (proj1 (std_132 (3 * m) _ HndB HbB)). exact C.
  - rewrite Ehi. intro C.
    apply Ha. apply (proj1 (std_213 (3 * m) _ HndA HbA)).
    apply (contains_213_addc m). exact C.
Qed.

(* The transpose of a word split by position.  Inverting exchanges the two
   coordinates, so the low cell of the inverse of B ++ C is the inverse of the
   pattern of B: reading the positions of B's values in increasing value order
   is exactly what pinv (std B) does. *)

Lemma idx_app_in : forall x l1 l2, In x l1 -> idx x (l1 ++ l2) = idx x l1.
Proof.
  intros x l1. induction l1 as [|a l1 IH]; intros l2 H; [contradiction|].
  cbn [app idx]. destruct (Nat.eqb_spec a x) as [E|E]; [reflexivity|].
  f_equal. apply IH. destruct H as [H|H]; [contradiction | exact H].
Qed.

Lemma idx_app_notin : forall x l1 l2, ~ In x l1 ->
  idx x (l1 ++ l2) = (length l1 + idx x l2)%nat.
Proof.
  intros x l1. induction l1 as [|a l1 IH]; intros l2 H; [reflexivity|].
  cbn [app idx length]. destruct (Nat.eqb_spec a x) as [E|E].
  - exfalso. apply H. left. exact E.
  - assert (K := IH l2 ltac:(intro C; apply H; right; exact C)). lia.
Qed.

Lemma std_length : forall l, length (std l) = length l.
Proof. intro l. unfold std. apply len_map_gen. Qed.

Lemma std_nth_rank : forall B j, (j < length B)%nat ->
  nth j (std B) 0%nat = rankin B (nth j B 0%nat).
Proof.
  intros B j Hj. unfold std. apply map_nth_def. exact Hj.
Qed.

Lemma idx_of_rank : forall B n i, NoDup B ->
  (forall y, In y B -> (y < n)%nat) -> (i < length B)%nat ->
  idx i (std B) = idx (nth i (sortset n B) 0%nat) B.
Proof.
  intros B n i Hnd Hb Hi.
  assert (HS : Permutation B (sortset n B)) by (apply sortset_perm; assumption).
  assert (HSlen : length (sortset n B) = length B)
    by (apply sortset_length; assumption).
  set (x := nth i (sortset n B) 0%nat).
  assert (HxS : In x (sortset n B)) by (unfold x; apply nth_In; lia).
  assert (HxB : In x B)
    by (apply (Permutation_in _ (Permutation_sym HS)); exact HxS).
  set (j := idx x B).
  assert (Hj : (j < length B)%nat) by (unfold j; apply idx_lt; exact HxB).
  assert (Ej : nth j B 0%nat = x) by (unfold j; apply idx_nth; exact HxB).
  assert (Erank : rankin B x = i).
  { rewrite (rankin_perm B (sortset n B) HS x).
    unfold x. apply incr_rank;
      [apply sortset_incr | apply sortset_nodup | lia]. }
  assert (Estd : nth j (std B) 0%nat = i)
    by (rewrite (std_nth_rank B j Hj), Ej; exact Erank).
  assert (Hndstd : NoDup (std B))
    by (destruct (std_is_perm B Hnd) as [_ [H _]]; exact H).
  assert (Hlenstd : length (std B) = length B) by apply len_map_gen.
  rewrite <- Estd. rewrite (nth_idx (std B) Hndstd j ltac:(lia)). reflexivity.
Qed.

Theorem locell_pinv_prefix : forall B C n,
  is_perm (B ++ C) n ->
  locell (length B) (pinv (B ++ C)) = pinv (std B).
Proof.
  intros B C n Hp. assert (Hp' := Hp).
  destruct Hp as [Hlen [Hnd Hbnd]].
  assert (HndB : NoDup B) by (apply (NoDup_app_l B C); exact Hnd).
  assert (HbB : forall y, In y B -> (y < n)%nat)
    by (intros y Hy; apply Hbnd; apply in_or_app; left; exact Hy).
  assert (Hmem : forall t, (t < n)%nat -> In t (B ++ C))
    by (intros t Ht; apply (perm_full (B ++ C) n Hp'); exact Ht).
  (* the values whose position in B ++ C lies in the prefix are exactly B's *)
  assert (Hsel : filter (fun t => Nat.ltb (idx t (B ++ C)) (length B))
                        (seq 0 n)
                 = sortset n B).
  { apply incr_eq.
    - apply incr_filter. apply incr_seq.
    - apply sortset_incr.
    - apply NoDup_filter. apply seq_NoDup.
    - apply sortset_nodup.
    - intro t. rewrite filter_In, in_seq.
      rewrite (sortset_In n B t HbB). split.
      + intros [Ht Hlt]. apply Nat.ltb_lt in Hlt.
        destruct (in_dec Nat.eq_dec t B) as [Hin|Hin]; [exact Hin|].
        exfalso. rewrite (idx_app_notin t B C Hin) in Hlt. lia.
      + intro Hin. split; [split; [lia | apply HbB; exact Hin]|].
        apply Nat.ltb_lt. rewrite (idx_app_in t B C Hin).
        apply idx_lt. exact Hin. }
  unfold locell, pinv at 1. rewrite Hlen.
  rewrite <- (map_filter_comm (fun t => idx t (B ++ C))
                (fun x => Nat.ltb x (length B)) (seq 0 n)).
  rewrite Hsel.
  (* on those values the position in B ++ C is the position in B *)
  rewrite (map_ext_in (fun t => idx t (B ++ C)) (fun t => idx t B)
             (sortset n B)).
  2:{ intros t Ht. apply idx_app_in.
      apply (proj1 (sortset_In n B t HbB)). exact Ht. }
  (* and reading them in increasing value order is pinv of the pattern *)
  assert (HSlen : length (sortset n B) = length B)
    by (apply sortset_length; assumption).
  unfold pinv. rewrite std_length.
  rewrite <- (map_nth_seq nat 0%nat (sortset n B)) at 1.
  rewrite HSlen, map_map.
  apply map_ext_in. intros i Hi. apply in_seq in Hi.
  symmetry. apply idx_of_rank; [exact HndB | exact HbB | lia].
Qed.

Theorem hicell_pinv_suffix : forall B C n,
  is_perm (B ++ C) n ->
  hicell (length B) (pinv (B ++ C))
  = map (fun z => (length B + z)%nat) (pinv (std C)).
Proof.
  intros B C n Hp. assert (Hp' := Hp).
  destruct Hp as [Hlen [Hnd Hbnd]].
  assert (HndC : NoDup C) by (apply (nodup_app_r B C); exact Hnd).
  assert (HbC : forall y, In y C -> (y < n)%nat)
    by (intros y Hy; apply Hbnd; apply in_or_app; right; exact Hy).
  assert (Hdisj : forall t, In t C -> ~ In t B)
    by (intros t Ht Hb; exact (nodup_app_disjoint B C t Hnd Hb Ht)).
  assert (Hsel : filter (fun t => Nat.leb (length B) (idx t (B ++ C)))
                        (seq 0 n)
                 = sortset n C).
  { apply incr_eq.
    - apply incr_filter. apply incr_seq.
    - apply sortset_incr.
    - apply NoDup_filter. apply seq_NoDup.
    - apply sortset_nodup.
    - intro t. rewrite filter_In, in_seq.
      rewrite (sortset_In n C t HbC). split.
      + intros [Ht Hge]. apply Nat.leb_le in Hge.
        destruct (in_dec Nat.eq_dec t B) as [Hin|Hin].
        * exfalso. rewrite (idx_app_in t B C Hin) in Hge.
          assert (K := idx_lt B t Hin). lia.
        * assert (Hin2 : In t (B ++ C))
            by (apply (perm_full (B ++ C) n Hp'); lia).
          apply in_app_or in Hin2. destruct Hin2 as [Hc|Hc];
            [contradiction | exact Hc].
      + intro Hin. split; [split; [lia | apply HbC; exact Hin]|].
        apply Nat.leb_le. rewrite (idx_app_notin t B C (Hdisj t Hin)). lia. }
  unfold hicell, pinv at 1. rewrite Hlen.
  rewrite <- (map_filter_comm (fun t => idx t (B ++ C))
                (fun x => Nat.leb (length B) x) (seq 0 n)).
  rewrite Hsel.
  rewrite (map_ext_in (fun t => idx t (B ++ C))
             (fun t => (length B + idx t C)%nat) (sortset n C)).
  2:{ intros t Ht. apply idx_app_notin. apply Hdisj.
      apply (proj1 (sortset_In n C t HbC)). exact Ht. }
  assert (HSlen : length (sortset n C) = length C)
    by (apply sortset_length; assumption).
  unfold pinv. rewrite std_length.
  rewrite <- (map_nth_seq nat 0%nat (sortset n C)) at 1.
  rewrite HSlen, !map_map.
  apply map_ext_in. intros i Hi. apply in_seq in Hi.
  f_equal. symmetry. apply idx_of_rank; [exact HndC | exact HbC | lia].
Qed.

(* Av(213) is inverse closed too, by the same transport as pinv_132. *)
Theorem pinv_213 : forall u m, is_perm u m ->
  contains_213 u -> contains_213 (pinv u).
Proof.
  intros u m Hp [p [q [r H]]]. unfold has_213_at in H.
  destruct H as [Hpq [Hqr [Hr [Hqp Hpr]]]].
  assert (Hlen : length u = m) by av.
  assert (Hbnd : forall t, (t < m)%nat -> (nth t u 0%nat < m)%nat).
  { intros t Ht. destruct Hp as [_ [_ Hb]]. apply Hb. apply nth_In. lia. }
  exists (nth q u 0%nat), (nth p u 0%nat), (nth r u 0%nat).
  unfold has_213_at.
  rewrite (pinv_nth_nth u m Hp p ltac:(lia)).
  rewrite (pinv_nth_nth u m Hp q ltac:(lia)).
  rewrite (pinv_nth_nth u m Hp r ltac:(lia)).
  rewrite pinv_length.
  assert (Hb := Hbnd r ltac:(lia)).
  repeat split; lia.
Qed.

Corollary pinv_avoids_213 : forall u m, is_perm u m ->
  (~ contains_213 u <-> ~ contains_213 (pinv u)).
Proof.
  intros u m Hp. split; intros H C.
  - apply H. rewrite <- (pinv_involutive u m Hp).
    apply (pinv_213 (pinv u) m); [apply (pinv_perm u m); exact Hp | exact C].
  - apply H. apply (pinv_213 u m Hp). exact C.
Qed.

(* The low part of a tromino, as a word: the shared cell followed by the cell
   beside it, because every point past the column divider lies below the row
   divider. *)
Lemma tromino_locell_split : forall m w,
  (forall x, In x (skipn (2 * m) w) -> (x < 2 * m)%nat) ->
  locell (2 * m) w
  = locell (2 * m) (firstn (2 * m) w) ++ skipn (2 * m) w.
Proof.
  intros m w He. unfold locell.
  transitivity (filter (fun x => Nat.ltb x (2 * m))
                       (firstn (2 * m) w ++ skipn (2 * m) w)).
  - rewrite firstn_skipn. reflexivity.
  - rewrite filter_app. f_equal.
    apply filter_all_gen. intros y Hy. apply Nat.ltb_lt. apply He. exact Hy.
Qed.

Lemma tromino_low_perm : forall m w,
  is_perm w (3 * m) ->
  (forall x, In x (skipn (2 * m) w) -> (x < 2 * m)%nat) ->
  is_perm (locell (2 * m) w) (2 * m).
Proof.
  intros m w Hp He.
  assert (Hlw : length w = (3 * m)%nat) by av.
  assert (Hndw : NoDup w) by av.
  assert (Hhi : length (hicell (2 * m) w) = m).
  { unfold hicell. rewrite (count_ge_in_perm w (3 * m) (2 * m) Hp ltac:(lia)).
    lia. }
  assert (K := Permutation_length (cell_split_perm (2 * m) w)).
  rewrite len_app, Hlw, Hhi in K.
  split; [lia | split].
  - unfold locell. apply NoDup_filter. exact Hndw.
  - intros x Hx. unfold locell in Hx. apply filter_In in Hx.
    destruct Hx as [_ Hx]. apply Nat.ltb_lt. exact Hx.
Qed.

Lemma tromino_vlocell : forall m w,
  In w (trominoes m) ->
  locell m (std (firstn (2 * m) w)) = std (locell (2 * m) (firstn (2 * m) w)).
Proof.
  intros m w Hw. assert (Hw' := Hw). apply trominoes_spec in Hw'.
  destruct Hw' as [Hp [Hav [He [Hb [Ha Hc]]]]].
  assert (Hndw : NoDup w) by av.
  assert (HndL : NoDup (firstn (2 * m) w)) by (apply NoDup_firstn; exact Hndw).
  destruct (tromino_cellsizes m w Hp He) as [_ Hlo].
  assert (K := std_locell (2 * m) (firstn (2 * m) w) HndL).
  rewrite Hlo in K. exact K.
Qed.

Theorem tromino_hdomino : forall m w,
  In w (trominoes m) -> In (pinv (locell (2 * m) w)) (dominoes m m).
Proof.
  intros m w Hw. assert (Hw' := Hw). apply trominoes_spec in Hw'.
  destruct Hw' as [Hp [Hav [He [Hb [Ha Hc]]]]].
  assert (Hlw : length w = (3 * m)%nat) by av.
  assert (Hndw : NoDup w) by av.
  assert (Hbw : forall x, In x w -> (x < 3 * m)%nat)
    by av.
  assert (HndL : NoDup (firstn (2 * m) w)) by (apply NoDup_firstn; exact Hndw).
  destruct (tromino_cellsizes m w Hp He) as [_ Hlo].
  assert (Hsplit := tromino_locell_split m w He).
  assert (Hlp := tromino_low_perm m w Hp He).
  rewrite Hsplit in Hlp.
  assert (HndB : NoDup (locell (2 * m) (firstn (2 * m) w)))
    by (unfold locell; apply NoDup_filter; exact HndL).
  assert (HbB : forall y, In y (locell (2 * m) (firstn (2 * m) w)) ->
                (y < 3 * m)%nat).
  { intros y Hy. unfold locell in Hy. apply filter_In in Hy.
    apply Hbw. apply (in_firstn_w w (2 * m)). exact (proj1 Hy). }
  assert (HndC : NoDup (skipn (2 * m) w)) by (apply NoDup_skipn; exact Hndw).
  assert (HbC : forall y, In y (skipn (2 * m) w) -> (y < 3 * m)%nat)
    by (intros y Hy; apply Hbw; apply (in_skipn_w w (2 * m)); exact Hy).
  assert (HlC : length (skipn (2 * m) w) = m)
    by (rewrite length_skipn, Hlw; lia).
  assert (HpB : is_perm (std (locell (2 * m) (firstn (2 * m) w))) m).
  { assert (K := std_is_perm _ HndB). rewrite Hlo in K. exact K. }
  assert (HpC : is_perm (std (skipn (2 * m) w)) m).
  { assert (K := std_is_perm _ HndC). rewrite HlC in K. exact K. }
  apply dominoes_spec. rewrite Hsplit.
  assert (Elo := locell_pinv_prefix _ _ _ Hlp).
  assert (Ehi := hicell_pinv_suffix _ _ _ Hlp).
  rewrite Hlo in Elo, Ehi.
  split; [| split; [| split]].
  - replace (m + m)%nat with (2 * m)%nat by lia.
    apply (pinv_perm _ (2 * m)). exact Hlp.
  - apply (proj1 (pinv_avoids_1324 _ _ Hlp)).
    intro C. apply Hav. apply (subseq_1324 (locell (2 * m) w) w).
    + unfold locell. apply filter_subseq.
    + rewrite Hsplit. exact C.
  - rewrite Elo. apply (proj1 (pinv_avoids_132 _ _ HpB)).
    intro C. apply Hb. apply (proj1 (std_132 (3 * m) _ HndB HbB)). exact C.
  - rewrite Ehi.
    assert (Ec : map (fun z => (m + z)%nat) (pinv (std (skipn (2 * m) w)))
                 = map (fun z => (z + m)%nat) (pinv (std (skipn (2 * m) w))))
      by (apply map_ext; intro z; lia).
    rewrite Ec. intro C.
    apply (proj1 (contains_213_addc m (pinv (std (skipn (2 * m) w))))) in C.
    assert (Hpp : is_perm (pinv (std (skipn (2 * m) w))) m)
      by (apply (pinv_perm _ m); exact HpC).
    assert (C2 : contains_213 (pinv (pinv (std (skipn (2 * m) w)))))
      by (apply (pinv_213 _ m Hpp); exact C).
    rewrite (pinv_involutive _ m HpC) in C2.
    apply Hc. apply (proj1 (std_213 (3 * m) _ HndC HbC)). exact C2.
Qed.

Theorem tromino_glue : forall m w,
  In w (trominoes m) ->
  locell m (pinv (locell (2 * m) w))
  = pinv (locell m (std (firstn (2 * m) w))).
Proof.
  intros m w Hw. assert (Hw' := Hw). apply trominoes_spec in Hw'.
  destruct Hw' as [Hp [Hav [He [Hb [Ha Hc]]]]].
  destruct (tromino_cellsizes m w Hp He) as [_ Hlo].
  assert (Hsplit := tromino_locell_split m w He).
  assert (Hlp := tromino_low_perm m w Hp He).
  rewrite Hsplit in Hlp.
  assert (Elo := locell_pinv_prefix _ _ _ Hlp).
  rewrite Hlo in Elo. rewrite Hsplit, Elo.
  rewrite (tromino_vlocell m w Hw). reflexivity.
Qed.

(* The pair a tromino determines: its vertical domino and the transpose of its
   horizontal one, glued along inverse copies of the shared cell. *)
Definition tgpair (m : nat) (w : list nat) : list nat * list nat :=
  (std (firstn (2 * m) w), pinv (locell (2 * m) w)).

Theorem tromino_in_glued : forall m w,
  In w (trominoes m) -> In (tgpair m w) (glued m).
Proof.
  intros m w Hw. unfold glued, tgpair. apply filter_In. split.
  - apply in_prod; [apply tromino_vdomino | apply tromino_hdomino]; exact Hw.
  - cbn [fst snd].
    destruct (list_eq_dec Nat.eq_dec
                (locell m (pinv (locell (2 * m) w)))
                (pinv (locell m (std (firstn (2 * m) w))))) as [E|E];
      [reflexivity | contradiction (E (tromino_glue m w Hw))].
Qed.

Lemma tromino_firstn_mem : forall m w x,
  In w (trominoes m) ->
  (In x (firstn (2 * m) w)
   <-> ((2 * m <= x)%nat /\ (x < 3 * m)%nat)
       \/ In x (locell (2 * m) (firstn (2 * m) w))).
Proof.
  intros m w x Hw. apply trominoes_spec in Hw.
  destruct Hw as [Hp [Hav [He [Hb [Ha Hc]]]]].
  assert (Hbw : forall y, In y w -> (y < 3 * m)%nat)
    by av.
  split.
  - intro Hx.
    assert (Hxw : In x w) by (apply (in_firstn_w w (2 * m)); exact Hx).
    destruct (Nat.le_gt_cases (2 * m) x) as [K|K].
    + left. split; [exact K | apply Hbw; exact Hxw].
    + right. unfold locell. apply filter_In.
      split; [exact Hx | apply Nat.ltb_lt; exact K].
  - intros [[K1 K2] | Hx].
    + assert (Hxw : In x w) by (apply (perm_full w (3 * m) Hp); exact K2).
      destruct (in_firstn_or_skipn w (2 * m) x Hxw) as [Hf|Hs]; [exact Hf|].
      exfalso. assert (K := He x Hs). lia.
    + unfold locell in Hx. apply filter_In in Hx. exact (proj1 Hx).
Qed.

Theorem tgpair_inj : forall m w1 w2,
  In w1 (trominoes m) -> In w2 (trominoes m) ->
  tgpair m w1 = tgpair m w2 -> w1 = w2.
Proof.
  intros m w1 w2 H1 H2 He. unfold tgpair in He. injection He as Hstd Hpinv.
  assert (S1 := H1). apply trominoes_spec in S1.
  destruct S1 as [Hp1 [Hav1 [He1 [Hb1 [Ha1 Hc1]]]]].
  assert (S2 := H2). apply trominoes_spec in S2.
  destruct S2 as [Hp2 [Hav2 [He2 [Hb2 [Ha2 Hc2]]]]].
  assert (Hlw1 : length w1 = (3 * m)%nat) by av.
  assert (Hlw2 : length w2 = (3 * m)%nat) by av.
  assert (Hnd1 : NoDup w1) by av.
  assert (Hnd2 : NoDup w2) by av.
  (* the two low parts agree, hence the shared cell and the cell beside it *)
  assert (Hlow : locell (2 * m) w1 = locell (2 * m) w2).
  { apply (pinv_inj _ _ (2 * m));
      [apply tromino_low_perm; assumption | apply tromino_low_perm; assumption
       | exact Hpinv]. }
  rewrite (tromino_locell_split m w1 He1),
          (tromino_locell_split m w2 He2) in Hlow.
  destruct (tromino_cellsizes m w1 Hp1 He1) as [_ Hlo1].
  destruct (tromino_cellsizes m w2 Hp2 He2) as [_ Hlo2].
  destruct (app_split_eq _ _ _ _ ltac:(rewrite Hlo1, Hlo2; reflexivity) Hlow)
    as [HB HC].
  (* the two left columns hold the same values, so equal standardisations
     force them equal *)
  assert (Hperm : Permutation (firstn (2 * m) w1) (firstn (2 * m) w2)).
  { apply NoDup_Permutation;
      [apply NoDup_firstn; exact Hnd1 | apply NoDup_firstn; exact Hnd2|].
    intro x. rewrite (tromino_firstn_mem m w1 x H1),
                     (tromino_firstn_mem m w2 x H2), HB. reflexivity. }
  assert (Hfst : firstn (2 * m) w1 = firstn (2 * m) w2).
  { apply std_perm_eq; [exact Hperm | apply NoDup_firstn; exact Hnd1 | |
                        exact Hstd].
    rewrite !length_firstn, Hlw1, Hlw2. reflexivity. }
  rewrite <- (firstn_skipn (2 * m) w1), <- (firstn_skipn (2 * m) w2),
          Hfst, HC. reflexivity.
Qed.

(* So the tromino count never exceeds the glued-pair count. *)
Theorem tromino_le_glued : forall m, (Tromino m <= length (glued m))%nat.
Proof.
  intro m. unfold Tromino.
  rewrite <- (len_map_gen _ _ (tgpair m) (trominoes m)).
  apply NoDup_incl_length.
  - apply NoDup_map_inj; [apply trominoes_nodup|].
    intros x y Hx Hy He. exact (tgpair_inj m x y Hx Hy He).
  - intros z Hz. apply in_map_iff in Hz. destruct Hz as [w [Hw Hin]].
    subst z. apply tromino_in_glued. exact Hin.
Qed.

Corollary tromino_le_Tcount : forall m, (Tromino m <= Tcount m)%nat.
Proof. intro m. rewrite Tcount_glued. apply tromino_le_glued. Qed.

(* The rank transport at the low cell, for 1324: an occurrence all of whose
   values lie below the cut is an occurrence of the cut-down word. *)
Lemma locell_1324_pos : forall b w i j k l,
  (i < j)%nat -> (j < k)%nat -> (k < l)%nat -> (l < length w)%nat ->
  (nth i w 0%nat < b)%nat -> (nth j w 0%nat < b)%nat ->
  (nth k w 0%nat < b)%nat -> (nth l w 0%nat < b)%nat ->
  has_1324_at w i j k l ->
  contains_1324 (locell b w).
Proof.
  intros b w i j k l Hij Hjk Hkl Hl Bi Bj Bk Bl H. unfold locell.
  apply (filter_1324 (fun x => Nat.ltb x b) w i j k l);
    [ keep | keep | keep | keep | exact H ].
Qed.

Lemma domino_cellsizes : forall m v,
  In v (dominoes m m) ->
  length (hicell m v) = m /\ length (locell m v) = m.
Proof.
  intros m v Hv. apply dominoes_spec in Hv. destruct Hv as [Hp _].
  assert (Hhi : length (hicell m v) = m).
  { unfold hicell. rewrite (count_ge_in_perm v (m + m) m Hp ltac:(lia)). lia. }
  split; [exact Hhi|].
  assert (K := Permutation_length (cell_split_perm m v)).
  destruct Hp as [Hlen _]. rewrite len_app, Hlen, Hhi in K. lia.
Qed.

(* The word a glued pair builds: the upper cell planted into the mask of v over
   the shared cell taken from h, followed by the cell beside it. *)
Definition tromino_of (m : nat) (p : list nat * list nat) : list nat :=
  mrg (map (fun x => Nat.leb m x) (fst p))
      (map (fun x => (x + m)%nat) (hicell m (fst p)))
      (firstn m (pinv (snd p)))
  ++ skipn m (pinv (snd p)).

(* Shifting every value leaves the pattern alone, and the high cell of a
   permutation of [0,2m) is exactly the values in [m,2m), so relabelling its
   standardisation upward returns it. *)

Lemma rankin_addc : forall c l x,
  rankin (map (fun y => (y + c)%nat) l) (x + c)%nat = rankin l x.
Proof.
  intros c l x. unfold rankin.
  rewrite <- (map_filter_comm (fun y => (y + c)%nat)
                (fun z => Nat.ltb z (x + c)) l).
  rewrite len_map_gen. f_equal.
  apply filter_ext_gen. intro y.
  destruct (Nat.ltb_spec (y + c) (x + c)); destruct (Nat.ltb_spec y x);
    solve [reflexivity | exfalso; lia].
Qed.

Lemma std_addc : forall c u, std (map (fun y => (y + c)%nat) u) = std u.
Proof.
  intros c u. unfold std. rewrite map_map.
  apply map_ext_in. intros x _. apply rankin_addc.
Qed.

Lemma hicell_perm_values : forall n b u, is_perm u n -> (b <= n)%nat ->
  forall x, In x (hicell b u) <-> ((b <= x)%nat /\ (x < n)%nat).
Proof.
  intros n b u Hp Hb x. unfold hicell. rewrite filter_In. split.
  - intros [Hin Hge]. apply Nat.leb_le in Hge.
    split; [exact Hge | destruct Hp as [_ [_ H]]; apply H; exact Hin].
  - intros [H1 H2]. split.
    + apply (perm_full u n Hp). exact H2.
    + apply Nat.leb_le. exact H1.
Qed.

Lemma sortset_hicell : forall m v, is_perm v (2 * m) ->
  sortset (2 * m) (hicell m v) = seq m m.
Proof.
  intros m v Hp.
  assert (Hb : forall y, In y (hicell m v) -> (y < 2 * m)%nat).
  { intros y Hy.
    apply (proj1 (hicell_perm_values (2 * m) m v Hp ltac:(lia) y)) in Hy. lia. }
  apply incr_eq.
  - apply sortset_incr.
  - intros a b Hab Hbb. rewrite length_seq in Hbb.
    rewrite !seq_nth by lia. lia.
  - apply sortset_nodup.
  - apply seq_NoDup.
  - intro x. rewrite (sortset_In (2 * m) (hicell m v) x Hb).
    rewrite (hicell_perm_values (2 * m) m v Hp ltac:(lia) x), in_seq. lia.
Qed.

Lemma relab_seq : forall m u, (forall x, In x u -> (x < m)%nat) ->
  relab (seq m m) u = map (fun t => (m + t)%nat) u.
Proof.
  intros m u Hb. unfold relab. apply map_ext_in. intros t Ht.
  rewrite seq_nth by (apply Hb; exact Ht). reflexivity.
Qed.

Lemma hicell_std_back : forall m v, is_perm v (2 * m) ->
  map (fun z => (z + m)%nat) (std (hicell m v)) = hicell m v.
Proof.
  intros m v Hp.
  assert (Hnd : NoDup (hicell m v))
    by (unfold hicell; apply NoDup_filter; destruct Hp as [_ [H _]]; exact H).
  assert (Hb : forall y, In y (hicell m v) -> (y < 2 * m)%nat).
  { intros y Hy.
    apply (proj1 (hicell_perm_values (2 * m) m v Hp ltac:(lia) y)) in Hy. lia. }
  assert (Hlen : length (hicell m v) = m).
  { rewrite (hicell_perm_length (2 * m) m v Hp ltac:(lia)). lia. }
  assert (Hsb : forall x, In x (std (hicell m v)) -> (x < m)%nat).
  { intros x Hx. destruct (std_is_perm _ Hnd) as [_ [_ Hbb]].
    rewrite <- Hlen. apply Hbb. exact Hx. }
  assert (K := relab_std_set (2 * m) (hicell m v) Hnd Hb).
  rewrite (sortset_hicell m v Hp) in K.
  rewrite (relab_seq m (std (hicell m v)) Hsb) in K.
  rewrite <- K at 2. apply map_ext. intro z. lia.
Qed.

(* Planting the upper cell into the mask of v over a shared cell taken from h:
   the three readings of the result are the two cells and the mask. *)

Lemma mrg_left_spec : forall m v Bl,
  is_perm v (2 * m) -> length Bl = m ->
  (forall y, In y Bl -> (y < 2 * m)%nat) ->
  hicell (2 * m) (mrg (map (fun x => Nat.leb m x) v)
                      (map (fun x => (x + m)%nat) (hicell m v)) Bl)
  = map (fun x => (x + m)%nat) (hicell m v)
  /\ locell (2 * m) (mrg (map (fun x => Nat.leb m x) v)
                         (map (fun x => (x + m)%nat) (hicell m v)) Bl) = Bl
  /\ map (fun x => Nat.leb (2 * m) x)
         (mrg (map (fun x => Nat.leb m x) v)
              (map (fun x => (x + m)%nat) (hicell m v)) Bl)
     = map (fun x => Nat.leb m x) v.
Proof.
  intros m v Bl Hp HlB HbB.
  assert (Hlv : length v = (2 * m)%nat) by av.
  assert (Hhilen : length (hicell m v) = m).
  { rewrite (hicell_perm_length (2 * m) m v Hp ltac:(lia)). lia. }
  assert (HcP : countt (map (fun x => Nat.leb m x) v) = m).
  { rewrite countt_map. exact Hhilen. }
  assert (HlP : length (map (fun x => Nat.leb m x) v) = (2 * m)%nat)
    by (rewrite len_map_gen; exact Hlv).
  assert (H1 : length (map (fun x => (x + m)%nat) (hicell m v))
               = countt (map (fun x => Nat.leb m x) v))
    by (rewrite len_map_gen, Hhilen, HcP; reflexivity).
  assert (H2 : length Bl = (length (map (fun x => Nat.leb m x) v)
                            - countt (map (fun x => Nat.leb m x) v))%nat)
    by (rewrite HlP, HcP, HlB; lia).
  assert (Hhi : forall x, In x (map (fun x => (x + m)%nat) (hicell m v)) ->
                Nat.leb (2 * m) x = true).
  { intros x Hx. apply in_map_iff in Hx. destruct Hx as [y [Hy Hyin]].
    assert (Hy2 := proj1 (proj1 (hicell_perm_values (2 * m) m v Hp
                                   ltac:(lia) y) Hyin)).
    destruct (Nat.leb_spec (2 * m) x); [reflexivity | exfalso; lia]. }
  assert (Hlo : forall y, In y Bl -> Nat.leb (2 * m) y = false).
  { intros y Hy. assert (Hy2 := HbB y Hy).
    destruct (Nat.leb_spec (2 * m) y); [exfalso; lia | reflexivity]. }
  destruct (mrg_spec (fun x => Nat.leb (2 * m) x)
              (map (fun x => Nat.leb m x) v)
              (map (fun x => (x + m)%nat) (hicell m v)) Bl H1 H2 Hhi Hlo)
    as [Ehi [Elo Emask]].
  split; [exact Ehi | split; [| exact Emask]].
  rewrite locell_as_negb. exact Elo.
Qed.

Lemma std_left : forall m v Bl,
  is_perm v (2 * m) -> length Bl = m -> NoDup Bl ->
  (forall y, In y Bl -> (y < 2 * m)%nat) ->
  std Bl = locell m v ->
  std (mrg (map (fun x => Nat.leb m x) v)
           (map (fun x => (x + m)%nat) (hicell m v)) Bl) = v.
Proof.
  intros m v Bl Hp HlB HndB HbB Hstd.
  destruct (mrg_left_spec m v Bl Hp HlB HbB) as [Ehi [Elo Emask]].
  set (L := mrg (map (fun x => Nat.leb m x) v)
                (map (fun x => (x + m)%nat) (hicell m v)) Bl) in *.
  assert (Hlv : length v = (2 * m)%nat) by av.
  assert (Hndv : NoDup v) by av.
  assert (HndA : NoDup (map (fun x => (x + m)%nat) (hicell m v))).
  { apply NoDup_map_inj.
    - unfold hicell. apply NoDup_filter. exact Hndv.
    - intros x y _ _ He. lia. }
  assert (Hperm : Permutation L
                    (map (fun x => (x + m)%nat) (hicell m v) ++ Bl)).
  { assert (Q := perm_filter_split (fun x => Nat.leb (2 * m) x) L).
    cbn beta in Q.
    assert (E1 : filter (fun x => Nat.leb (2 * m) x) L
                 = map (fun x => (x + m)%nat) (hicell m v)) by exact Ehi.
    assert (E2 : filter (fun x => negb (Nat.leb (2 * m) x)) L = Bl).
    { rewrite <- locell_as_negb. exact Elo. }
    rewrite E1, E2 in Q. exact Q. }
  assert (HndL : NoDup L).
  { apply (Permutation_NoDup (Permutation_sym Hperm)).
    apply NoDup_app_disj; [exact HndA | exact HndB |].
    intros z Hz1 Hz2.
    assert (K1 : Nat.leb (2 * m) z = true).
    { apply in_map_iff in Hz1. destruct Hz1 as [y [Hy Hyin]].
      assert (Hy2 := proj1 (proj1 (hicell_perm_values (2 * m) m v Hp
                                     ltac:(lia) y) Hyin)).
      destruct (Nat.leb_spec (2 * m) z); [reflexivity | exfalso; lia]. }
    assert (K2 := HbB z Hz2).
    destruct (Nat.leb_spec (2 * m) z); [lia | discriminate]. }
  assert (HlocL : length (locell (2 * m) L) = m) by (rewrite Elo; exact HlB).
  (* the two cells and the mask of std L *)
  assert (Flo : locell m (std L) = locell m v).
  { assert (K := std_locell (2 * m) L HndL). rewrite HlocL in K.
    rewrite K, Elo. exact Hstd. }
  assert (Fhi : hicell m (std L) = hicell m v).
  { assert (K := std_hicell (2 * m) L HndL). rewrite HlocL in K.
    rewrite K, Ehi, std_addc. apply hicell_std_back. exact Hp. }
  assert (Fmask : map (fun x => Nat.leb m x) (std L)
                  = map (fun x => Nat.leb m x) v).
  { rewrite <- Emask. unfold std. rewrite map_map.
    apply map_ext_in. intros x Hx.
    assert (K := std_cut_test (2 * m) L x Hx). rewrite HlocL in K. natb. }
  (* two words with the same mask and the same two cells are equal *)
  assert (Gv := mrg_split (fun x => Nat.leb m x) v).
  assert (GL := mrg_split (fun x => Nat.leb m x) (std L)).
  cbn beta in Gv, GL.
  assert (Ev : filter (fun x => negb (Nat.leb m x)) v = locell m v)
    by (symmetry; apply locell_as_negb).
  assert (EL : filter (fun x => negb (Nat.leb m x)) (std L) = locell m (std L))
    by (symmetry; apply locell_as_negb).
  unfold hicell in Fhi.
  rewrite Ev in Gv. rewrite EL in GL.
  rewrite <- Gv, <- GL, Fmask, Fhi, Flo. reflexivity.
Qed.

Lemma tromino_of_unfold : forall m v h,
  tromino_of m (v, h)
  = mrg (map (fun x => Nat.leb m x) v)
        (map (fun x => (x + m)%nat) (hicell m v))
        (firstn m (pinv h))
    ++ skipn m (pinv h).
Proof. intros m v h. reflexivity. Qed.

Theorem tromino_of_spec : forall m v h,
  In v (dominoes m m) -> In h (dominoes m m) ->
  locell m h = pinv (locell m v) ->
  In (tromino_of m (v, h)) (trominoes m)
  /\ tgpair m (tromino_of m (v, h)) = (v, h).
Proof.
  intros m v h Hv Hh Hglue.
  assert (Sv := Hv). apply dominoes_spec in Sv.
  destruct Sv as [Hpv [Havv [Hlov Hhiv]]].
  assert (Sh := Hh). apply dominoes_spec in Sh.
  destruct Sh as [Hph [Havh [Hloh Hhih]]].
  assert (Hpv2 : is_perm v (2 * m))
    by (replace (2 * m)%nat with (m + m)%nat by lia; exact Hpv).
  assert (Hph2 : is_perm h (2 * m))
    by (replace (2 * m)%nat with (m + m)%nat by lia; exact Hph).
  assert (HpH : is_perm (pinv h) (2 * m))
    by (apply (pinv_perm h (2 * m)); exact Hph2).
  assert (HlH : length (pinv h) = (2 * m)%nat)
    by av.
  assert (HndH : NoDup (pinv h)) by av.
  assert (HbH : forall x, In x (pinv h) -> (x < 2 * m)%nat)
    by av.
  assert (Hsplit : firstn m (pinv h) ++ skipn m (pinv h) = pinv h)
    by apply firstn_skipn.
  assert (HlB : length (firstn m (pinv h)) = m)
    by (rewrite length_firstn, HlH; lia).
  assert (HlC : length (skipn m (pinv h)) = m)
    by (rewrite length_skipn, HlH; lia).
  assert (HndB : NoDup (firstn m (pinv h))) by (apply NoDup_firstn; exact HndH).
  assert (HndC : NoDup (skipn m (pinv h))) by (apply NoDup_skipn; exact HndH).
  assert (HbB : forall y, In y (firstn m (pinv h)) -> (y < 2 * m)%nat)
    by (intros y Hy; apply HbH; apply (in_firstn_w (pinv h) m); exact Hy).
  assert (HbC : forall y, In y (skipn m (pinv h)) -> (y < 2 * m)%nat)
    by (intros y Hy; apply HbH; apply (in_skipn_w (pinv h) m); exact Hy).
  assert (HpBC : is_perm (firstn m (pinv h) ++ skipn m (pinv h)) (2 * m))
    by (rewrite Hsplit; exact HpH).
  (* the shared cell of the pair, standardised, is the low cell of v *)
  assert (Hstd : std (firstn m (pinv h)) = locell m v).
  { assert (K := locell_pinv_prefix (firstn m (pinv h)) (skipn m (pinv h))
                   (2 * m) HpBC).
    rewrite HlB, Hsplit, (pinv_involutive h (2 * m) Hph2), Hglue in K.
    apply (pinv_inj _ _ m).
    - assert (Q := std_is_perm _ HndB). rewrite HlB in Q. exact Q.
    - apply (locell_is_perm m m v). exact Hpv.
    - symmetry. exact K. }
  (* the cell beside it avoids 213 *)
  assert (HCav : ~ contains_213 (skipn m (pinv h))).
  { assert (K := hicell_pinv_suffix (firstn m (pinv h)) (skipn m (pinv h))
                   (2 * m) HpBC).
    rewrite HlB, Hsplit, (pinv_involutive h (2 * m) Hph2) in K.
    assert (HpsC : is_perm (std (skipn m (pinv h))) m).
    { assert (Q := std_is_perm _ HndC). rewrite HlC in Q. exact Q. }
    intro C.
    apply (proj2 (std_213 (2 * m) _ HndC HbC)) in C.
    assert (C2 : contains_213 (pinv (std (skipn m (pinv h)))))
      by (apply (pinv_213 _ m HpsC); exact C).
    apply Hhih. rewrite K.
    assert (Ec : map (fun z => (m + z)%nat) (pinv (std (skipn m (pinv h))))
                 = map (fun z => (z + m)%nat) (pinv (std (skipn m (pinv h)))))
      by (apply map_ext; intro z; lia).
    rewrite Ec.
    apply (proj2 (contains_213_addc m (pinv (std (skipn m (pinv h)))))).
    exact C2. }
  (* the left column *)
  destruct (mrg_left_spec m v (firstn m (pinv h)) Hpv2 HlB HbB)
    as [Ehi [Elo Emask]].
  assert (HstdL : std (mrg (map (fun x => Nat.leb m x) v)
                           (map (fun x => (x + m)%nat) (hicell m v))
                           (firstn m (pinv h))) = v)
    by (apply std_left; assumption).
  assert (HlL : length (mrg (map (fun x => Nat.leb m x) v)
                            (map (fun x => (x + m)%nat) (hicell m v))
                            (firstn m (pinv h))) = (2 * m)%nat).
  { rewrite <- (len_map_gen _ _ (fun x => Nat.leb (2 * m) x)), Emask,
            len_map_gen. destruct Hpv2 as [K _]. exact K. }
  assert (Hndv : NoDup v) by av.
  assert (HndL : NoDup (mrg (map (fun x => Nat.leb m x) v)
                            (map (fun x => (x + m)%nat) (hicell m v))
                            (firstn m (pinv h)))).
  { apply (nodup_map_rev (rankin (mrg (map (fun x => Nat.leb m x) v)
                                      (map (fun x => (x + m)%nat) (hicell m v))
                                      (firstn m (pinv h))))).
    change (map (rankin ?X) ?X) with (std X). rewrite HstdL. exact Hndv. }
  assert (HpermL : Permutation
            (mrg (map (fun x => Nat.leb m x) v)
                 (map (fun x => (x + m)%nat) (hicell m v))
                 (firstn m (pinv h)))
            (map (fun x => (x + m)%nat) (hicell m v) ++ firstn m (pinv h))).
  { assert (Q := perm_filter_split (fun x => Nat.leb (2 * m) x)
                   (mrg (map (fun x => Nat.leb m x) v)
                        (map (fun x => (x + m)%nat) (hicell m v))
                        (firstn m (pinv h)))).
    cbn beta in Q.
    assert (E1 : filter (fun x => Nat.leb (2 * m) x)
                   (mrg (map (fun x => Nat.leb m x) v)
                        (map (fun x => (x + m)%nat) (hicell m v))
                        (firstn m (pinv h)))
                 = map (fun x => (x + m)%nat) (hicell m v)) by exact Ehi.
    rewrite E1 in Q.
    assert (E2 : filter (fun x => negb (Nat.leb (2 * m) x))
                   (mrg (map (fun x => Nat.leb m x) v)
                        (map (fun x => (x + m)%nat) (hicell m v))
                        (firstn m (pinv h))) = firstn m (pinv h))
      by (rewrite <- locell_as_negb; exact Elo).
    rewrite E2 in Q. exact Q. }
  assert (HbA : forall y, In y (map (fun x => (x + m)%nat) (hicell m v)) ->
                (2 * m <= y)%nat /\ (y < 3 * m)%nat).
  { intros y Hy. apply in_map_iff in Hy. destruct Hy as [z [Hz Hzin]].
    assert (K := proj1 (hicell_perm_values (2 * m) m v Hpv2 ltac:(lia) z) Hzin).
    lia. }
  assert (HbL : forall y, In y (mrg (map (fun x => Nat.leb m x) v)
                                    (map (fun x => (x + m)%nat) (hicell m v))
                                    (firstn m (pinv h))) -> (y < 3 * m)%nat).
  { intros y Hy.
    assert (K : In y (map (fun x => (x + m)%nat) (hicell m v)
                      ++ firstn m (pinv h)))
      by (apply (Permutation_in _ HpermL); exact Hy).
    apply in_app_or in K. destruct K as [K|K].
    - assert (Q := HbA y K). lia.
    - assert (Q := HbB y K). lia. }
  (* the word itself *)
  rewrite tromino_of_unfold.
  assert (Hlw : length (mrg (map (fun x => Nat.leb m x) v)
                            (map (fun x => (x + m)%nat) (hicell m v))
                            (firstn m (pinv h)) ++ skipn m (pinv h))
                = (3 * m)%nat) by (rewrite len_app, HlL, HlC; lia).
  assert (Hfst : firstn (2 * m)
                   (mrg (map (fun x => Nat.leb m x) v)
                        (map (fun x => (x + m)%nat) (hicell m v))
                        (firstn m (pinv h)) ++ skipn m (pinv h))
                 = mrg (map (fun x => Nat.leb m x) v)
                       (map (fun x => (x + m)%nat) (hicell m v))
                       (firstn m (pinv h)))
    by (rewrite <- HlL; apply firstn_len_app).
  assert (Hskp : skipn (2 * m)
                   (mrg (map (fun x => Nat.leb m x) v)
                        (map (fun x => (x + m)%nat) (hicell m v))
                        (firstn m (pinv h)) ++ skipn m (pinv h))
                 = skipn m (pinv h))
    by (rewrite <- HlL; apply skipn_len_app).
  assert (Hlowsplit : locell (2 * m)
                        (mrg (map (fun x => Nat.leb m x) v)
                             (map (fun x => (x + m)%nat) (hicell m v))
                             (firstn m (pinv h)) ++ skipn m (pinv h))
                      = pinv h).
  { unfold locell. rewrite filter_app.
    rewrite (filter_all_gen nat (fun x => Nat.ltb x (2 * m))
               (skipn m (pinv h)))
      by (intros y Hy; apply Nat.ltb_lt; apply HbC; exact Hy).
    change (filter (fun x => Nat.ltb x (2 * m))
              (mrg (map (fun x => Nat.leb m x) v)
                   (map (fun x => (x + m)%nat) (hicell m v))
                   (firstn m (pinv h))))
      with (locell (2 * m)
              (mrg (map (fun x => Nat.leb m x) v)
                   (map (fun x => (x + m)%nat) (hicell m v))
                   (firstn m (pinv h)))).
    rewrite Elo. exact Hsplit. }
  assert (Hperm3 : Permutation
            (mrg (map (fun x => Nat.leb m x) v)
                 (map (fun x => (x + m)%nat) (hicell m v))
                 (firstn m (pinv h)) ++ skipn m (pinv h))
            (map (fun x => (x + m)%nat) (hicell m v)
             ++ (firstn m (pinv h) ++ skipn m (pinv h)))).
  { rewrite app_assoc. apply Permutation_app_tail. exact HpermL. }
  assert (Hip : is_perm (mrg (map (fun x => Nat.leb m x) v)
                             (map (fun x => (x + m)%nat) (hicell m v))
                             (firstn m (pinv h)) ++ skipn m (pinv h))
                        (3 * m)).
  { split; [exact Hlw | split].
    - apply (Permutation_NoDup (Permutation_sym Hperm3)).
      apply NoDup_app_disj.
      + apply NoDup_map_inj;
          [unfold hicell; apply NoDup_filter; exact Hndv
           | intros x y _ _ He; lia].
      + rewrite Hsplit. exact HndH.
      + intros z Hz1 Hz2. assert (K1 := HbA z Hz1).
        rewrite Hsplit in Hz2. assert (K2 := HbH z Hz2). lia.
    - intros x Hx.
      assert (K : In x (map (fun y => (y + m)%nat) (hicell m v)
                        ++ (firstn m (pinv h) ++ skipn m (pinv h))))
        by (apply (Permutation_in _ Hperm3); exact Hx).
      apply in_app_or in K. destruct K as [K|K].
      + assert (Q := HbA x K). lia.
      + rewrite Hsplit in K. assert (Q := HbH x K). lia. }
  (* avoidance, by the fibre split *)
  assert (Hav : ~ contains_1324
            (mrg (map (fun x => Nat.leb m x) v)
                 (map (fun x => (x + m)%nat) (hicell m v))
                 (firstn m (pinv h)) ++ skipn m (pinv h))).
  { intros [i [j [k [l Hocc]]]].
    assert (Hempty : forall t, (2 * m <= t)%nat ->
              (t < length (mrg (map (fun x => Nat.leb m x) v)
                               (map (fun x => (x + m)%nat) (hicell m v))
                               (firstn m (pinv h)) ++ skipn m (pinv h)))%nat ->
              (nth t (mrg (map (fun x => Nat.leb m x) v)
                          (map (fun x => (x + m)%nat) (hicell m v))
                          (firstn m (pinv h)) ++ skipn m (pinv h)) 0%nat
               < 2 * m)%nat).
    { intros t H1 H2. rewrite Hlw in H2.
      rewrite (nth_app2 _ _ t 0%nat ltac:(rewrite HlL; lia)), HlL.
      apply HbC. apply nth_In. rewrite HlC. lia. }
    destruct (tromino_fibre _ (2 * m) (2 * m) Hempty i j k l Hocc)
      as [Hlt | [Bi [Bj [Bk Bl]]]].
    - assert (Hocc2 : contains_1324
                (mrg (map (fun x => Nat.leb m x) v)
                     (map (fun x => (x + m)%nat) (hicell m v))
                     (firstn m (pinv h)))).
      { destruct Hocc as [Hij [Hjk [Hkl [Hlen [Hik [Hkj Hjl]]]]]].
        assert (Enth : forall t, (t < 2 * m)%nat ->
                  nth t (mrg (map (fun x => Nat.leb m x) v)
                             (map (fun x => (x + m)%nat) (hicell m v))
                             (firstn m (pinv h)) ++ skipn m (pinv h)) 0%nat
                  = nth t (mrg (map (fun x => Nat.leb m x) v)
                               (map (fun x => (x + m)%nat) (hicell m v))
                               (firstn m (pinv h))) 0%nat).
        { intros t Ht. apply nth_app1. rewrite HlL. exact Ht. }
        rewrite (Enth i ltac:(lia)), (Enth k ltac:(lia)) in Hik.
        rewrite (Enth k ltac:(lia)), (Enth j ltac:(lia)) in Hkj.
        rewrite (Enth j ltac:(lia)), (Enth l ltac:(lia)) in Hjl.
        exists i, j, k, l. unfold has_1324_at.
        repeat split; try assumption; try lia. }
      apply Havv. rewrite <- HstdL.
      apply (proj2 (std_1324 (3 * m) _ HndL HbL)). exact Hocc2.
    - assert (K := locell_1324_pos (2 * m) _ i j k l
                     ltac:(destruct Hocc as [H _]; exact H)
                     ltac:(destruct Hocc as [_ [H _]]; exact H)
                     ltac:(destruct Hocc as [_ [_ [H _]]]; exact H)
                     ltac:(destruct Hocc as [_ [_ [_ [H _]]]]; exact H)
                     Bi Bj Bk Bl Hocc).
      rewrite Hlowsplit in K.
      apply (proj1 (pinv_avoids_1324 h (2 * m) Hph2) Havh). exact K. }
  split.
  - apply trominoes_spec. split; [exact Hip | split; [exact Hav | split]].
    + rewrite Hskp. exact HbC.
    + split; [| split].
      * rewrite Hfst, Elo. intro C.
        apply Hlov. rewrite <- Hstd.
        apply (proj2 (std_132 (2 * m) _ HndB HbB)). exact C.
      * rewrite Hfst, Ehi. intro C.
        apply Hhiv. apply (proj1 (contains_213_addc m (hicell m v))). exact C.
      * rewrite Hskp. exact HCav.
  - unfold tgpair. rewrite Hfst, HstdL, Hlowsplit,
      (pinv_involutive h (2 * m) Hph2). reflexivity.
Qed.

Lemma glued_nodup : forall m, NoDup (glued m).
Proof.
  intro m. unfold glued. apply NoDup_filter.
  apply NoDup_list_prod; apply dominoes_nodup.
Qed.

Lemma glued_spec : forall m p,
  In p (glued m) <->
  (In (fst p) (dominoes m m) /\ In (snd p) (dominoes m m)
   /\ locell m (snd p) = pinv (locell m (fst p))).
Proof.
  intros m p. unfold glued. rewrite filter_In. destruct p as [v h].
  cbn [fst snd]. split.
  - intros [Hp He]. apply in_prod_iff in Hp. destruct Hp as [Hv Hh].
    split; [exact Hv | split; [exact Hh |]].
    destruct (list_eq_dec Nat.eq_dec (locell m h) (pinv (locell m v)))
      as [E|E]; [exact E | discriminate].
  - intros [Hv [Hh Hg]].
    split; [apply in_prod; assumption |].
    destruct (list_eq_dec Nat.eq_dec (locell m h) (pinv (locell m v)))
      as [E|E]; [reflexivity | contradiction].
Qed.

Theorem glued_le_tromino : forall m, (length (glued m) <= Tromino m)%nat.
Proof.
  intro m. unfold Tromino.
  rewrite <- (len_map_gen _ _ (tromino_of m) (glued m)).
  apply NoDup_incl_length.
  - apply NoDup_map_inj; [apply glued_nodup|].
    intros p q Hp Hq He.
    destruct p as [v h]; destruct q as [v' h'].
    apply glued_spec in Hp. cbn [fst snd] in Hp. destruct Hp as [Hv [Hh Hg]].
    apply glued_spec in Hq. cbn [fst snd] in Hq. destruct Hq as [Hv' [Hh' Hg']].
    cbn beta in He.
    assert (K1 := proj2 (tromino_of_spec m v h Hv Hh Hg)).
    assert (K2 := proj2 (tromino_of_spec m v' h' Hv' Hh' Hg')).
    rewrite <- K1, <- K2, He. reflexivity.
  - intros z Hz. apply in_map_iff in Hz. destruct Hz as [p [Hpz Hpin]].
    subst z. destruct p as [v h].
    apply glued_spec in Hpin. cbn [fst snd] in Hpin.
    destruct Hpin as [Hv [Hh Hg]].
    exact (proj1 (tromino_of_spec m v h Hv Hh Hg)).
Qed.

(* Tcount is the tromino count, in general. *)
Theorem tromino_eq_Tcount : forall m, Tromino m = Tcount m.
Proof.
  intro m. rewrite Tcount_glued. apply Nat.le_antisymm;
    [apply tromino_le_glued | apply glued_le_tromino].
Qed.

(* over the fast enumerator, so the counts are affordable *)
Definition trominoesf (m : nat) : list (list nat) :=
  filter (trominob m) (genf (3 * m)).

Definition Trominof (m : nat) : nat := length (trominoesf m).

Lemma Trominof_eq : forall m, Trominof m = Tromino m.
Proof.
  intro m. unfold Trominof, Tromino, trominoesf, trominoes.
  rewrite genf_eq. reflexivity.
Qed.

(* The two counts, at the sizes the enumeration reaches. *)
Theorem tromino_count_1 : Tromino 1 = Tcount 1.
Proof. apply tromino_eq_Tcount. Qed.

Theorem tromino_count_2 : Tromino 2 = Tcount 2.
Proof. apply tromino_eq_Tcount. Qed.

(* ------------------------------------------------------------------ *)
(* The decreasing lower cell is the unique maximiser of d_A.  Insert the
   smallest upper value directly after an ascent of the lower cell and put the
   remaining upper values, in increasing order, at the end.  Over the
   decreasing cell that word is a domino, since its upper cell increases and
   dec_cell_domino leaves nothing else to check; over any cell with an ascent
   it carries a 1324, the ascent playing 1 and 3 and the two upper points 2
   and 4.  Its mask and its upper cell do not depend on the lower cell, so the
   injection of dA_le_dec cannot reach it and the inequality is strict. *)

Definition upvals (b a : nat) : list nat := map (fun i => (b + i)%nat) (seq 0 a).

Definition maskins (b p a : nat) : list bool :=
  repeat false (S p) ++ true :: (repeat false (b - S p) ++ repeat true (a - 1)).

Definition insword (b p a : nat) (L : list nat) : list nat :=
  firstn (S p) L ++ b :: (skipn (S p) L
                          ++ map (fun i => (S b + i)%nat) (seq 0 (a - 1))).

Lemma nth_skipn_nat : forall (l : list nat) m n d,
  nth n (skipn m l) d = nth (m + n) l d.
Proof.
  induction l as [|x l IH]; intros m n d.
  - rewrite skipn_nil. rewrite !nth_overflow by (cbn [length]; lia). reflexivity.
  - destruct m as [|m]; cbn [skipn]; [reflexivity | cbn [nth]; apply IH].
Qed.

Lemma map_leb_low : forall b (l : list nat),
  (forall x, In x l -> (x < b)%nat) ->
  map (fun x => Nat.leb b x) l = repeat false (length l).
Proof.
  intros b l. induction l as [|x l IH]; intro H; cbn [map length repeat];
    [reflexivity|].
  assert (K := H x (or_introl eq_refl)).
  destruct (Nat.leb_spec b x); [exfalso; lia|].
  f_equal. apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma map_leb_high : forall b (l : list nat),
  (forall x, In x l -> (b <= x)%nat) ->
  map (fun x => Nat.leb b x) l = repeat true (length l).
Proof.
  intros b l. induction l as [|x l IH]; intro H; cbn [map length repeat];
    [reflexivity|].
  assert (K := H x (or_introl eq_refl)).
  destruct (Nat.leb_spec b x); [|exfalso; lia].
  f_equal. apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma incr_no_213 : forall l,
  (forall t t', (t < t')%nat -> (t' < length l)%nat ->
     (nth t l 0%nat < nth t' l 0%nat)%nat) -> ~ contains_213 l.
Proof.
  intros l H [p [q [r Hpat]]]. unfold has_213_at in Hpat.
  destruct Hpat as [Hpq [Hqr [Hr [Hqp _]]]].
  assert (K := H p q ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma upvals_length : forall b a, length (upvals b a) = a.
Proof. intros b a. unfold upvals. rewrite len_map_gen, length_seq. reflexivity. Qed.

Lemma upvals_nth : forall b a t, (t < a)%nat ->
  nth t (upvals b a) 0%nat = (b + t)%nat.
Proof.
  intros b a t H. unfold upvals.
  rewrite (map_nth_def (fun i => (b + i)%nat) (seq 0 a) t)
    by (rewrite length_seq; exact H).
  rewrite seq_nth by exact H. reflexivity.
Qed.

Lemma upvals_bound : forall b a x, In x (upvals b a) ->
  (b <= x)%nat /\ (x < b + a)%nat.
Proof.
  intros b a x H. unfold upvals in H. apply in_map_iff in H.
  destruct H as [i [Hi Hin]]. apply in_seq in Hin. lia.
Qed.

Lemma upvals_nodup : forall b a, NoDup (upvals b a).
Proof.
  intros b a. unfold upvals. apply NoDup_map_inj; [apply seq_NoDup|].
  intros x y _ _ He. lia.
Qed.

Lemma upvals_no_213 : forall b a, ~ contains_213 (upvals b a).
Proof.
  intros b a. apply incr_no_213. intros t t' H1 H2.
  rewrite upvals_length in H2.
  rewrite (upvals_nth b a t ltac:(lia)), (upvals_nth b a t' H2). lia.
Qed.

Lemma upvals_cons : forall b a, (1 <= a)%nat ->
  upvals b a = b :: map (fun i => (S b + i)%nat) (seq 0 (a - 1)).
Proof.
  intros b a Ha. destruct a as [|a']; [lia|].
  unfold upvals. replace (S a' - 1)%nat with a' by lia.
  change (seq 0 (S a')) with (0%nat :: seq 1 a').
  cbn [map]. rewrite Nat.add_0_r. f_equal.
  rewrite <- (seq_shift a' 0), map_map. apply map_ext. intro i. lia.
Qed.

Lemma insword_length : forall b p a L,
  length L = b -> (p < b)%nat -> (1 <= a)%nat ->
  length (insword b p a L) = (a + b)%nat.
Proof.
  intros b p a L HL Hp Ha. unfold insword.
  rewrite len_app. cbn [length]. rewrite len_app.
  rewrite length_firstn, length_skipn, len_map_gen, length_seq, HL. lia.
Qed.

Lemma insword_locell : forall b p a L,
  (forall x, In x L -> (x < b)%nat) ->
  locell b (insword b p a L) = L.
Proof.
  intros b p a L HB. unfold insword, locell.
  rewrite filter_app. cbn [filter]. rewrite Nat.ltb_irrefl.
  rewrite filter_app.
  rewrite (filter_all_gen nat (fun x => Nat.ltb x b) (firstn (S p) L)).
  2:{ intros y Hy. apply Nat.ltb_lt. apply HB.
      apply (In_firstn_nat y (S p) L). exact Hy. }
  rewrite (filter_all_gen nat (fun x => Nat.ltb x b) (skipn (S p) L)).
  2:{ intros y Hy. apply Nat.ltb_lt. apply HB.
      apply (in_skipn_w L (S p)). exact Hy. }
  rewrite (filter_all_false (fun x => Nat.ltb x b)
             (map (fun i => (S b + i)%nat) (seq 0 (a - 1)))).
  2:{ intros y Hy. apply in_map_iff in Hy. destruct Hy as [i [Hi _]].
      destruct (Nat.ltb_spec y b); [exfalso; lia | reflexivity]. }
  rewrite app_nil_r. apply firstn_skipn.
Qed.

Lemma insword_hicell : forall b p a L,
  (forall x, In x L -> (x < b)%nat) -> (1 <= a)%nat ->
  hicell b (insword b p a L) = upvals b a.
Proof.
  intros b p a L HB Ha. unfold insword, hicell.
  rewrite filter_app. cbn [filter]. rewrite Nat.leb_refl.
  rewrite filter_app.
  rewrite (filter_all_false (fun x => Nat.leb b x) (firstn (S p) L)).
  2:{ intros y Hy.
      assert (K := HB y (In_firstn_nat y (S p) L Hy)).
      destruct (Nat.leb_spec b y); [exfalso; lia | reflexivity]. }
  rewrite (filter_all_false (fun x => Nat.leb b x) (skipn (S p) L)).
  2:{ intros y Hy.
      assert (K := HB y (in_skipn_w L (S p) y Hy)).
      destruct (Nat.leb_spec b y); [exfalso; lia | reflexivity]. }
  rewrite (filter_all_gen nat (fun x => Nat.leb b x)
             (map (fun i => (S b + i)%nat) (seq 0 (a - 1)))).
  2:{ intros y Hy. apply in_map_iff in Hy. destruct Hy as [i [Hi _]].
      destruct (Nat.leb_spec b y); [reflexivity | exfalso; lia]. }
  cbn [app]. symmetry. apply upvals_cons. exact Ha.
Qed.

Lemma insword_mask : forall b p a L,
  length L = b -> (p < b)%nat -> (forall x, In x L -> (x < b)%nat) ->
  map (fun x => Nat.leb b x) (insword b p a L) = maskins b p a.
Proof.
  intros b p a L HL Hp HB. unfold insword, maskins.
  rewrite map_app. cbn [map]. rewrite Nat.leb_refl, map_app.
  rewrite (map_leb_low b (firstn (S p) L))
    by (intros y Hy; apply HB; apply (In_firstn_nat y (S p) L); exact Hy).
  rewrite (map_leb_low b (skipn (S p) L))
    by (intros y Hy; apply HB; apply (in_skipn_w L (S p) y); exact Hy).
  rewrite (map_leb_high b (map (fun i => (S b + i)%nat) (seq 0 (a - 1)))).
  2:{ intros y Hy. apply in_map_iff in Hy. destruct Hy as [i [Hi _]]. lia. }
  rewrite length_firstn, length_skipn, len_map_gen, length_seq, HL.
  replace (Nat.min (S p) b) with (S p) by lia. reflexivity.
Qed.

Lemma insword_perm : forall b p a L,
  length L = b -> NoDup L -> (forall x, In x L -> (x < b)%nat) ->
  (p < b)%nat -> (1 <= a)%nat ->
  is_perm (insword b p a L) (a + b).
Proof.
  intros b p a L HL Hnd HB Hp Ha.
  assert (Hlo : locell b (insword b p a L) = L)
    by (apply insword_locell; exact HB).
  assert (Hhi : hicell b (insword b p a L) = upvals b a)
    by (apply insword_hicell; assumption).
  assert (Hperm : Permutation (insword b p a L) (upvals b a ++ L)).
  { assert (Q := cell_split_perm b (insword b p a L)).
    rewrite Hlo, Hhi in Q. exact Q. }
  split; [apply insword_length; assumption | split].
  - apply (Permutation_NoDup (Permutation_sym Hperm)).
    apply NoDup_app_disj; [apply upvals_nodup | exact Hnd |].
    intros z Hz1 Hz2. assert (K1 := upvals_bound b a z Hz1).
    assert (K2 := HB z Hz2). lia.
  - intros x Hx.
    assert (K : In x (upvals b a ++ L))
      by (apply (Permutation_in _ Hperm); exact Hx).
    apply in_app_or in K. destruct K as [K|K].
    + assert (Q := upvals_bound b a x K). lia.
    + assert (Q := HB x K). lia.
Qed.

Theorem insword_domino : forall b p a,
  (p < b)%nat -> (1 <= a)%nat ->
  In (insword b p a (decpat b)) (dominoes a b).
Proof.
  intros b p a Hp Ha.
  apply (dec_cell_domino a b _).
  - apply insword_perm;
      [apply decpat_length | apply decpat_nodup | apply decpat_bound
       | exact Hp | exact Ha].
  - apply insword_locell. apply decpat_bound.
  - rewrite (insword_hicell b p a (decpat b) (decpat_bound b) Ha).
    apply upvals_no_213.
Qed.

(* the four entries the occurrence reads *)

Lemma insword_nth_lo : forall b p a L t,
  (t < S p)%nat -> (S p <= length L)%nat ->
  nth t (insword b p a L) 0%nat = nth t L 0%nat.
Proof.
  intros b p a L t H1 H2. unfold insword.
  rewrite nth_app1 by (rewrite length_firstn; lia).
  apply nth_firstn_lt. lia.
Qed.

Lemma insword_nth_mid : forall b p a L,
  (S p <= length L)%nat -> nth (S p) (insword b p a L) 0%nat = b.
Proof.
  intros b p a L H. unfold insword.
  rewrite nth_app2 by (rewrite length_firstn; lia).
  rewrite length_firstn.
  replace (S p - Nat.min (S p) (length L))%nat with 0%nat by lia.
  reflexivity.
Qed.

Lemma insword_nth_hi : forall b p a L t,
  (p < t)%nat -> (t < length L)%nat ->
  nth (S t) (insword b p a L) 0%nat = nth t L 0%nat.
Proof.
  intros b p a L t H1 H2. unfold insword.
  rewrite nth_app2 by (rewrite length_firstn; lia).
  rewrite length_firstn.
  replace (Nat.min (S p) (length L)) with (S p) by lia.
  replace (S t - S p)%nat with (S (t - S p))%nat by lia.
  cbn [nth].
  rewrite nth_app1 by (rewrite length_skipn; lia).
  rewrite nth_skipn_nat. f_equal. lia.
Qed.

Lemma insword_nth_top : forall b p a L,
  length L = b -> (p < b)%nat -> (2 <= a)%nat ->
  nth (S b) (insword b p a L) 0%nat = S b.
Proof.
  intros b p a L HL Hp Ha. unfold insword.
  rewrite nth_app2 by (rewrite length_firstn, HL; lia).
  rewrite length_firstn, HL.
  replace (Nat.min (S p) b) with (S p) by lia.
  replace (S b - S p)%nat with (S (b - S p))%nat by lia.
  cbn [nth].
  rewrite nth_app2 by (rewrite length_skipn, HL; lia).
  rewrite length_skipn, HL.
  replace (b - S p - (b - S p))%nat with 0%nat by lia.
  destruct (a - 1)%nat as [|k] eqn:Ea; [lia|].
  cbn [seq map nth]. lia.
Qed.

Theorem insword_1324 : forall b p a L p2,
  length L = b -> (forall x, In x L -> (x < b)%nat) ->
  (p < p2)%nat -> (p2 < b)%nat -> (2 <= a)%nat ->
  (nth p L 0%nat < nth p2 L 0%nat)%nat ->
  contains_1324 (insword b p a L).
Proof.
  intros b p a L p2 HL HB H1 H2 Ha Hasc.
  exists p, (S p), (S p2), (S b). unfold has_1324_at. cbv zeta.
  rewrite (insword_nth_lo b p a L p ltac:(lia) ltac:(lia)).
  rewrite (insword_nth_mid b p a L ltac:(lia)).
  rewrite (insword_nth_hi b p a L p2 H1 ltac:(lia)).
  rewrite (insword_nth_top b p a L HL ltac:(lia) Ha).
  rewrite (insword_length b p a L HL ltac:(lia) ltac:(lia)).
  assert (Hb2 : (nth p2 L 0%nat < b)%nat)
    by (apply HB; apply nth_In; lia).
  repeat split; lia.
Qed.

(* rebuilding the witness over a different lower cell *)
Lemma insword_rebuild : forall b p a L L',
  length L = b -> (forall x, In x L -> (x < b)%nat) ->
  length L' = b -> (forall x, In x L' -> (x < b)%nat) ->
  (p < b)%nat -> (1 <= a)%nat ->
  mrg (map (fun x => Nat.leb b x) (insword b p a L))
      (hicell b (insword b p a L)) L'
  = insword b p a L'.
Proof.
  intros b p a L L' HL HLB HL' HL'B Hp Ha.
  assert (G := mrg_split (fun z => Nat.leb b z) (insword b p a L')).
  cbn beta in G.
  assert (E : filter (fun z => negb (Nat.leb b z)) (insword b p a L') = L').
  { rewrite <- locell_as_negb. apply insword_locell. exact HL'B. }
  rewrite E in G.
  change (filter (fun z => Nat.leb b z) (insword b p a L'))
    with (hicell b (insword b p a L')) in G.
  rewrite (insword_mask b p a L' HL' Hp HL'B) in G.
  rewrite (insword_hicell b p a L' HL'B Ha) in G.
  rewrite (insword_mask b p a L HL Hp HLB).
  rewrite (insword_hicell b p a L HLB Ha).
  exact G.
Qed.

(* a permutation is its own standardisation, so a cell with no ascent is the
   decreasing pattern outright *)

Lemma rankin_perm_id : forall l m, is_perm l m ->
  forall x, In x l -> rankin l x = x.
Proof.
  intros l m Hp x Hx. assert (Hp' := Hp).
  assert (Hxm : (x < m)%nat) by (destruct Hp as [_ [_ Hb]]; apply Hb; exact Hx).
  assert (Hhi : length (hicell x l) = (m - x)%nat)
    by (apply (hicell_perm_length m x l Hp' ltac:(lia))).
  assert (K := Permutation_length (cell_split_perm x l)).
  rewrite len_app, Hhi in K. destruct Hp as [Hlen _]. rewrite Hlen in K.
  unfold rankin.
  change (filter (fun y => Nat.ltb y x) l) with (locell x l). lia.
Qed.

Theorem std_perm_id : forall l m, is_perm l m -> std l = l.
Proof.
  intros l m Hp. unfold std.
  transitivity (map (fun x : nat => x) l).
  - apply map_ext_in. intros x Hx. apply (rankin_perm_id l m Hp x Hx).
  - apply map_id.
Qed.

Lemma perm_no_ascent_dec : forall b l, is_perm l b ->
  (forall p p2, (p < p2)%nat -> (p2 < b)%nat ->
     ~ (nth p l 0%nat < nth p2 l 0%nat)%nat) ->
  l = decpat b.
Proof.
  intros b l Hp Hno.
  assert (Hlen : length l = b) by av.
  assert (Hnd : NoDup l) by av.
  assert (Hstrict : forall t t', (t < t')%nat -> (t' < length l)%nat ->
            (nth t' l 0%nat < nth t l 0%nat)%nat).
  { intros t t' H1 H2.
    assert (Hne : nth t' l 0%nat <> nth t l 0%nat).
    { intro E. apply (proj1 (NoDup_nth l 0%nat) Hnd t' t) in E; lia. }
    assert (K := Hno t t' H1 ltac:(lia)). lia. }
  assert (Hs : sortedD l) by (apply strict_dec_sortedD; exact Hstrict).
  rewrite <- (std_perm_id l b Hp), (dec_std l Hnd Hs), Hlen. reflexivity.
Qed.

Lemma dec_or_ascent : forall b l, In l (gen132 b) -> l <> decpat b ->
  exists p p2, (p < p2)%nat /\ (p2 < b)%nat /\
               (nth p l 0%nat < nth p2 l 0%nat)%nat.
Proof.
  intros b l Hl Hne.
  assert (Hp : is_perm l b) by av.
  destruct (bounded_ex_dec
    (fun p => exists p2, (p < p2)%nat /\ (p2 < b)%nat /\
                (nth p l 0%nat < nth p2 l 0%nat)%nat) b) as [Hex|Hno].
  { intro p.
    destruct (bounded_ex_dec
      (fun p2 => (p < p2)%nat /\ (p2 < b)%nat /\
                 (nth p l 0%nat < nth p2 l 0%nat)%nat) b) as [K|K].
    - intro p2.
      destruct (lt_dec p p2) as [A|A]; [|right; tauto].
      destruct (lt_dec p2 b) as [B|B]; [|right; tauto].
      destruct (lt_dec (nth p l 0%nat) (nth p2 l 0%nat)) as [C|C];
        [|right; tauto].
      left. repeat split; assumption.
    - left. destruct K as [p2 [_ H]]. exists p2. exact H.
    - right. intros [p2 H]. apply K. exists p2. split; [lia | exact H]. }
  - destruct Hex as [p [_ [p2 H]]]. exists p, p2. exact H.
  - exfalso. apply Hne. apply (perm_no_ascent_dec b l Hp).
    intros p p2 H1 H2 H3. apply Hno. exists p. split; [lia|].
    exists p2. repeat split; assumption.
Qed.

(* The maximiser is unique. *)
Theorem dA_lt_dec : forall a b l,
  (2 <= a)%nat -> In l (gen132 b) -> l <> decpat b ->
  (dA a b l < dA a b (decpat b))%nat.
Proof.
  intros a b l Ha Hl Hne.
  destruct (dec_or_ascent b l Hl Hne) as [p [p2 [H1 [H2 H3]]]].
  assert (Hp : is_perm l b) by av.
  assert (Hlb : length l = b) by av.
  assert (HlB : forall x, In x l -> (x < b)%nat)
    by av.
  assert (Hpb : (p < b)%nat) by lia.
  set (W := insword b p a (decpat b)).
  assert (HWin : In W (dominoes a b))
    by (unfold W; apply insword_domino; lia).
  assert (HWlo : locell b W = decpat b)
    by (unfold W; apply insword_locell; apply decpat_bound).
  unfold dA.
  set (Fl := filter (fun w => if list_eq_dec Nat.eq_dec (locell b w) l
                              then true else false) (dominoes a b)).
  set (Fd := filter (fun w => if list_eq_dec Nat.eq_dec (locell b w) (decpat b)
                              then true else false) (dominoes a b)).
  (* the image of the l-fibre, together with W, is a duplicate-free sublist *)
  assert (Hmiss : forall w, In w Fl -> flatlo b w <> W).
  { intros w Hw Hc.
    apply filter_In in Hw. destruct Hw as [Hwd Hwl].
    destruct (list_eq_dec Nat.eq_dec (locell b w) l) as [Ew|]; [|discriminate].
    destruct (flatlo_spec a b w Hwd) as [_ [Ehi Ema]].
    assert (Ehiw : hicell b w = hicell b W)
      by (rewrite <- Ehi, Hc; reflexivity).
    assert (Emaw : map (fun z => Nat.leb b z) w
                   = map (fun z => Nat.leb b z) W)
      by (rewrite <- Ema, Hc; reflexivity).
    assert (Gw := mrg_split (fun z => Nat.leb b z) w). cbn beta in Gw.
    assert (Fw : filter (fun z => negb (Nat.leb b z)) w = l)
      by (rewrite <- locell_as_negb; exact Ew).
    rewrite Fw in Gw.
    change (filter (fun z => Nat.leb b z) w) with (hicell b w) in Gw.
    rewrite Ehiw, Emaw in Gw.
    assert (Hre : mrg (map (fun z => Nat.leb b z) W) (hicell b W) l
                  = insword b p a l).
    { unfold W. apply insword_rebuild;
        [apply decpat_length | apply decpat_bound | exact Hlb | exact HlB
         | exact Hpb | lia]. }
    rewrite Hre in Gw. subst w.
    apply dominoes_spec in Hwd. destruct Hwd as [_ [Hav _]].
    apply Hav. apply (insword_1324 b p a l p2); assumption. }
  assert (HND : NoDup (map (flatlo b) Fl ++ [W])).
  { apply NoDup_app_disj.
    - apply NoDup_map_inj.
      + apply NoDup_filter. apply dominoes_nodup.
      + intros x y Hx Hy He.
        apply filter_In in Hx. destruct Hx as [Hxd Hxl].
        apply filter_In in Hy. destruct Hy as [Hyd Hyl].
        destruct (list_eq_dec Nat.eq_dec (locell b x) l) as [Ex|];
          [|discriminate].
        destruct (list_eq_dec Nat.eq_dec (locell b y) l) as [Ey|];
          [|discriminate].
        destruct (flatlo_spec a b x Hxd) as [_ [Ehx Emx]].
        destruct (flatlo_spec a b y Hyd) as [_ [Ehy Emy]].
        assert (Ehi : hicell b x = hicell b y)
          by (rewrite <- Ehx, <- Ehy, He; reflexivity).
        assert (Ema : map (fun z => Nat.leb b z) x
                      = map (fun z => Nat.leb b z) y)
          by (rewrite <- Emx, <- Emy, He; reflexivity).
        cells b.
    - constructor; [intros [] | constructor].
    - intros z Hz1 Hz2. cbn [In] in Hz2.
      destruct Hz2 as [Hz2 | []]. subst z.
      apply in_map_iff in Hz1. destruct Hz1 as [w [Hw Hwin]].
      exact (Hmiss w Hwin Hw). }
  assert (HIN : incl (map (flatlo b) Fl ++ [W]) Fd).
  { intros z Hz. apply in_app_or in Hz. destruct Hz as [Hz | Hz].
    - apply in_map_iff in Hz. destruct Hz as [w [Hwz Hwin]]. subst z.
      apply filter_In in Hwin. destruct Hwin as [Hwd _].
      apply filter_In. split; [apply flatlo_in; exact Hwd|].
      destruct (flatlo_spec a b w Hwd) as [Elo _].
      destruct (list_eq_dec Nat.eq_dec (locell b (flatlo b w)) (decpat b));
        [reflexivity | contradiction].
    - cbn [In] in Hz. destruct Hz as [Hz | []]. subst z.
      apply filter_In. split; [exact HWin|].
      destruct (list_eq_dec Nat.eq_dec (locell b W) (decpat b));
        [reflexivity | contradiction]. }
  assert (K := NoDup_incl_length HND HIN).
  rewrite len_app_gen, len_map_gen in K. cbn [length] in K. lia.
Qed.

(* The decreasing fibre is non-empty, the witness itself sitting in it. *)
Lemma dA_dec_pos : forall a b, (1 <= a)%nat -> (1 <= b)%nat ->
  (1 <= dA a b (decpat b))%nat.
Proof.
  intros a b Ha Hb. unfold dA.
  apply (in_length_pos (list nat) (insword b 0 a (decpat b))).
  apply filter_In. split.
  - apply insword_domino; [lia | exact Ha].
  - destruct (list_eq_dec Nat.eq_dec
                (locell b (insword b 0 a (decpat b))) (decpat b)) as [E|E];
      [reflexivity|].
    exfalso. apply E. apply insword_locell. apply decpat_bound.
Qed.

(* Hence the up-set at the top threshold is the singleton { decpat }, which
   decpat_pinv fixes, and pqd_diag_closed applies with no hypothesis left. *)
Theorem pqd_diag_top : forall m a,
  (2 <= m)%nat ->
  (cntA a (diag_pairs m) * cntB (pred (dA m m (decpat m))) (diag_pairs m)
   <= length (diag_pairs m)
      * cnt2 a (pred (dA m m (decpat m))) (diag_pairs m))%nat.
Proof.
  intros m a Hm. apply pqd_diag_closed. intros l Hl.
  assert (Hpos : (1 <= dA m m (decpat m))%nat) by (apply dA_dec_pos; lia).
  assert (Hp : is_perm l m) by av.
  assert (Hli : In (pinv l) (gen132 m))
    by (apply (Permutation_in _ (pinv_gen132 m)); apply in_map; exact Hl).
  assert (Hmax : forall k, In k (gen132 m) ->
            ((pred (dA m m (decpat m)) < dA m m k)%nat <-> k = decpat m)).
  { intros k Hk. split.
    - intro Hgt. destruct (list_eq_dec Nat.eq_dec k (decpat m)) as [E|E];
        [exact E|]. exfalso. assert (Q := dA_lt_dec m m k Hm Hk E). lia.
    - intro E. subst k. lia. }
  split.
  - intro E.
    assert (Q : pinv l = decpat m) by (apply (Hmax (pinv l) Hli); exact E).
    apply (Hmax l Hl).
    assert (R : pinv (pinv l) = pinv (decpat m)) by (rewrite Q; reflexivity).
    rewrite (pinv_involutive l m Hp), decpat_pinv in R. exact R.
  - intro E.
    assert (Q : l = decpat m) by (apply (Hmax l Hl); exact E).
    apply (Hmax (pinv l) Hli). rewrite Q. apply decpat_pinv.
Qed.

(* The two-term law, with the degree bounds as fields. *)
Record Diagonal (d : nat) : Type := mkDiagonal {
  dp : list Q;
  dq : list Q;
  dp_len : length dp = d;
  dq_len : length dq = pred d;
  d_law  : forall M : nat,
    Qeq (Qn (Ddiag d M))
        (Qplus (Qmult (polyQ dp (Qn M)) (Qn (binomN (2 * M) M)))
               (Qmult (polyQ dq (Qn M)) (Qn (4 ^ M))))
}.

(* The d = 1 diagonal outright, from Ddiag_one_binom: p_1 is the constant 1 and
   q_1 is empty, so the law there reads Ddiag 1 M = C(2M,M). *)
Definition diagonal_one : Diagonal 1.
Proof.
  refine (mkDiagonal 1%nat (1%Q :: nil) nil eq_refl eq_refl _).
  intro M. rewrite Ddiag_one_binom. cbn [polyQ]. ring.
Defined.

Theorem two_term_law : forall d : nat, (2 <= d)%nat -> Diagonal d.
Proof.
Admitted.

(* so the law itself is open only from d = 2 on *)
Corollary two_term_law_from_one : forall d : nat, (1 <= d)%nat -> Diagonal d.
Proof.
  intros d Hd. destruct (Nat.eq_dec d 1%nat) as [E|E].
  - subst d. exact diagonal_one.
  - apply two_term_law. lia.
Qed.

(* Equivalently GF_d(x) * s^(2d-1) is a polynomial in s of degree exactly 2d-2,
   so 2d-1 numbers determine the diagonal.  Its coefficients are the backward
   differences of p_d and q_d. *)
Definition rcoef (d : nat) (Dg : Diagonal d) (t : nat) : Q :=
  if Nat.even t
  then let i := Nat.div (2 * d - 2 - t) 2 in
       Qmult (Qdiv (Qn (binomN (2 * i) i)) (Qn (4 ^ i)))
             (delta i (dp d Dg) (Qopp (Qmake 1 2)))
  else let i := Nat.div (2 * d - 3 - t) 2 in
       delta i (dq d Dg) (Qopp 1).

(* The even side.  Writing w_i = C(2i,i)/4^i, the even-index coefficients of R_d
   are w_i Delta^i p_d(-1/2) and the claim R_d(1) = p_d(0) + q_d(0) needs
   sum_i w_i Delta^i f(-1/2) = f(0).  On the binomial basis Delta^i binQ(.,k)(x)
   = binQ(x-i, k-i), so at x = -1/2 the statement is that

     sum_{i<=k} w_i * binQ(-1/2 - i, k-i)  =  0   for k >= 1

   and this collapses termwise: each summand equals (-1)^(k-i) w_k C(k,i), so the
   sum is w_k times the alternating row sum of Pascal's triangle.  The termwise
   identity follows by downward induction on i using wQ's recurrence
   w_i (2i+1) = w_{i+1} (2i+2), the absorption rule binQ_absorb, and
   C(k,i+1) (i+1) = C(k,i) (k-i); the ratio is -(i+1)/(k-i) on both sides.
   binQ, wQ, binQ_absorb, binQ_diag and the arithmetic bridges above are proved,
   and so is the assembly: collapse_term is the termwise identity, collapse_sum
   the vanishing row, and weighted_basis and weighted_sum carry it from the
   binomial basis to an arbitrary polynomial. *)

(* The weights annihilate every binomial basis element of positive degree, and
   fix the constant one. *)
Theorem weighted_basis : forall n k, (k <= n)%nat ->
  sumQn n (fun i => Qmult (wQ i) (delta i (binlist k) (Qopp (Qmake 1 2))))
  == polyQ (binlist k) 0.
Proof.
  intros n k Hk.
  assert (Hz : forall i, (k < i)%nat -> (i <= n)%nat ->
               Qmult (wQ i) (delta i (binlist k) (Qopp (Qmake 1 2))) == 0).
  { intros i H1 H2. destruct i as [|i']; [lia|].
    assert (Hd : delta (S i') (binlist k) (Qopp (Qmake 1 2)) == 0).
    { apply delta_vanishes. rewrite binlist_len. lia. }
    rewrite Hd. ring. }
  rewrite (sumQn_trunc n k _ Hk Hz).
  destruct k as [|k'].
  - cbn [sumQn delta binlist]. change (wQ 0) with (1:Q). simpl. ring.
  - transitivity (sumQn (S k') (fun i =>
        Qmult (wQ i) (binQ (Qminus (Qopp (Qmake 1 2)) (Qn i)) (S k' - i)))).
    { apply sumQn_ext_le. intros i Hi.
      rewrite (delta_binlist i (S k') (Qopp (Qmake 1 2)) Hi). reflexivity. }
    rewrite <- (sumQn_rev (S k') (fun i =>
        Qmult (wQ i) (binQ (Qminus (Qopp (Qmake 1 2)) (Qn i)) (S k' - i)))).
    transitivity (sumQn (S k') (fun j => Qmult (wQ (S k' - j))
        (binQ (Qminus (Qopp (Qmake 1 2)) (Qn (S k' - j))) j))).
    { apply sumQn_ext_le. intros j Hj.
      replace (S k' - (S k' - j))%nat with j by lia. reflexivity. }
    rewrite (collapse_sum (S k') ltac:(lia)).
    rewrite binlist_spec.
    assert (E : (0:Q) == Qn 0) by (rewrite Qn_0; reflexivity).
    rewrite (binQ_ext (S k') _ _ E), (binQ_zero (S k') 0 ltac:(lia)). reflexivity.
Qed.

Lemma binQ_one : forall x, binQ x 1 == x.
Proof.
  intro x. change (binQ x 1)
    with (Qdiv (Qmult (binQ x 0) (Qminus x (Qn 0))) (Qn 1)).
  change (binQ x 0) with (1:Q). rewrite Qn_0, Qn_1. field.
Qed.

(* The i-weighted version on the binomial basis: zero for k >= 2, and 1/2 at
   k = 1, matching (1/2)(binQ 1 k - binQ 0 k). *)
Theorem weighted_i_basis : forall n k, (k <= n)%nat ->
  sumQn n (fun i => Qmult (Qn i)
             (Qmult (wQ i) (delta i (binlist k) (Qopp (Qmake 1 2)))))
  == Qmult (Qdiv 1 2) (Qminus (polyQ (binlist k) 1) (polyQ (binlist k) 0)).
Proof.
  intros n k Hk.
  assert (Hz : forall i, (k < i)%nat -> (i <= n)%nat ->
               Qmult (Qn i) (Qmult (wQ i)
                 (delta i (binlist k) (Qopp (Qmake 1 2)))) == 0).
  { intros i H1 H2. destruct i as [|i']; [lia|].
    assert (Hd : delta (S i') (binlist k) (Qopp (Qmake 1 2)) == 0)
      by (apply delta_vanishes; rewrite binlist_len; lia).
    rewrite Hd. ring. }
  rewrite (sumQn_trunc n k _ Hk Hz).
  destruct k as [|k'].
  - vm_compute. reflexivity.
  - destruct k' as [|k''].
    + vm_compute. reflexivity.
    + rewrite !binlist_spec.
      set (k := S (S k'')) in *.
      assert (Hk2 : (2 <= k)%nat) by (unfold k; lia).
      transitivity (sumQn k (fun i => Qmult (Qn i)
          (Qmult (wQ i)
                 (binQ (Qminus (Qopp (Qmake 1 2)) (Qn i)) (k - i))))).
      { apply sumQn_ext_le. intros i Hi.
        rewrite (delta_binlist i k (Qopp (Qmake 1 2)) Hi). reflexivity. }
      rewrite <- (sumQn_rev k (fun i => Qmult (Qn i)
          (Qmult (wQ i)
                 (binQ (Qminus (Qopp (Qmake 1 2)) (Qn i)) (k - i))))).
      transitivity (sumQn k (fun j => Qmult (Qn (k - j))
          (Qmult (wQ (k - j))
                 (binQ (Qminus (Qopp (Qmake 1 2)) (Qn (k - j))) j)))).
      { apply sumQn_ext_le. intros j Hj.
        replace (k - (k - j))%nat with j by lia. reflexivity. }
      rewrite (collapse_sum_i k Hk2).
      assert (E1 : (1:Q) == Qn 1) by (rewrite Qn_1; reflexivity).
      assert (E0 : (0:Q) == Qn 0) by (rewrite Qn_0; reflexivity).
      rewrite (binQ_ext k _ _ E1), (binQ_ext k _ _ E0).
      rewrite (binQ_zero k 1 ltac:(unfold k; lia)),
              (binQ_zero k 0 ltac:(unfold k; lia)). ring.
Qed.

(* The even-side counterpart of sum_delta: the weighted differences at -1/2
   recover the polynomial at 0.  With c = p_d this is the even half of
   R_d(1) = p_d(0) + q_d(0) and of R_d(-1) = p_d(0) - q_d(0). *)
Theorem weighted_sum : forall n c, (length c <= S n)%nat ->
  sumQn n (fun i => Qmult (wQ i) (delta i c (Qopp (Qmake 1 2)))) == polyQ c 0.
Proof.
  induction n as [|n IH]; intros c Hc.
  - cbn [sumQn delta]. change (wQ 0) with (1:Q).
    destruct c as [|u c]; [simpl; ring|].
    destruct c as [|v c]; simpl in *; [ring | lia].
  - remember (Qmult (nth (S n) c 0%Q) (Qn (factn (S n)))) as lam eqn:Hlam.
    remember (psub c (pscale lam (binlist (S n)))) as d eqn:Hd.
    remember (firstn (S n) d) as c' eqn:Hc'.
    assert (Hdx : forall x, polyQ d x == Qminus (polyQ c x)
                                                (Qmult lam (binQ x (S n)))).
    { intro x. rewrite Hd, psub_spec, pscale_spec, binlist_spec. reflexivity. }
    assert (Htop : forall j, (S n <= j)%nat -> nth j d 0%Q == 0).
    { intros j Hj. rewrite Hd, nth_psub, nth_pscale.
      destruct (Nat.eq_dec j (S n)) as [E|E].
      - subst j. rewrite binlist_lead, Hlam. field.
        apply Qn_pos_nonzero, factn_pos.
      - assert (H1 : nth j c 0%Q = 0%Q) by (apply nth_overflow; lia).
        assert (H2 : nth j (binlist (S n)) 0%Q = 0%Q)
          by (apply nth_overflow; rewrite binlist_len; lia).
        rewrite H1, H2. ring. }
    assert (Hc'x : forall x, polyQ c' x == polyQ d x)
      by (intro x; rewrite Hc'; apply polyQ_firstn; exact Htop).
    assert (Hc'len : (length c' <= S n)%nat)
      by (rewrite Hc'; rewrite length_firstn; lia).
    assert (Hsplit : forall x, polyQ c x
                     == polyQ (padd c' (pscale lam (binlist (S n)))) x).
    { intro x. rewrite padd_spec, pscale_spec, binlist_spec, (Hc'x x), (Hdx x).
      ring. }
    transitivity (sumQn (S n) (fun i =>
        Qplus (Qmult (wQ i) (delta i c' (Qopp (Qmake 1 2))))
              (Qmult lam (Qmult (wQ i)
                                (delta i (binlist (S n)) (Qopp (Qmake 1 2))))))).
    { apply sumQn_ext_le. intros i Hi.
      rewrite (delta_congr i c (padd c' (pscale lam (binlist (S n))))
                           (Qopp (Qmake 1 2)) Hsplit).
      rewrite delta_padd, delta_pscale. ring. }
    rewrite sumQn_add.
    rewrite (sumQn_scal (S n) lam
              (fun i => Qmult (wQ i)
                              (delta i (binlist (S n)) (Qopp (Qmake 1 2))))).
    rewrite (weighted_basis (S n) (S n) ltac:(lia)).
    rewrite binlist_spec.
    assert (E0 : (0:Q) == Qn 0) by (rewrite Qn_0; reflexivity).
    rewrite (binQ_ext (S n) _ _ E0), (binQ_zero (S n) 0 ltac:(lia)).
    assert (Hlast : Qmult (wQ (S n)) (delta (S n) c' (Qopp (Qmake 1 2))) == 0).
    { assert (Z : delta (S n) c' (Qopp (Qmake 1 2)) == 0)
        by (apply delta_vanishes; exact Hc'len).
      rewrite Z. ring. }
    change (sumQn (S n) (fun i => Qmult (wQ i) (delta i c' (Qopp (Qmake 1 2)))))
      with (Qplus (sumQn n (fun i => Qmult (wQ i) (delta i c' (Qopp (Qmake 1 2)))))
                  (Qmult (wQ (S n)) (delta (S n) c' (Qopp (Qmake 1 2))))).
    rewrite Hlast, (IH c' Hc'len), (Hc'x 0), (Hdx 0).
    assert (E1 : binQ (0:Q) (S n) == 0).
    { rewrite (binQ_ext (S n) _ _ E0). apply binQ_zero. lia. }
    rewrite E1. ring.
Qed.

Theorem weighted_i_sum : forall n c, (length c <= S n)%nat ->
  sumQn n (fun i => Qmult (Qn i)
             (Qmult (wQ i) (delta i c (Qopp (Qmake 1 2)))))
  == Qmult (Qdiv 1 2) (Qminus (polyQ c 1) (polyQ c 0)).
Proof.
  induction n as [|n IH]; intros c Hc.
  - cbn [sumQn]. rewrite Qn_0.
    destruct c as [|u c]; [simpl; ring|].
    destruct c as [|v c]; simpl in *; [ring | lia].
  - remember (Qmult (nth (S n) c 0%Q) (Qn (factn (S n)))) as lam eqn:Hlam.
    remember (psub c (pscale lam (binlist (S n)))) as d eqn:Hd.
    remember (firstn (S n) d) as c' eqn:Hc'.
    assert (Hdx : forall x, polyQ d x
                            == Qminus (polyQ c x) (Qmult lam (binQ x (S n)))).
    { intro x. rewrite Hd, psub_spec, pscale_spec, binlist_spec. reflexivity. }
    assert (Htop : forall j, (S n <= j)%nat -> nth j d 0%Q == 0).
    { intros j Hj. rewrite Hd, nth_psub, nth_pscale.
      destruct (Nat.eq_dec j (S n)) as [E|E].
      - subst j. rewrite binlist_lead, Hlam. field.
        apply Qn_pos_nonzero, factn_pos.
      - assert (H1 : nth j c 0%Q = 0%Q) by (apply nth_overflow; lia).
        assert (H2 : nth j (binlist (S n)) 0%Q = 0%Q)
          by (apply nth_overflow; rewrite binlist_len; lia).
        rewrite H1, H2. ring. }
    assert (Hc'x : forall x, polyQ c' x == polyQ d x)
      by (intro x; rewrite Hc'; apply polyQ_firstn; exact Htop).
    assert (Hc'len : (length c' <= S n)%nat)
      by (rewrite Hc'; rewrite length_firstn; lia).
    assert (Hsplit : forall x, polyQ c x
                     == polyQ (padd c' (pscale lam (binlist (S n)))) x).
    { intro x. rewrite padd_spec, pscale_spec, binlist_spec, (Hc'x x), (Hdx x).
      ring. }
    transitivity (sumQn (S n) (fun i =>
        Qplus (Qmult (Qn i) (Qmult (wQ i) (delta i c' (Qopp (Qmake 1 2)))))
              (Qmult lam (Qmult (Qn i) (Qmult (wQ i)
                   (delta i (binlist (S n)) (Qopp (Qmake 1 2)))))))).
    { apply sumQn_ext_le. intros i Hi.
      rewrite (delta_congr i c (padd c' (pscale lam (binlist (S n))))
                           (Qopp (Qmake 1 2)) Hsplit).
      rewrite delta_padd, delta_pscale. ring. }
    rewrite sumQn_add.
    rewrite (sumQn_scal (S n) lam
              (fun i => Qmult (Qn i) (Qmult (wQ i)
                   (delta i (binlist (S n)) (Qopp (Qmake 1 2)))))).
    rewrite (weighted_i_basis (S n) (S n) ltac:(lia)).
    assert (Hlast : Qmult (Qn (S n)) (Qmult (wQ (S n))
                      (delta (S n) c' (Qopp (Qmake 1 2)))) == 0).
    { assert (Z : delta (S n) c' (Qopp (Qmake 1 2)) == 0)
        by (apply delta_vanishes; exact Hc'len).
      rewrite Z. ring. }
    change (sumQn (S n) (fun i => Qmult (Qn i)
              (Qmult (wQ i) (delta i c' (Qopp (Qmake 1 2))))))
      with (Qplus (sumQn n (fun i => Qmult (Qn i)
                     (Qmult (wQ i) (delta i c' (Qopp (Qmake 1 2))))))
                  (Qmult (Qn (S n)) (Qmult (wQ (S n))
                     (delta (S n) c' (Qopp (Qmake 1 2)))))).
    rewrite Hlast, (IH c' Hc'len), !binlist_spec.
    rewrite (Hc'x 1), (Hc'x 0), (Hdx 1), (Hdx 0). ring.
Qed.

Lemma wQ_div : forall i, wQ i == Qdiv (Qn (binomN (2 * i) i)) (Qn (4 ^ i)).
Proof.
  intro i. rewrite <- (wQ_eq i). field.
  apply Qn_pos_nonzero, four_pow_pos.
Qed.

Lemma rcoef_even : forall d (Dg : Diagonal d) i,
  (1 <= d)%nat -> (i <= d - 1)%nat ->
  rcoef d Dg (2 * d - 2 - 2 * i)
  == Qmult (wQ i) (delta i (dp d Dg) (Qopp (Qmake 1 2))).
Proof.
  intros d Dg i Hd Hi.
  assert (Ht : (2 * d - 2 - 2 * i = 2 * (d - 1 - i))%nat) by lia.
  unfold rcoef. rewrite Ht, Nat.even_mul. cbn [Nat.even orb].
  replace (2 * d - 2 - 2 * (d - 1 - i))%nat with (i * 2)%nat by lia.
  rewrite (Nat.div_mul i 2 ltac:(lia)), <- wQ_div. reflexivity.
Qed.

(* The even-index coefficients of R_d are w_i Delta^i p_d(-1/2) for i = 0..d-1,
   so by weighted_sum they add to p_d(0).  With odd_coeffs_sum this gives
   R_d(1) = p_d(0) + q_d(0) and R_d(-1) = p_d(0) - q_d(0). *)
Theorem even_coeffs_sum : forall d (Dg : Diagonal d), (1 <= d)%nat ->
  sumQn (d - 1) (fun i => rcoef d Dg (2 * d - 2 - 2 * i))
  == polyQ (dp d Dg) 0.
Proof.
  intros d Dg Hd.
  transitivity (sumQn (d - 1)
    (fun i => Qmult (wQ i) (delta i (dp d Dg) (Qopp (Qmake 1 2))))).
  { apply sumQn_ext_le. intros i Hi. apply rcoef_even; assumption. }
  apply weighted_sum. rewrite (dp_len d Dg). lia.
Qed.

Theorem even_coeffs_weighted : forall d (Dg : Diagonal d), (1 <= d)%nat ->
  sumQn (d - 1) (fun i => Qmult (Qn i) (rcoef d Dg (2 * d - 2 - 2 * i)))
  == Qmult (Qdiv 1 2) (Qminus (polyQ (dp d Dg) 1) (polyQ (dp d Dg) 0)).
Proof.
  intros d Dg Hd.
  transitivity (sumQn (d - 1) (fun i => Qmult (Qn i)
      (Qmult (wQ i) (delta i (dp d Dg) (Qopp (Qmake 1 2)))))).
  { apply sumQn_ext_le. intros i Hi.
    rewrite (rcoef_even d Dg i Hd Hi). reflexivity. }
  apply weighted_i_sum. rewrite (dp_len d Dg). lia.
Qed.

(* The odd-index coefficients of R_d are delta i q_d(-1) for i = 0..d-2, so by
   sum_delta they add to q_d(0).  This is the odd half of R_d(1) = p_d(0) + q_d(0)
   and of R_d(-1) = p_d(0) - q_d(0).  The even half needs
   sum_i (C(2i,i)/4^i) Delta^i f(-1/2) = f(0), Chu-Vandermonde in the binomial
   basis, which weighted_sum proves by a termwise collapse. *)
Theorem odd_coeffs_sum : forall (d : nat) (Dg : Diagonal d), (2 <= d)%nat ->
  Qeq (sumQn (d - 2) (fun i => delta i (dq d Dg) (Qopp 1)))
      (polyQ (dq d Dg) 0).
Proof.
  intros d Dg Hd.
  transitivity (sumQn (d - 2) (fun i => delta i (dq d Dg) (Qminus 0 1))).
  - apply sumQn_ext. intro i. apply delta_ext. ring.
  - apply sum_delta. rewrite (dq_len d Dg). lia.
Qed.

Lemma rcoef_odd : forall d (Dg : Diagonal d) i,
  (2 <= d)%nat -> (i <= d - 2)%nat ->
  rcoef d Dg (2 * d - 3 - 2 * i) == delta i (dq d Dg) (Qopp 1).
Proof.
  intros d Dg i Hd Hi.
  assert (Ht : (2 * d - 3 - 2 * i = S (2 * (d - 2 - i)))%nat) by lia.
  unfold rcoef. rewrite Ht, Nat.even_succ, Nat.odd_mul. cbn [Nat.odd andb].
  replace (2 * d - 3 - S (2 * (d - 2 - i)))%nat with (i * 2)%nat by lia.
  rewrite (Nat.div_mul i 2 ltac:(lia)). reflexivity.
Qed.

Theorem odd_coeffs_sum_rcoef : forall d (Dg : Diagonal d), (2 <= d)%nat ->
  sumQn (d - 2) (fun i => rcoef d Dg (2 * d - 3 - 2 * i))
  == polyQ (dq d Dg) 0.
Proof.
  intros d Dg Hd.
  transitivity (sumQn (d - 2) (fun i => delta i (dq d Dg) (Qopp 1))).
  { apply sumQn_ext_le. intros i Hi. apply rcoef_odd; assumption. }
  apply odd_coeffs_sum. exact Hd.
Qed.

(* The i-weighted odd sum, which is one of the four pieces of R_d'(-1). *)
Theorem odd_coeffs_weighted : forall d (Dg : Diagonal d), (2 <= d)%nat ->
  sumQn (d - 2) (fun i => Qmult (Qn i) (rcoef d Dg (2 * d - 3 - 2 * i)))
  == Qminus (polyQ (dq d Dg) 1) (polyQ (dq d Dg) 0).
Proof.
  intros d Dg Hd.
  transitivity (sumQn (d - 2)
    (fun i => Qmult (Qn i) (delta i (dq d Dg) (Qminus 0 1)))).
  { apply sumQn_ext_le. intros i Hi.
    rewrite (rcoef_odd d Dg i Hd Hi).
    assert (E : delta i (dq d Dg) (Qopp 1) == delta i (dq d Dg) (Qminus 0 1))
      by (apply delta_ext; ring).
    rewrite E. reflexivity. }
  rewrite (sum_i_delta (d - 2) (dq d Dg) 0
             ltac:(rewrite (dq_len d Dg); lia)).
  assert (E1 : Qplus (0:Q) 1 == 1) by ring.
  rewrite (polyQ_ext (dq d Dg) _ _ E1). reflexivity.
Qed.

(* R_d(1) and R_d(-1) in terms of p_d and q_d.  R_d(1) = A061552(d) and
   R_d(-1) = 1 are then exactly p_d(0) + q_d(0) = A061552(d) and
   p_d(0) - q_d(0) = 1. *)
Theorem R_at_one : forall d (Dg : Diagonal d), (2 <= d)%nat ->
  Qeq (Qplus (sumQn (d - 1) (fun i => rcoef d Dg (2 * d - 2 - 2 * i)))
             (sumQn (d - 2) (fun i => rcoef d Dg (2 * d - 3 - 2 * i))))
      (Qplus (polyQ (dp d Dg) 0) (polyQ (dq d Dg) 0)).
Proof.
  intros d Dg Hd.
  rewrite (even_coeffs_sum d Dg ltac:(lia)), (odd_coeffs_sum_rcoef d Dg Hd).
  reflexivity.
Qed.

Theorem R_at_minus_one_split : forall d (Dg : Diagonal d), (2 <= d)%nat ->
  Qeq (Qminus (sumQn (d - 1) (fun i => rcoef d Dg (2 * d - 2 - 2 * i)))
              (sumQn (d - 2) (fun i => rcoef d Dg (2 * d - 3 - 2 * i))))
      (Qminus (polyQ (dp d Dg) 0) (polyQ (dq d Dg) 0)).
Proof.
  intros d Dg Hd.
  rewrite (even_coeffs_sum d Dg ltac:(lia)), (odd_coeffs_sum_rcoef d Dg Hd).
  reflexivity.
Qed.

(* Evaluating the two-term law at M = 0, 1, 2, where Ddiag_short makes the left
   side the counting sequence, so these are identities between the two
   polynomials and card.  With R_at_one they give R_d(1) = A061552(d); the
   companion R_d(-1) = 1 is p(0) - q(0) and stays open. *)

Theorem two_term_at_zero : forall d (Dg : Diagonal d),
  Qeq (Qplus (polyQ (dp d Dg) 0) (polyQ (dq d Dg) 0)) (Qn (card d)).
Proof.
  intros d Dg. assert (H := d_law d Dg 0%nat).
  rewrite (Ddiag_short d 0%nat ltac:(lia)) in H.
  replace (0 + d)%nat with d in H by lia.
  assert (E0 : Qn 0 == 0) by apply Qn_0.
  rewrite (polyQ_ext (dp d Dg) (Qn 0) 0 E0) in H.
  rewrite (polyQ_ext (dq d Dg) (Qn 0) 0 E0) in H.
  replace (2 * 0)%nat with 0%nat in H by lia.
  change (binomN 0 0) with 1%nat in H.
  change (4 ^ 0)%nat with 1%nat in H.
  rewrite Qn_1 in H. rewrite H. ring.
Qed.

Theorem two_term_at_one : forall d (Dg : Diagonal d),
  Qeq (Qplus (Qmult 2 (polyQ (dp d Dg) 1)) (Qmult 4 (polyQ (dq d Dg) 1)))
      (Qn (card (S d))).
Proof.
  intros d Dg. assert (H := d_law d Dg 1%nat).
  rewrite (Ddiag_short d 1%nat ltac:(lia)) in H.
  replace (1 + d)%nat with (S d) in H by lia.
  assert (E1 : Qn 1 == 1) by apply Qn_1.
  rewrite (polyQ_ext (dp d Dg) (Qn 1) 1 E1) in H.
  rewrite (polyQ_ext (dq d Dg) (Qn 1) 1 E1) in H.
  replace (2 * 1)%nat with 2%nat in H by lia.
  change (binomN 2 1) with 2%nat in H.
  change (4 ^ 1)%nat with 4%nat in H.
  assert (E2 : Qn 2 == 2) by apply Qn2.
  assert (E4 : Qn 4 == 4) by (unfold Qn, Qeq; simpl; lia).
  rewrite E2, E4 in H. rewrite H. ring.
Qed.

Theorem two_term_at_two : forall d (Dg : Diagonal d),
  Qeq (Qplus (Qmult 6 (polyQ (dp d Dg) 2)) (Qmult 16 (polyQ (dq d Dg) 2)))
      (Qn (card (S (S d)))).
Proof.
  intros d Dg. assert (H := d_law d Dg 2%nat).
  rewrite (Ddiag_short d 2%nat ltac:(lia)) in H.
  replace (2 + d)%nat with (S (S d)) in H by lia.
  assert (E2 : Qn 2 == 2) by apply Qn2.
  rewrite (polyQ_ext (dp d Dg) (Qn 2) 2 E2) in H.
  rewrite (polyQ_ext (dq d Dg) (Qn 2) 2 E2) in H.
  replace (2 * 2)%nat with 4%nat in H by lia.
  change (binomN 4 2) with 6%nat in H.
  change (4 ^ 2)%nat with 16%nat in H.
  assert (E6 : Qn 6 == 6) by (unfold Qn, Qeq; simpl; lia).
  assert (E16 : Qn 16 == 16) by (unfold Qn, Qeq; simpl; lia).
  rewrite E6, E16 in H. rewrite H. ring.
Qed.

(* R_d(1) = A061552(d): the coefficients of R_d add to the counting sequence. *)
Corollary R_at_one_card : forall d (Dg : Diagonal d), (2 <= d)%nat ->
  Qeq (Qplus (sumQn (d - 1) (fun i => rcoef d Dg (2 * d - 2 - 2 * i)))
             (sumQn (d - 2) (fun i => rcoef d Dg (2 * d - 3 - 2 * i))))
      (Qn (card d)).
Proof.
  intros d Dg Hd. rewrite (R_at_one d Dg Hd). apply two_term_at_zero.
Qed.

(* The coefficient degrees, observed as 0, 4, 8 on the p side and 2, 6 on the q
   side; the exponent law follows from them. *)
Theorem p_degree_pattern : forall j : nat,
  exists c : list Q, length c = S (4 * j) /\
    forall (d : nat) (Dg : Diagonal d), (j < d)%nat ->
      Qeq (Qmult (Qn (factn d)) (nth (d - 1 - j) (dp d Dg) 0%Q))
          (polyQ c (Qn d)).
Proof.
Admitted.

Theorem q_degree_pattern : forall j : nat,
  exists c : list Q, length c = S (2 + 4 * j) /\
    forall (d : nat) (Dg : Diagonal d), (S j < d)%nat ->
      Qeq (Qmult (Qn (factn d)) (nth (d - 2 - j) (dq d Dg) 0%Q))
          (polyQ c (Qn d)).
Proof.
Admitted.

(* R_d(-1) = p_d(0) - q_d(0) = 1: the decreasing suffix pattern contributes
   Cat(M) C(M+d,d) and every other pattern contributes 0. *)
Theorem R_at_minus_one : forall (d : nat) (Dg : Diagonal d), (1 <= d)%nat ->
  Qeq (Qminus (polyQ (dp d Dg) 0) (polyQ (dq d Dg) 0)) 1.
Proof.
Admitted.

(* R_d'(-1), obtained by differentiating the operator identity.  Grouping
   R_d(s) = sum_i a_i s^(2d-2-2i) + sum_i b_i s^(2d-3-2i) and differentiating at
   s = -1 gives

     R_d'(-1) = -(2d-2) sum a_i + 2 sum i a_i + (2d-3) sum b_i - 2 sum i b_i

   and the four sums are even_coeffs_sum, even_coeffs_weighted,
   odd_coeffs_sum_rcoef and odd_coeffs_weighted, using
   sum_i i (C(2i,i)/4^i) Delta^i = (1/2)(E^(3/2) - E^(1/2)) and
   sum_i i Delta^i = E^2 - E.  Since R_d(-1) = p_d(0) - q_d(0), the nearest zero
   of R_d sits at 1 + rho = -R_d(-1)/R_d'(-1), so mu is the growth rate of
   |p_d(1) - 2 q_d(1)|. *)
Theorem R_deriv_at_minus_one : forall (d : nat) (Dg : Diagonal d), (2 <= d)%nat ->
  Qeq (Qplus (Qplus (Qmult (Qopp (Qn (2 * d - 2)))
                           (sumQn (d - 1) (fun i => rcoef d Dg (2 * d - 2 - 2 * i))))
                    (Qmult 2
                           (sumQn (d - 1) (fun i => Qmult (Qn i)
                                             (rcoef d Dg (2 * d - 2 - 2 * i))))))
             (Qminus (Qmult (Qn (2 * d - 3))
                            (sumQn (d - 2) (fun i => rcoef d Dg (2 * d - 3 - 2 * i))))
                     (Qmult 2
                            (sumQn (d - 2) (fun i => Qmult (Qn i)
                                              (rcoef d Dg (2 * d - 3 - 2 * i)))))))
      (Qminus (Qminus (polyQ (dp d Dg) 1) (Qmult 2 (polyQ (dq d Dg) 1)))
              (Qmult (Qn (2 * d - 1))
                     (Qminus (polyQ (dp d Dg) 0) (polyQ (dq d Dg) 0)))).
Proof.
  intros d Dg Hd.
  rewrite (even_coeffs_sum d Dg ltac:(lia)),
          (even_coeffs_weighted d Dg ltac:(lia)),
          (odd_coeffs_sum_rcoef d Dg Hd),
          (odd_coeffs_weighted d Dg Hd).
  assert (E1 : Qn (2 * d - 2) == Qplus (Qn (2 * d - 3)) 1).
  { replace (2 * d - 2)%nat with ((2 * d - 3) + 1)%nat by lia.
    rewrite Qn_add, Qn_1. reflexivity. }
  assert (E2 : Qn (2 * d - 1) == Qplus (Qn (2 * d - 3)) 2).
  { replace (2 * d - 1)%nat with ((2 * d - 3) + 2)%nat by lia.
    rewrite Qn_add, Qn2. reflexivity. }
  rewrite E1, E2. field.
Qed.

(* The derivative at -1, reduced to two consecutive terms of the counting sequence. *)
Corollary R_deriv_from_card : forall d (Dg : Diagonal d), (2 <= d)%nat ->
  Qeq (Qminus (polyQ (dp d Dg) 0) (polyQ (dq d Dg) 0)) 1 ->
  Qeq (Qplus (Qplus (Qmult (Qopp (Qn (2 * d - 2)))
                           (sumQn (d - 1) (fun i => rcoef d Dg (2 * d - 2 - 2 * i))))
                    (Qmult 2
                           (sumQn (d - 1) (fun i => Qmult (Qn i)
                                             (rcoef d Dg (2 * d - 2 - 2 * i))))))
             (Qminus (Qmult (Qn (2 * d - 3))
                            (sumQn (d - 2) (fun i => rcoef d Dg (2 * d - 3 - 2 * i))))
                     (Qmult 2
                            (sumQn (d - 2) (fun i => Qmult (Qn i)
                                              (rcoef d Dg (2 * d - 3 - 2 * i)))))))
      (Qminus (Qminus (polyQ (dp d Dg) 1) (Qmult 2 (polyQ (dq d Dg) 1)))
              (Qn (2 * d - 1))).
Proof.
  intros d Dg Hd Hone.
  rewrite (R_deriv_at_minus_one d Dg Hd), Hone. ring.
Qed.

(* At fixed t the family [s^t]R_d is polynomially bounded in d, which is what
   makes every rho_t analytic in the unit disc while their sum is not. *)
Theorem exponent_law : forall t : nat,
  exists (C : Q) (k : nat),
    forall (d : nat) (Dg : Diagonal d), (t <= 2 * d - 2)%nat ->
      Qle (Qabs (rcoef d Dg t)) (Qmult C (Qn (d ^ k))).
Proof.
Admitted.

(* No congruence for ext of index 2^m decides both legality and the 132-free step. *)

Open Scope nat_scope.

Definition Coarsening : Prop :=
  exists (St : Type) (abs : list nat -> St) (stp : St -> nat -> St)
         (legb : St -> nat -> bool) (cutb : St -> nat -> bool)
         (enum : nat -> list St),
    (forall u y, abs (ext u y) = stp (abs u) y) /\
    (forall u y, legb (abs u) y = true <-> legal u y) /\
    (forall u y, cutb (abs u) y = true <-> safe_at u y) /\
    (forall m w, is_perm w m -> ~ contains_1324 w -> In (abs w) (enum m)) /\
    (forall m : nat, (length (enum m) <= 2 ^ m)%nat).

(* The number of legal letters at or below the current length.  It is a
   function of legality alone, so any state deciding legality determines it. *)
Definition mstat (u : list nat) : nat :=
  length (filter (legalb u) (seq 0 (S (length u)))).

(* One step of lookahead: the legal-letter count after each possible letter.
   Conditions (1) and (2) force this to factor through abs, so the number of
   distinct values it takes on words of length m bounds the state count. *)
Definition Phi (u : list nat) : list nat :=
  map (fun y => mstat (ext u y)) (seq 0 (S (length u))).

(* Deduplicate by the second component, so Phi is evaluated once per word
   rather than once per comparison. *)
Fixpoint dedup_snd (l : list (list nat * list nat)) : list (list nat * list nat) :=
  match l with
  | nil => nil
  | p :: r =>
      let d := dedup_snd r in
      if existsb (fun q => if list_eq_dec Nat.eq_dec (snd q) (snd p)
                           then true else false) d
      then d else p :: d
  end.

Definition phipairs : list (list nat * list nat) :=
  map (fun w => (w, Phi w)) (gen 4).

Lemma dedup_snd_incl : forall l p, In p (dedup_snd l) -> In p l.
Proof.
  induction l as [|a r IH]; intros p H; [contradiction|].
  cbn [dedup_snd] in H.
  destruct (existsb (fun q => if list_eq_dec Nat.eq_dec (snd q) (snd a)
                              then true else false) (dedup_snd r)) eqn:E.
  - right. apply IH. exact H.
  - destruct H as [<- | H]; [left; reflexivity | right; apply IH; exact H].
Qed.

Lemma dedup_snd_nodup : forall l, NoDup (dedup_snd l).
Proof.
  induction l as [|a r IH]; [constructor|].
  cbn [dedup_snd].
  destruct (existsb (fun q => if list_eq_dec Nat.eq_dec (snd q) (snd a)
                              then true else false) (dedup_snd r)) eqn:E;
    [exact IH|].
  constructor; [| exact IH].
  intro Hin.
  assert (K : existsb (fun q => if list_eq_dec Nat.eq_dec (snd q) (snd a)
                                then true else false) (dedup_snd r) = true).
  { apply existsb_exists. exists a. split; [exact Hin|].
    destruct (list_eq_dec Nat.eq_dec (snd a) (snd a));
      [reflexivity | contradiction]. }
  rewrite E in K. discriminate.
Qed.

Lemma dedup_snd_distinct : forall l p q,
  In p (dedup_snd l) -> In q (dedup_snd l) -> snd p = snd q -> p = q.
Proof.
  induction l as [|a r IH]; intros p q Hp Hq Hf; [contradiction|].
  cbn [dedup_snd] in Hp, Hq.
  destruct (existsb (fun z => if list_eq_dec Nat.eq_dec (snd z) (snd a)
                              then true else false) (dedup_snd r)) eqn:E.
  - exact (IH p q Hp Hq Hf).
  - assert (Hno : forall z, In z (dedup_snd r) -> snd z <> snd a).
    { intros z Hz Hc.
      assert (K : existsb (fun y => if list_eq_dec Nat.eq_dec (snd y) (snd a)
                                    then true else false) (dedup_snd r) = true).
      { apply existsb_exists. exists z. split; [exact Hz|].
        destruct (list_eq_dec Nat.eq_dec (snd z) (snd a));
          [reflexivity | contradiction]. }
      rewrite E in K. discriminate. }
    destruct Hp as [<- | Hp]; destruct Hq as [<- | Hq].
    + reflexivity.
    + exfalso. apply (Hno q Hq). symmetry. exact Hf.
    + exfalso. apply (Hno p Hp). exact Hf.
    + exact (IH p q Hp Hq Hf).
Qed.

(* cbn on the projections only.  simpl here would try to evaluate gen 4 and Phi
   through the decision procedures and never return. *)
Lemma phipairs_shape : forall p, In p phipairs ->
  In (fst p) (gen 4) /\ snd p = Phi (fst p).
Proof.
  intros p Hp. unfold phipairs in Hp. apply in_map_iff in Hp.
  destruct Hp as [w [Hw Hin]]. subst p. cbn [fst snd].
  split; [exact Hin | reflexivity].
Qed.

(* Stated over an abstract list.  Applying in_map_iff to a concrete one puts
   the list in head position, and whnf then evaluates it. *)
Lemma incl_map_of : forall (A B : Type) (f : A -> B) (l : list A) (L : list B),
  (forall a, In a l -> In (f a) L) -> incl (map f l) L.
Proof.
  intros A B f l L H b Hb. apply in_map_iff in Hb.
  destruct Hb as [a [Ha Hin]]. subst b. apply H. exact Hin.
Qed.

(* The count at top level: vm_compute under a local context falls back to lazy. *)
Lemma witness_19 : length (dedup_snd phipairs) = 19.
Proof. vm_compute. reflexivity. Qed.

(* At length 4 there are 23 avoiders and 19 distinct one-step lookaheads,
   against the 16 states a 2^m coarsening allows. *)
Theorem no_coarsening : ~ Coarsening.
Proof.
  intros [St [abs [stp [legb [cutb [enum [H1 [H2 [H3 [H4 H5]]]]]]]]]].
  assert (Hleg : forall u u' y, abs u = abs u' -> legalb u y = legalb u' y).
  { intros u u' y Ha.
    destruct (legalb u y) eqn:Eu; destruct (legalb u' y) eqn:Eu'; try reflexivity.
    - exfalso.
      assert (Lu : legal u y) by (apply legalb_spec; exact Eu).
      assert (Bu : legb (abs u) y = true) by (apply H2; exact Lu).
      rewrite Ha in Bu.
      assert (Lu' : legal u' y) by (apply H2; exact Bu).
      assert (Eu2 : legalb u' y = true) by (apply legalb_spec; exact Lu').
      rewrite Eu' in Eu2. discriminate.
    - exfalso.
      assert (Lu : legal u' y) by (apply legalb_spec; exact Eu').
      assert (Bu : legb (abs u') y = true) by (apply H2; exact Lu).
      rewrite <- Ha in Bu.
      assert (Lu' : legal u y) by (apply H2; exact Bu).
      assert (Eu2 : legalb u y = true) by (apply legalb_spec; exact Lu').
      rewrite Eu in Eu2. discriminate. }
  assert (Hm : forall u u', abs u = abs u' -> length u = length u' ->
                            mstat u = mstat u').
  { intros u u' Ha Hl. unfold mstat. rewrite Hl. f_equal.
    apply filter_ext_in_nat. intros y _. apply Hleg. exact Ha. }
  assert (HPhi : forall u u', abs u = abs u' -> length u = length u' ->
                              Phi u = Phi u').
  { intros u u' Ha Hl. unfold Phi. rewrite Hl. apply map_ext. intro y.
    apply Hm; [rewrite !H1, Ha; reflexivity | rewrite !ext_length, Hl; reflexivity]. }
  assert (HW : (length (dedup_snd phipairs) = 19)%nat) by exact witness_19.
  assert (Hsh : forall p, In p (dedup_snd phipairs) ->
                  In (fst p) (gen 4) /\ snd p = Phi (fst p))
    by (intros p Hp; apply phipairs_shape; exact (dedup_snd_incl phipairs p Hp)).
  assert (Hlen4 : forall p, In p (dedup_snd phipairs) -> length (fst p) = 4%nat).
  { intros p Hp. destruct (Hsh p Hp) as [Hg _]. apply gen_spec in Hg.
    destruct Hg as [[Hl _] _]. exact Hl. }
  assert (Hnd : NoDup (map (fun p => abs (fst p)) (dedup_snd phipairs))).
  { apply NoDup_map_inj; [apply dedup_snd_nodup|].
    intros x y Hx Hy Hab.
    apply (dedup_snd_distinct phipairs x y Hx Hy).
    destruct (Hsh x Hx) as [_ Ex]. destruct (Hsh y Hy) as [_ Ey].
    rewrite Ex, Ey. apply HPhi;
      [exact Hab | rewrite (Hlen4 x Hx), (Hlen4 y Hy); reflexivity]. }
  assert (Hincl : incl (map (fun p => abs (fst p)) (dedup_snd phipairs))
                       (enum 4)).
  { apply incl_map_of. intros p Hpin.
    destruct (Hsh p Hpin) as [Hg _]. apply gen_spec in Hg.
    destruct Hg as [Hperm Hav]. exact (H4 4%nat (fst p) Hperm Hav). }
  assert (K := NoDup_incl_length Hnd Hincl).
  rewrite len_map_gen, HW in K.
  assert (K2 := H5 4%nat).
  change (2 ^ 4)%nat with 16%nat in K2. lia.
Qed.

Close Scope nat_scope.

Fixpoint polyZ (c : list Z) (n : nat) : Z :=
  match c with [] => 0%Z | a :: r => (a + Z.of_nat n * polyZ r n)%Z end.

(* P-recursive: a nontrivial linear recurrence with polynomial coefficients. *)
Definition Precursive (a : nat -> Z) : Prop :=
  exists (r : nat) (C : nat -> list Z),
    (exists j, (j <= r)%nat /\ exists x, In x (C j) /\ x <> 0%Z) /\
    forall n : nat, (1 <= n)%nat ->
      fold_right Z.add 0%Z
        (map (fun j => (polyZ (C j) n * a (n + j)%nat)%Z) (seq 0 (S r))) = 0%Z.

(* Conway, Guttmann and Zinn-Justin give numerical evidence from 50 terms. *)
Theorem av1324_not_Precursive :
  ~ Precursive (fun n => Z.of_nat (card n)).
Proof.
Admitted.

(* ------------------------------------------------------------------ *)
(* The m = 5 computations. *)

Open Scope nat_scope.

Theorem domino_5 : Z.of_nat (Dcount 5 5) = 255642%Z.
Proof. rewrite <- Dcountf_eq. vm_compute. reflexivity. Qed.

Theorem tromino_count_3 : Tromino 3 = Tcount 3.
Proof. apply tromino_eq_Tcount. Qed.

Theorem tromino_3 : Z.of_nat (Tromino 3) = 36325%Z.
Proof.
  rewrite tromino_eq_Tcount, <- Tz_eq, <- Tzf_eq. vm_compute. reflexivity.
Qed.

Theorem tromino_5 : Tz 5 = 1615228302%Z.
Proof. rewrite <- Tzf_eq. vm_compute. reflexivity. Qed.

Lemma card132_5_val : card132 5 = 42%nat.
Proof. vm_compute. reflexivity. Qed.

(* 255642^2 = 65352832164 against 42 * 1615228302 = 67839588684 *)
Lemma chebyshevZ_5 : chebyshev_holdsZ 5 = true.
Proof.
  apply (chebyshevZ_of_vals 5 255642 1615228302 42
           domino_5 tromino_5 card132_5_val).
  reflexivity.
Qed.

Theorem chebyshevZ_upto_5 : forall m, (m <= 5)%nat -> chebyshev_holdsZ m = true.
Proof.
  intros m Hm.
  destruct m as [|[|[|[|[|[|m]]]]]]; try lia.
  - rewrite <- chebyshev_holdsZf_eq; vm_compute; reflexivity.
  - rewrite <- chebyshev_holdsZf_eq; vm_compute; reflexivity.
  - rewrite <- chebyshev_holdsZf_eq; vm_compute; reflexivity.
  - rewrite <- chebyshev_holdsZf_eq; vm_compute; reflexivity.
  - exact chebyshevZ_4.
  - exact chebyshevZ_5.
Qed.

Corollary chebyshev_le_5 : forall m, (m <= 5)%nat ->
  (Z.of_nat (Dcount m m) * Z.of_nat (Dcount m m)
   <= Z.of_nat (card132 m) * Z.of_nat (Tcount m))%Z.
Proof.
  intros m Hm. apply chebyshev_holds_spec.
  rewrite <- chebyshev_holdsZ_eq. apply chebyshevZ_upto_5. exact Hm.
Qed.

(* ------------------------------------------------------------------ *)
(* The d = 2 diagonal.  Only two suffix patterns occur, the decreasing one is
   Nsig_dec, and the whole of the case sits in the increasing fibre. *)

Lemma perm_two_cases : forall l, is_perm l 2 -> l = [0; 1] \/ l = [1; 0].
Proof.
  intros l [Hlen [Hnd Hb]].
  destruct l as [|a [|b [|c l]]]; cbn [length] in Hlen; try discriminate.
  assert (Ha : a < 2) by (apply Hb; left; reflexivity).
  assert (Hbb : b < 2) by (apply Hb; right; left; reflexivity).
  assert (Hab : a <> b).
  { inversion Hnd as [|x xs Hni Hr Heq]; subst. intro E. apply Hni. left.
    symmetry. exact E. }
  destruct a as [|[|a]]; destruct b as [|[|b]]; try lia;
    first [left; reflexivity | right; reflexivity].
Qed.

Lemma decpat_two : decpat 2 = [1; 0].
Proof. reflexivity. Qed.

Theorem Ddiag_two : forall M,
  Ddiag 2 M = (binomN (M + 2) 2 * card132 M + Nsig 2 M [0; 1])%nat.
Proof.
  intro M.
  assert (Hcov : forall w,
            In w (filter (fun w => avoids132b (firstn M w)) (gen (M + 2))) ->
            In (suffix_pat 2 w) [[1; 0]; [0; 1]]).
  { intros w Hw. apply filter_In in Hw. destruct Hw as [Hg _].
    apply gen_spec in Hg. destruct Hg as [[Hlen [Hnd _]] _].
    rewrite (suffix_pat_skipn 2 M w Hlen).
    assert (Hsk : length (skipn M w) = 2)
      by (rewrite length_skipn, Hlen; lia).
    assert (Hp : is_perm (std (skipn M w)) 2).
    { assert (K := std_is_perm (skipn M w) (NoDup_skipn w M Hnd)).
      rewrite Hsk in K. exact K. }
    destruct (perm_two_cases _ Hp) as [E|E]; rewrite E;
      [right; left | left]; reflexivity. }
  assert (Hnd : NoDup [[1; 0]; [0; 1]]).
  { constructor; [| constructor; [intros [] | constructor]].
    intros [H|[]]. discriminate. }
  rewrite (Ddiag_partition 2 M [[1; 0]; [0; 1]] Hnd Hcov).
  cbn [fold_right].
  rewrite <- decpat_two, (Nsig_dec 2 M).
  lia.
Qed.

Lemma binomN_one_val : forall n, binomN n 1 = n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  change (binomN (S n) 1) with (binomN n 0 + binomN n 1)%nat.
  rewrite binomN_0, IH. lia.
Qed.

Lemma binomN_two_val : forall n, (2 * binomN (S n) 2 = S n * n)%nat.
Proof.
  induction n as [|n IH]; [reflexivity|].
  change (binomN (S (S n)) 2) with (binomN (S n) 1 + binomN (S n) 2)%nat.
  rewrite binomN_one_val. nia.
Qed.

Theorem Ddiag_two_closed : forall M,
  (2 * Nsig 2 M [0; 1] = binomN (2 * M) M + 4 ^ M)%nat ->
  (2 * Ddiag 2 M = (M + 3) * binomN (2 * M) M + 4 ^ M)%nat.
Proof.
  intros M H. rewrite (Ddiag_two M).
  assert (Hb : (2 * binomN (M + 2) 2 = (M + 2) * (M + 1))%nat).
  { replace (M + 2)%nat with (S (M + 1))%nat by lia.
    exact (binomN_two_val (M + 1)). }
  assert (Hc : ((M + 1) * card132 M = binomN (2 * M) M)%nat).
  { rewrite <- (card132_binom M). f_equal. lia. }
  transitivity ((2 * binomN (M + 2) 2) * card132 M + 2 * Nsig 2 M [0; 1])%nat.
  - ring.
  - rewrite Hb, H.
    transitivity ((M + 2) * ((M + 1) * card132 M)
                  + (binomN (2 * M) M + 4 ^ M))%nat.
    + ring.
    + rewrite Hc. ring.
Qed.

(* p_2 = (M+3)/2 and q_2 = 1/2 *)
Definition diagonal_two
  (H : forall M, (2 * Nsig 2 M [0; 1] = binomN (2 * M) M + 4 ^ M)%nat)
  : Diagonal 2.
Proof.
  refine (mkDiagonal 2 (Qmake 3 2 :: Qmake 1 2 :: nil) (Qmake 1 2 :: nil)
            eq_refl eq_refl _).
  intro M.
  assert (K := Ddiag_two_closed M (H M)).
  assert (E : Qn (2 * Ddiag 2 M)%nat == Qmult 2 (Qn (Ddiag 2 M))).
  { rewrite Qn_mul, Qn2. reflexivity. }
  assert (E3 : Qn 3 == 3) by (unfold Qn, Qeq; simpl; lia).
  assert (KQ : Qmult 2 (Qn (Ddiag 2 M))
               == Qplus (Qmult (Qplus (Qn M) 3) (Qn (binomN (2 * M) M)))
                        (Qn (4 ^ M))).
  { rewrite <- E, K, Qn_add, Qn_mul, Qn_add, E3. reflexivity. }
  cbn [polyQ dp dq].
  setoid_replace (Qn (Ddiag 2 M))
    with (Qdiv (Qmult 2 (Qn (Ddiag 2 M))) 2) by field.
  rewrite KQ. field.
Defined.

(* The closed form of the increasing fibre and a recurrence for it are the same
   statement, so either may be attacked. *)

Lemma central_step : forall M,
  (binomN (2 * S M) (S M) + 2 * card132 M = 4 * binomN (2 * M) M)%nat.
Proof.
  intro M.
  assert (Hc := binomN_central M).
  assert (Hb := card132_binom M).
  apply (Nat.mul_cancel_l _ _ (S M)); [lia|].
  replace (2 * S M)%nat with (2 * M + 2)%nat by lia.
  transitivity (S M * binomN (2 * M + 2) (S M) + 2 * (S M * card132 M))%nat;
    [ring|].
  rewrite Hc, Hb. ring.
Qed.

Definition NSIG_TWO_CLOSED : Prop :=
  forall M, (2 * Nsig 2 M [0; 1] = binomN (2 * M) M + 4 ^ M)%nat.

Definition NSIG_TWO_REC : Prop :=
  forall M, (Nsig 2 (S M) [0; 1] + card132 M = 4 * Nsig 2 M [0; 1])%nat.

Lemma Nsig_two_zero : Nsig 2 0 [0; 1] = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem nsig_two_closed_of_rec : NSIG_TWO_REC -> NSIG_TWO_CLOSED.
Proof.
  intros HR M. induction M as [|M IH].
  - assert (E1 : binomN (2 * 0) 0 = 1%nat) by reflexivity.
    assert (E2 : (4 ^ 0)%nat = 1%nat) by reflexivity.
    assert (E3 := Nsig_two_zero). lia.
  - assert (HS := HR M). assert (HC := central_step M).
    assert (H4 : (4 ^ S M = 4 * 4 ^ M)%nat) by reflexivity.
    lia.
Qed.

Theorem nsig_two_rec_of_closed : NSIG_TWO_CLOSED -> NSIG_TWO_REC.
Proof.
  intros H M.
  assert (HM := H M). assert (HS := H (S M)). assert (HC := central_step M).
  assert (H4 : (4 ^ S M = 4 * 4 ^ M)%nat) by reflexivity.
  lia.
Qed.

Definition diagonal_two_rec (H : NSIG_TWO_REC) : Diagonal 2 :=
  diagonal_two (nsig_two_closed_of_rec H).

(* ------------------------------------------------------------------ *)
(* The diagonal against its decreasing fibre.  Every occurring suffix pattern
   is a 1324-avoider of length d, and no fibre beats the decreasing one, so
   the diagonal sits between one and card d copies of it. *)

Lemma fold_Nsig_le : forall d M B (l : list (list nat)),
  (forall sg, In sg l -> Nsig d M sg <= B) ->
  fold_right (fun sg acc => Nsig d M sg + acc) 0 l <= length l * B.
Proof.
  intros d M B l. induction l as [|a l IH]; intro H;
    cbn [fold_right length]; [lia|].
  assert (Ha := H a (or_introl eq_refl)).
  assert (Hl := IH (fun sg Hs => H sg (or_intror Hs))). lia.
Qed.

Lemma suffix_pat_in_gen : forall d M w,
  In w (filter (fun w => avoids132b (firstn M w)) (gen (M + d))) ->
  In (suffix_pat d w) (gen d).
Proof.
  intros d M w Hw. apply filter_In in Hw. destruct Hw as [Hg _].
  assert (Hg' := Hg). apply gen_spec in Hg'.
  destruct Hg' as [[Hlen [Hnd Hb]] Hav].
  rewrite (suffix_pat_skipn d M w Hlen).
  assert (Hsk : length (skipn M w) = d)
    by (rewrite length_skipn, Hlen; lia).
  apply gen_spec. split.
  - assert (K := std_is_perm (skipn M w) (NoDup_skipn w M Hnd)).
    rewrite Hsk in K. exact K.
  - intro C.
    apply (proj1 (std_1324 (M + d) (skipn M w) (NoDup_skipn w M Hnd)
                    (fun y Hy => Hb y (in_skipn_w w M y Hy)))) in C.
    apply Hav. apply (subseq_1324 (skipn M w) w);
      [apply skipn_subseq | exact C].
Qed.

Theorem Ddiag_le_dec : forall d M,
  Ddiag d M <= card d * Nsig d M (decpat d).
Proof.
  intros d M.
  rewrite (Ddiag_partition d M (gen d) (gen_nodup d)
             (fun w Hw => suffix_pat_in_gen d M w Hw)).
  unfold card. apply fold_Nsig_le. intros sg _. apply Nsig_le_dec.
Qed.

Corollary Ddiag_sandwich : forall d M,
  binomN (M + d) d * card132 M <= Ddiag d M
  /\ Ddiag d M <= card d * (binomN (M + d) d * card132 M).
Proof.
  intros d M. split.
  - apply Ddiag_ge_free.
  - rewrite <- (Nsig_dec d M). apply Ddiag_le_dec.
Qed.

(* ------------------------------------------------------------------ *)
(* The decreasing suffix fibre's two-term law.  Nsig_dec gives
   N_dec(M) = C(M+d,d) card132 M and card132_binom gives
   (M+1) card132 M = C(2M,M), so (M+1) N_dec(M) = C(M+d,d) C(2M,M) and the
   fibre obeys the law with q identically zero and
   p_dec(M) = (M+2)...(M+d)/d!, of degree d-1 and leading coefficient 1/d!. *)

Lemma Qcancel_l : forall z x y,
  ~ Qeq z 0 -> Qeq (Qmult z x) (Qmult z y) -> Qeq x y.
Proof.
  intros z x y Hz H.
  transitivity (Qmult (Qinv z) (Qmult z x)); [field; exact Hz|].
  rewrite H. field. exact Hz.
Qed.

Lemma Qn_le : forall a b, (a <= b)%nat -> Qle (Qn a) (Qn b).
Proof. intros a b H. unfold Qn, Qle. simpl. lia. Qed.

Lemma nth_padd : forall a b m,
  nth m (padd a b) 0%Q == Qplus (nth m a 0%Q) (nth m b 0%Q).
Proof.
  induction a as [|u a IH]; intros b m.
  - change (padd (@nil Q) b) with b. rewrite (nth_nil m). ring.
  - destruct b as [|v b].
    + change (padd (u :: a) (@nil Q)) with (u :: a).
      rewrite (nth_nil m). ring.
    + destruct m as [|m]; [reflexivity|].
      change (nth (S m) (padd (u :: a) (v :: b)) 0%Q)
        with (nth m (padd a b) 0%Q).
      change (nth (S m) (u :: a) 0%Q) with (nth m a 0%Q).
      change (nth (S m) (v :: b) 0%Q) with (nth m b 0%Q). apply IH.
Qed.

(* (d+1) C(n+1,d+1) = (n+1) C(n,d), from the step and pivot identities *)
Lemma binomN_absorb : forall n d, (d <= n)%nat ->
  (S d * binomN (S n) (S d) = S n * binomN n d)%nat.
Proof.
  intros n d Hd. apply Nat2Z.inj.
  rewrite !Nat2Z.inj_mul, !binomN_binomZ.
  assert (H1 := binomZ_step (S n) d ltac:(lia)).
  assert (H2 := binomZ_pivot n d ltac:(lia)).
  lia.
Qed.

(* multiplication of a coefficient list by the linear factor x + a *)
Definition plin (a : Q) (c : list Q) : list Q := padd (pscale a c) (0%Q :: c).

Lemma plin_spec : forall a c x,
  polyQ (plin a c) x == Qmult (Qplus x a) (polyQ c x).
Proof.
  intros a c x. unfold plin. rewrite padd_spec, pscale_spec.
  cbn [polyQ]. ring.
Qed.

Lemma plin_len : forall a c, length (plin a c) = S (length c).
Proof.
  intros a c. unfold plin. rewrite padd_len, pscale_len. cbn [length]. lia.
Qed.

Fixpoint pdec (d : nat) : list Q :=
  match d with
  | O => nil
  | S O => 1%Q :: nil
  | S d' => pscale (Qinv (Qn (S d'))) (plin (Qn (S d')) (pdec d'))
  end.

Lemma pdec_1 : pdec 1 = 1%Q :: nil.
Proof. reflexivity. Qed.

Lemma pdec_S : forall d, (1 <= d)%nat ->
  pdec (S d) = pscale (Qinv (Qn (S d))) (plin (Qn (S d)) (pdec d)).
Proof. intros d Hd. destruct d as [|d]; [lia | reflexivity]. Qed.

Lemma pdec_len : forall d, (1 <= d)%nat -> length (pdec d) = d.
Proof.
  induction d as [|d IH]; intro Hd; [lia|].
  destruct d as [|d]; [reflexivity|].
  rewrite (pdec_S (S d) ltac:(lia)), pscale_len, plin_len, (IH ltac:(lia)).
  reflexivity.
Qed.

Theorem pdec_binom : forall d M, (1 <= d)%nat ->
  Qmult (Qn (S M)) (polyQ (pdec d) (Qn M)) == Qn (binomN (M + d) d).
Proof.
  intro d. induction d as [|d IH]; intros M Hd; [lia|].
  destruct d as [|d].
  - change (pdec 1) with (1%Q :: nil). cbn [polyQ].
    replace (M + 1)%nat with (S M) by lia. rewrite binomN_one_val. ring.
  - rewrite (pdec_S (S d) ltac:(lia)), pscale_spec, plin_spec.
    assert (IHd := IH M ltac:(lia)).
    assert (Habs : (S (S d) * binomN (S (M + S d)) (S (S d))
                    = S (M + S d) * binomN (M + S d) (S d))%nat)
      by (apply binomN_absorb; lia).
    assert (HQ : Qmult (Qn (S (S d))) (Qn (binomN (S (M + S d)) (S (S d))))
                 == Qmult (Qn (S (M + S d))) (Qn (binomN (M + S d) (S d)))).
    { rewrite <- !Qn_mul, Habs. reflexivity. }
    assert (Hsum : Qplus (Qn M) (Qn (S (S d))) == Qn (S (M + S d))).
    { rewrite <- (Qn_add M (S (S d))).
      replace (M + S (S d))%nat with (S (M + S d))%nat by lia. reflexivity. }
    replace (M + S (S d))%nat with (S (M + S d))%nat by lia.
    rewrite Hsum.
    assert (Hz : ~ Qn (S (S d)) == 0) by apply Qn_nonzero.
    transitivity (Qmult (Qinv (Qn (S (S d))))
                    (Qmult (Qn (S (M + S d)))
                           (Qmult (Qn (S M)) (polyQ (pdec (S d)) (Qn M))))).
    { ring. }
    rewrite IHd, <- HQ. field. exact Hz.
Qed.

Theorem pdec_lead : forall d, (1 <= d)%nat ->
  nth (pred d) (pdec d) 0%Q == Qinv (Qn (factn d)).
Proof.
  induction d as [|d IH]; intro Hd; [lia|].
  destruct d as [|d].
  - change (pred 1)%nat with 0%nat. change (pdec 1) with (1%Q :: nil).
    cbn [nth]. replace (factn 1) with 1%nat by reflexivity.
    rewrite Qn_1. reflexivity.
  - assert (Hlen : length (pdec (S d)) = S d) by (apply pdec_len; lia).
    rewrite (pdec_S (S d) ltac:(lia)). cbn [pred].
    rewrite nth_pscale. unfold plin. rewrite nth_padd, nth_pscale.
    assert (Hov : nth (S d) (pdec (S d)) 0%Q = 0%Q)
      by (apply nth_overflow; rewrite Hlen; lia).
    rewrite Hov.
    change (nth (S d) (0%Q :: pdec (S d)) 0%Q) with (nth d (pdec (S d)) 0%Q).
    assert (Hl := IH ltac:(lia)). cbn [pred] in Hl. rewrite Hl.
    change (factn (S (S d))) with (S (S d) * factn (S d))%nat.
    rewrite Qn_mul. field.
    split; [apply Qn_pos_nonzero; apply factn_pos | apply Qn_nonzero].
Qed.

Theorem Nsig_dec_two_term : forall d M, (1 <= d)%nat ->
  Qn (Nsig d M (decpat d))
  == Qmult (polyQ (pdec d) (Qn M)) (Qn (binomN (2 * M) M)).
Proof.
  intros d M Hd.
  apply (Qcancel_l (Qn (S M))); [apply Qn_nonzero|].
  assert (Hnat : (S M * Nsig d M (decpat d)
                  = binomN (M + d) d * binomN (2 * M) M)%nat).
  { rewrite (Nsig_dec d M), <- (card132_binom M). ring. }
  assert (H3 := pdec_binom d M Hd).
  transitivity (Qn (S M * Nsig d M (decpat d))%nat).
  { rewrite Qn_mul. reflexivity. }
  rewrite Hnat, Qn_mul, <- H3. ring.
Qed.

Lemma pdec_one_diagonal : pdec 1 = dp 1 diagonal_one.
Proof. reflexivity. Qed.

(* The sandwich, read on the two polynomials. *)
Theorem diagonal_ge_dec : forall d (Dg : Diagonal d), (1 <= d)%nat -> forall M,
  Qle (Qmult (polyQ (pdec d) (Qn M)) (Qn (binomN (2 * M) M)))
      (Qplus (Qmult (polyQ (dp d Dg) (Qn M)) (Qn (binomN (2 * M) M)))
             (Qmult (polyQ (dq d Dg) (Qn M)) (Qn (4 ^ M)))).
Proof.
  intros d Dg Hd M.
  rewrite <- (d_law d Dg M), <- (Nsig_dec_two_term d M Hd).
  apply Qn_le. rewrite (Nsig_dec d M). apply Ddiag_ge_free.
Qed.

Theorem diagonal_le_dec : forall d (Dg : Diagonal d), (1 <= d)%nat -> forall M,
  Qle (Qplus (Qmult (polyQ (dp d Dg) (Qn M)) (Qn (binomN (2 * M) M)))
             (Qmult (polyQ (dq d Dg) (Qn M)) (Qn (4 ^ M))))
      (Qmult (Qn (card d))
             (Qmult (polyQ (pdec d) (Qn M)) (Qn (binomN (2 * M) M)))).
Proof.
  intros d Dg Hd M.
  rewrite <- (d_law d Dg M), <- (Nsig_dec_two_term d M Hd), <- Qn_mul.
  apply Qn_le. apply Ddiag_le_dec.
Qed.

(* ------------------------------------------------------------------ *)
(* The two-term law is a fibrewise statement.  Ddiag_partition sums Nsig over
   the suffix patterns that occur, so a law at every fibre adds coefficientwise
   to a law at the diagonal.  The decreasing fibre already has one. *)

Lemma nth_repeat0 : forall k j, nth j (repeat 0%Q k) 0%Q = 0%Q.
Proof.
  induction k as [|k IH]; intro j; cbn [repeat].
  - destruct j; reflexivity.
  - destruct j as [|j]; [reflexivity | cbn [nth]; apply IH].
Qed.

Lemma polyQ_app_zeros : forall c k x, polyQ (c ++ repeat 0%Q k) x == polyQ c x.
Proof.
  induction c as [|u c IH]; intros k x; cbn [app polyQ].
  - apply polyQ_zero_list. intro j. rewrite nth_repeat0. reflexivity.
  - rewrite IH. reflexivity.
Qed.

Definition ppad (n : nat) (c : list Q) : list Q := c ++ repeat 0%Q (n - length c).

Lemma ppad_len : forall n c, (length c <= n)%nat -> length (ppad n c) = n.
Proof.
  intros n c H. unfold ppad. rewrite len_app_gen, repeat_length. lia.
Qed.

Lemma ppad_spec : forall n c x, polyQ (ppad n c) x == polyQ c x.
Proof. intros n c x. unfold ppad. apply polyQ_app_zeros. Qed.

Fixpoint psum (L : list (list Q)) : list Q :=
  match L with nil => nil | c :: r => padd c (psum r) end.

Lemma psum_len_le : forall n L,
  (forall c, In c L -> (length c <= n)%nat) -> (length (psum L) <= n)%nat.
Proof.
  intros n L. induction L as [|c L IH]; intro H; cbn [psum length]; [lia|].
  rewrite padd_len.
  assert (Hc := H c (or_introl eq_refl)).
  assert (Hl := IH (fun z Hz => H z (or_intror Hz))). lia.
Qed.

Lemma psum_map_spec : forall (A : Type) (f : A -> list Q) (L : list A) x,
  polyQ (psum (map f L)) x
  == fold_right (fun a acc => Qplus (polyQ (f a) x) acc) 0%Q L.
Proof.
  intros A f. induction L as [|a L IH]; intro x; cbn [map psum fold_right].
  - reflexivity.
  - rewrite padd_spec, IH. reflexivity.
Qed.

Lemma Qn_fold_nat : forall (A : Type) (f : A -> nat) (L : list A),
  Qn (fold_right (fun a acc => (f a + acc)%nat) 0%nat L)
  == fold_right (fun a acc => Qplus (Qn (f a)) acc) 0%Q L.
Proof.
  intros A f. induction L as [|a L IH]; cbn [fold_right].
  - apply Qn_0.
  - rewrite Qn_add, IH. reflexivity.
Qed.

Lemma fold_law_split : forall (L : list (list nat))
    (w u v : list nat -> Q) (C F : Q),
  (forall sg, In sg L ->
     Qeq (w sg) (Qplus (Qmult (u sg) C) (Qmult (v sg) F))) ->
  fold_right (fun sg acc => Qplus (w sg) acc) 0%Q L
  == Qplus (Qmult (fold_right (fun sg acc => Qplus (u sg) acc) 0%Q L) C)
           (Qmult (fold_right (fun sg acc => Qplus (v sg) acc) 0%Q L) F).
Proof.
  intros L w u v C F. induction L as [|a L IH]; intro H; cbn [fold_right].
  - ring.
  - rewrite (H a (or_introl eq_refl)),
            (IH (fun sg Hs => H sg (or_intror Hs))). ring.
Qed.

Definition dpfib (d : nat) (P : list nat -> list Q) : list Q :=
  ppad d (psum (map P (gen d))).

Definition dqfib (d : nat) (Qc : list nat -> list Q) : list Q :=
  ppad (pred d) (psum (map Qc (gen d))).

Lemma dpfib_len : forall d (P : list nat -> list Q),
  (forall sg, In sg (gen d) -> length (P sg) = d) -> length (dpfib d P) = d.
Proof.
  intros d P HlP. unfold dpfib.
  apply ppad_len. apply (psum_len_le d). intros c Hc.
  apply in_map_iff in Hc. destruct Hc as [sg [Hsg Hin]]. subst c.
  rewrite (HlP sg Hin). lia.
Qed.

Lemma dqfib_len : forall d (Qc : list nat -> list Q),
  (forall sg, In sg (gen d) -> length (Qc sg) = pred d) ->
  length (dqfib d Qc) = pred d.
Proof.
  intros d Qc HlQ. unfold dqfib.
  apply ppad_len. apply (psum_len_le (pred d)). intros c Hc.
  apply in_map_iff in Hc. destruct Hc as [sg [Hsg Hin]]. subst c.
  rewrite (HlQ sg Hin). lia.
Qed.

Lemma dfib_law : forall d (P Qc : list nat -> list Q),
  (forall sg M, In sg (gen d) ->
     Qn (Nsig d M sg)
     == Qplus (Qmult (polyQ (P sg) (Qn M)) (Qn (binomN (2 * M) M)))
              (Qmult (polyQ (Qc sg) (Qn M)) (Qn (4 ^ M)))) ->
  forall M, Qn (Ddiag d M)
    == Qplus (Qmult (polyQ (dpfib d P) (Qn M)) (Qn (binomN (2 * M) M)))
             (Qmult (polyQ (dqfib d Qc) (Qn M)) (Qn (4 ^ M))).
Proof.
  intros d P Qc Hlaw M. unfold dpfib, dqfib.
  rewrite !ppad_spec, !psum_map_spec.
  rewrite (Ddiag_partition d M (gen d) (gen_nodup d)
             (fun w Hw => suffix_pat_in_gen d M w Hw)).
  rewrite (Qn_fold_nat (list nat) (fun sg => Nsig d M sg) (gen d)).
  apply (fold_law_split (gen d)
           (fun sg => Qn (Nsig d M sg))
           (fun sg => polyQ (P sg) (Qn M))
           (fun sg => polyQ (Qc sg) (Qn M))
           (Qn (binomN (2 * M) M)) (Qn (4 ^ M))).
  intros sg Hsg. apply Hlaw. exact Hsg.
Qed.

Definition two_term_law_of_fibres (d : nat) (P Qc : list nat -> list Q)
  (H1 : forall sg, In sg (gen d) -> length (P sg) = d)
  (H2 : forall sg, In sg (gen d) -> length (Qc sg) = pred d)
  (H3 : forall sg M, In sg (gen d) ->
     Qn (Nsig d M sg)
     == Qplus (Qmult (polyQ (P sg) (Qn M)) (Qn (binomN (2 * M) M)))
              (Qmult (polyQ (Qc sg) (Qn M)) (Qn (4 ^ M))))
  : Diagonal d :=
  mkDiagonal d (dpfib d P) (dqfib d Qc)
             (dpfib_len d P H1) (dqfib_len d Qc H2) (dfib_law d P Qc H3).

Definition sqzero (d : nat) : list Q := repeat 0%Q (pred d).

Lemma sqzero_len : forall d, length (sqzero d) = pred d.
Proof. intro d. unfold sqzero. apply repeat_length. Qed.

Lemma sqzero_spec : forall d x, polyQ (sqzero d) x == 0.
Proof.
  intros d x. unfold sqzero. apply polyQ_zero_list.
  intro j. rewrite nth_repeat0. reflexivity.
Qed.

Theorem fibre_law_dec : forall d M, (1 <= d)%nat ->
  Qn (Nsig d M (decpat d))
  == Qplus (Qmult (polyQ (pdec d) (Qn M)) (Qn (binomN (2 * M) M)))
           (Qmult (polyQ (sqzero d) (Qn M)) (Qn (4 ^ M))).
Proof.
  intros d M Hd. rewrite (sqzero_spec d (Qn M)), (Nsig_dec_two_term d M Hd).
  ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Two consequences of the fibre decomposition: the leading coefficient of the
   diagonal is the decreasing fibre's as soon as no other fibre reaches degree
   d-1, and p(0) - q(0) = 1 as soon as every other fibre splits its unit
   evenly.  Those are the level-1 claim and R_at_minus_one, fibre by fibre. *)

Lemma binomN_zero_above : forall n k, (n < k)%nat -> binomN n k = 0%nat.
Proof.
  induction n as [|n IH]; intros k H.
  - destruct k; [lia | reflexivity].
  - destruct k as [|k]; [lia|].
    change (binomN (S n) (S k)) with (binomN n k + binomN n (S k))%nat.
    rewrite (IH k ltac:(lia)), (IH (S k) ltac:(lia)). reflexivity.
Qed.

Lemma binomN_diag : forall n, binomN n n = 1%nat.
Proof.
  induction n as [|n IH]; [reflexivity|].
  change (binomN (S n) (S n)) with (binomN n n + binomN n (S n))%nat.
  rewrite IH, (binomN_zero_above n (S n) ltac:(lia)). reflexivity.
Qed.

Lemma pdec_at_zero : forall d, (1 <= d)%nat -> polyQ (pdec d) 0 == 1.
Proof.
  intros d Hd.
  assert (H := pdec_binom d 0 Hd).
  assert (E0 : Qn 0 == 0) by apply Qn_0.
  rewrite (polyQ_ext (pdec d) (Qn 0) 0 E0) in H.
  rewrite Nat.add_0_l, binomN_diag in H.
  transitivity (Qmult (Qn (S 0)) (polyQ (pdec d) 0)).
  - rewrite Qn_1. ring.
  - rewrite H. apply Qn_1.
Qed.

Lemma nth_ppad : forall n c j, nth j (ppad n c) 0%Q == nth j c 0%Q.
Proof.
  intros n c j. unfold ppad.
  destruct (Nat.lt_ge_cases j (length c)) as [H|H].
  - rewrite app_nth1 by exact H. reflexivity.
  - rewrite app_nth2 by exact H.
    rewrite (nth_overflow c 0%Q H), nth_repeat0. reflexivity.
Qed.

Lemma nth_psum_map : forall (A : Type) (f : A -> list Q) (L : list A) j,
  nth j (psum (map f L)) 0%Q
  == fold_right (fun a acc => Qplus (nth j (f a) 0%Q) acc) 0%Q L.
Proof.
  intros A f. induction L as [|a L IH]; intro j; cbn [map psum fold_right].
  - rewrite (nth_nil j). reflexivity.
  - rewrite nth_padd, IH. reflexivity.
Qed.

Lemma foldQ_zero : forall (A : Type) (g : A -> Q) (L : list A),
  (forall a, In a L -> g a == 0) ->
  fold_right (fun a acc => Qplus (g a) acc) 0%Q L == 0.
Proof.
  intros A g. induction L as [|a L IH]; intro H; cbn [fold_right]; [reflexivity|].
  rewrite (H a (or_introl eq_refl)), (IH (fun z Hz => H z (or_intror Hz))).
  ring.
Qed.

Lemma foldQ_pick : forall (A : Type) (eqA : forall x y : A, {x = y} + {x <> y})
    (g : A -> Q) (a : A) (L : list A),
  NoDup L -> In a L -> (forall z, In z L -> z <> a -> g z == 0) ->
  fold_right (fun z acc => Qplus (g z) acc) 0%Q L == g a.
Proof.
  intros A eqA g a. induction L as [|b L IH]; intros Hnd Hin Hz;
    [contradiction|].
  inversion Hnd as [|x r Hnb Hnd' Heq]; subst.
  cbn [fold_right].
  destruct (eqA b a) as [E|E].
  - subst b. rewrite (foldQ_zero A g L).
    + ring.
    + intros z HzL. apply Hz; [right; exact HzL|].
      intro C. subst z. contradiction.
  - rewrite (Hz b (or_introl eq_refl) E).
    rewrite (IH Hnd'
               ltac:(destruct Hin as [Hc|Hc];
                     [exfalso; apply E; exact Hc | exact Hc])
               (fun z HzL => Hz z (or_intror HzL))).
    ring.
Qed.

Lemma foldQ_sub : forall (A : Type) (u v : A -> Q) (L : list A),
  Qminus (fold_right (fun a acc => Qplus (u a) acc) 0%Q L)
         (fold_right (fun a acc => Qplus (v a) acc) 0%Q L)
  == fold_right (fun a acc => Qplus (Qminus (u a) (v a)) acc) 0%Q L.
Proof.
  intros A u v. induction L as [|a L IH]; cbn [fold_right]; [ring|].
  rewrite <- IH. ring.
Qed.

Lemma decpat_in_gen : forall d, In (decpat d) (gen d).
Proof.
  intro d. apply gen_spec. split.
  - apply decpat_is_perm.
  - apply empty_tail_avoids. apply decpat_avoids_132.
Qed.

Theorem fibres_p_lead : forall d (P : list nat -> list Q), (1 <= d)%nat ->
  P (decpat d) = pdec d ->
  (forall sg, In sg (gen d) -> sg <> decpat d ->
     nth (pred d) (P sg) 0%Q == 0) ->
  Qmult (Qn (factn d)) (nth (pred d) (dpfib d P) 0%Q) == 1.
Proof.
  intros d P Hd Hdec Hlev. unfold dpfib.
  rewrite nth_ppad, nth_psum_map.
  rewrite (foldQ_pick (list nat) (list_eq_dec Nat.eq_dec)
             (fun sg => nth (pred d) (P sg) 0%Q) (decpat d) (gen d)
             (gen_nodup d) (decpat_in_gen d) Hlev).
  rewrite Hdec, (pdec_lead d Hd). field.
  apply Qn_pos_nonzero. apply factn_pos.
Qed.

Theorem fibres_at_minus_one : forall d (P Qc : list nat -> list Q),
  (1 <= d)%nat ->
  P (decpat d) = pdec d -> Qc (decpat d) = sqzero d ->
  (forall sg, In sg (gen d) -> sg <> decpat d ->
     polyQ (P sg) 0 == polyQ (Qc sg) 0) ->
  Qeq (Qminus (polyQ (dpfib d P) 0) (polyQ (dqfib d Qc) 0)) 1.
Proof.
  intros d P Qc Hd HdecP HdecQ Hsplit. unfold dpfib, dqfib.
  rewrite !ppad_spec, !psum_map_spec, foldQ_sub.
  rewrite (foldQ_pick (list nat) (list_eq_dec Nat.eq_dec)
             (fun sg => Qminus (polyQ (P sg) 0) (polyQ (Qc sg) 0))
             (decpat d) (gen d) (gen_nodup d) (decpat_in_gen d)).
  - rewrite HdecP, HdecQ, (sqzero_spec d 0), (pdec_at_zero d Hd). ring.
  - intros z Hz Hne. rewrite (Hsplit z Hz Hne). ring.
Qed.

Lemma dp_of_fibres : forall d P Qc H1 H2 H3,
  dp d (two_term_law_of_fibres d P Qc H1 H2 H3) = dpfib d P.
Proof. reflexivity. Qed.

Lemma dq_of_fibres : forall d P Qc H1 H2 H3,
  dq d (two_term_law_of_fibres d P Qc H1 H2 H3) = dqfib d Qc.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* d = 2 through the fibre decomposition.  Both fibres are named, the
   decreasing one is a theorem and the increasing one is NSIG_TWO_CLOSED, so
   the level-1 claim and R_at_minus_one both come out at that size. *)

Lemma gen_two : gen 2 = [[1; 0]; [0; 1]].
Proof. vm_compute. reflexivity. Qed.

Definition P2 (sg : list nat) : list Q :=
  if list_eq_dec Nat.eq_dec sg [1; 0]
  then pdec 2 else (Qmake 1 2 :: 0%Q :: nil).

Definition Q2 (sg : list nat) : list Q :=
  if list_eq_dec Nat.eq_dec sg [1; 0]
  then sqzero 2 else (Qmake 1 2 :: nil).

Lemma P2_dec : P2 (decpat 2) = pdec 2.
Proof.
  unfold P2. rewrite decpat_two.
  destruct (list_eq_dec Nat.eq_dec [1; 0] [1; 0]); [reflexivity | contradiction].
Qed.

Lemma Q2_dec : Q2 (decpat 2) = sqzero 2.
Proof.
  unfold Q2. rewrite decpat_two.
  destruct (list_eq_dec Nat.eq_dec [1; 0] [1; 0]); [reflexivity | contradiction].
Qed.

Lemma P2_len : forall sg, In sg (gen 2) -> length (P2 sg) = 2.
Proof.
  intros sg _. unfold P2.
  destruct (list_eq_dec Nat.eq_dec sg [1; 0]);
    [apply pdec_len; lia | reflexivity].
Qed.

Lemma Q2_len : forall sg, In sg (gen 2) -> length (Q2 sg) = pred 2.
Proof.
  intros sg _. unfold Q2.
  destruct (list_eq_dec Nat.eq_dec sg [1; 0]);
    [apply sqzero_len | reflexivity].
Qed.

Lemma Qtwo_nonzero : ~ Qeq 2 0.
Proof. unfold Qeq. cbn. discriminate. Qed.

Lemma P2_law : NSIG_TWO_CLOSED ->
  forall sg M, In sg (gen 2) ->
    Qn (Nsig 2 M sg)
    == Qplus (Qmult (polyQ (P2 sg) (Qn M)) (Qn (binomN (2 * M) M)))
             (Qmult (polyQ (Q2 sg) (Qn M)) (Qn (4 ^ M))).
Proof.
  intros H sg M Hsg. rewrite gen_two in Hsg. cbn [In] in Hsg.
  destruct Hsg as [E | [E | []]]; subst sg.
  - rewrite <- decpat_two, P2_dec, Q2_dec.
    apply fibre_law_dec. lia.
  - unfold P2, Q2.
    destruct (list_eq_dec Nat.eq_dec [0; 1] [1; 0]) as [Ec|Ec];
      [discriminate Ec|].
    assert (HM := H M).
    assert (HQ : Qmult 2 (Qn (Nsig 2 M [0; 1]))
                 == Qplus (Qn (binomN (2 * M) M)) (Qn (4 ^ M))).
    { rewrite <- Qn_add, <- HM, Qn_mul, Qn2. reflexivity. }
    apply (Qcancel_l 2); [apply Qtwo_nonzero|].
    rewrite HQ. cbn [polyQ]. ring.
Qed.

Definition diagonal_two_fib (H : NSIG_TWO_CLOSED) : Diagonal 2 :=
  two_term_law_of_fibres 2 P2 Q2 P2_len Q2_len (P2_law H).

Theorem p_lead_two : Qmult (Qn (factn 2)) (nth 1 (dpfib 2 P2) 0%Q) == 1.
Proof.
  apply (fibres_p_lead 2 P2); [lia | apply P2_dec |].
  intros sg _ Hne. unfold P2.
  destruct (list_eq_dec Nat.eq_dec sg [1; 0]) as [Ec|Ec].
  - exfalso. apply Hne. rewrite decpat_two. exact Ec.
  - reflexivity.
Qed.

Theorem R_at_minus_one_two :
  Qeq (Qminus (polyQ (dpfib 2 P2) 0) (polyQ (dqfib 2 Q2) 0)) 1.
Proof.
  apply (fibres_at_minus_one 2 P2 Q2);
    [lia | apply P2_dec | apply Q2_dec |].
  intros sg _ Hne. unfold P2, Q2.
  destruct (list_eq_dec Nat.eq_dec sg [1; 0]) as [Ec|Ec].
  - exfalso. apply Hne. rewrite decpat_two. exact Ec.
  - cbn [polyQ]. ring.
Qed.

Corollary R_at_minus_one_of_two : forall H : NSIG_TWO_CLOSED,
  Qeq (Qminus (polyQ (dp 2 (diagonal_two_fib H)) 0)
              (polyQ (dq 2 (diagonal_two_fib H)) 0)) 1.
Proof. intro H. exact R_at_minus_one_two. Qed.

(* ------------------------------------------------------------------ *)
(* Every coefficient of the diagonal is the sum of the fibre coefficients, so
   both degree claims are statements about that sum. *)

Lemma nth_dpfib : forall d (P : list nat -> list Q) j,
  nth j (dpfib d P) 0%Q
  == fold_right (fun sg acc => Qplus (nth j (P sg) 0%Q) acc) 0%Q (gen d).
Proof.
  intros d P j. unfold dpfib. rewrite nth_ppad, nth_psum_map. reflexivity.
Qed.

Lemma nth_dqfib : forall d (Qc : list nat -> list Q) j,
  nth j (dqfib d Qc) 0%Q
  == fold_right (fun sg acc => Qplus (nth j (Qc sg) 0%Q) acc) 0%Q (gen d).
Proof.
  intros d Qc j. unfold dqfib. rewrite nth_ppad, nth_psum_map. reflexivity.
Qed.

(* the decreasing fibre contributes nothing to q, at any coefficient *)
Lemma sqzero_nth : forall d j, nth j (sqzero d) 0%Q = 0%Q.
Proof. intros d j. unfold sqzero. apply nth_repeat0. Qed.

(* d = 1 through the same machinery, where the decreasing pattern is the only
   fibre and the law is unconditional. *)

Lemma gen_one : gen 1 = [[0]].
Proof. vm_compute. reflexivity. Qed.

Lemma decpat_one : decpat 1 = [0].
Proof. reflexivity. Qed.

Definition P1 (_ : list nat) : list Q := pdec 1.
Definition Q1 (_ : list nat) : list Q := sqzero 1.

Lemma P1_len : forall sg, In sg (gen 1) -> length (P1 sg) = 1.
Proof. intros sg _. unfold P1. apply pdec_len. lia. Qed.

Lemma Q1_len : forall sg, In sg (gen 1) -> length (Q1 sg) = pred 1.
Proof. intros sg _. unfold Q1. apply sqzero_len. Qed.

Lemma P1_law : forall sg M, In sg (gen 1) ->
  Qn (Nsig 1 M sg)
  == Qplus (Qmult (polyQ (P1 sg) (Qn M)) (Qn (binomN (2 * M) M)))
           (Qmult (polyQ (Q1 sg) (Qn M)) (Qn (4 ^ M))).
Proof.
  intros sg M Hsg. rewrite gen_one in Hsg. cbn [In] in Hsg.
  destruct Hsg as [E | []]; subst sg.
  unfold P1, Q1. rewrite <- decpat_one. apply fibre_law_dec. lia.
Qed.

Definition diagonal_one_fib : Diagonal 1 :=
  two_term_law_of_fibres 1 P1 Q1 P1_len Q1_len P1_law.

Lemma dpfib_one : dpfib 1 P1 = dp 1 diagonal_one.
Proof. vm_compute. reflexivity. Qed.

Lemma dqfib_one : dqfib 1 Q1 = dq 1 diagonal_one.
Proof. vm_compute. reflexivity. Qed.

(* q_degree_pattern at j = 0 and d = 2: d! q_{d,d-2} = C(d,2). *)
Definition qlead0 : list Q := 0%Q :: Qopp (Qmake 1 2) :: Qmake 1 2 :: nil.

Lemma qlead0_len : length qlead0 = 3.
Proof. reflexivity. Qed.

Theorem q_lead_two :
  Qmult (Qn (factn 2)) (nth 0 (dqfib 2 Q2) 0%Q) == polyQ qlead0 (Qn 2).
Proof. vm_compute. reflexivity. Qed.

(* p_degree_pattern at j = 0 and d = 2 is p_lead_two, with c = [1]. *)
Theorem p_lead_two_poly :
  Qmult (Qn (factn 2)) (nth 1 (dpfib 2 P2) 0%Q) == polyQ (1%Q :: nil) (Qn 2).
Proof. rewrite p_lead_two. cbn [polyQ]. ring. Qed.

(* ------------------------------------------------------------------ *)
(* The top backward difference, and with it [s^0] R_d.  Delta^n of a
   polynomial of degree at most n is the constant n! times its leading
   coefficient, so the lowest coefficient of R_d is fixed by lead p_d alone. *)

Theorem delta_top : forall n c x, (length c <= S n)%nat ->
  delta n c x == Qmult (Qn (factn n)) (nth n c 0%Q).
Proof.
  intros n c x Hc.
  remember (Qmult (nth n c 0%Q) (Qn (factn n))) as lam eqn:Hlam.
  remember (psub c (pscale lam (binlist n))) as d eqn:Hd.
  remember (firstn n d) as c' eqn:Hc'.
  assert (Hdx : forall y, polyQ d y == Qminus (polyQ c y) (Qmult lam (binQ y n))).
  { intro y. rewrite Hd, psub_spec, pscale_spec, binlist_spec. reflexivity. }
  assert (Htop : forall j, (n <= j)%nat -> nth j d 0%Q == 0).
  { intros j Hj. rewrite Hd, nth_psub, nth_pscale.
    destruct (Nat.eq_dec j n) as [E|E].
    - subst j. rewrite binlist_lead, Hlam. field.
      apply Qn_pos_nonzero, factn_pos.
    - assert (H1 : nth j c 0%Q = 0%Q) by (apply nth_overflow; lia).
      assert (H2 : nth j (binlist n) 0%Q = 0%Q)
        by (apply nth_overflow; rewrite binlist_len; lia).
      rewrite H1, H2. ring. }
  assert (Hc'x : forall y, polyQ c' y == polyQ d y)
    by (intro y; rewrite Hc'; apply polyQ_firstn; exact Htop).
  assert (Hc'len : (length c' <= n)%nat)
    by (rewrite Hc'; rewrite length_firstn; lia).
  assert (Hsplit : forall y, polyQ c y
                   == polyQ (padd c' (pscale lam (binlist n))) y).
  { intro y. rewrite padd_spec, pscale_spec, binlist_spec, (Hc'x y), (Hdx y).
    ring. }
  rewrite (delta_congr n c (padd c' (pscale lam (binlist n))) x Hsplit).
  rewrite delta_padd, delta_pscale.
  assert (Hzero : delta n c' x == 0).
  { destruct n as [|m].
    - assert (Ec : c' = nil) by (rewrite Hc'; reflexivity).
      rewrite Ec. cbn [delta polyQ]. reflexivity.
    - apply (delta_vanishes m c' x). exact Hc'len. }
  assert (Hbl : delta n (binlist n) x == 1).
  { rewrite (delta_binlist n n x (Nat.le_refl n)), Nat.sub_diag.
    cbn [binQ]. reflexivity. }
  rewrite Hzero, Hbl, Hlam. ring.
Qed.

Theorem rcoef_zero : forall d (Dg : Diagonal d), (1 <= d)%nat ->
  rcoef d Dg 0
  == Qmult (wQ (pred d))
           (Qmult (Qn (factn (pred d))) (nth (pred d) (dp d Dg) 0%Q)).
Proof.
  intros d Dg Hd.
  assert (H := rcoef_even d Dg (d - 1) Hd (Nat.le_refl (d - 1))).
  replace (2 * d - 2 - 2 * (d - 1))%nat with 0%nat in H by lia.
  replace (d - 1)%nat with (pred d) in H by lia.
  rewrite H, (delta_top (pred d) (dp d Dg) (Qopp (Qmake 1 2))).
  - reflexivity.
  - rewrite (dp_len d Dg). lia.
Qed.

Theorem rcoef_zero_catalan : forall d (Dg : Diagonal d), (1 <= d)%nat ->
  Qmult (Qn (factn d)) (nth (pred d) (dp d Dg) 0%Q) == 1 ->
  rcoef d Dg 0 == Qdiv (Qn (card132 (pred d))) (Qn (4 ^ pred d)).
Proof.
  intros d Dg Hd Hlead.
  assert (Hdp : d = S (pred d)) by lia.
  assert (Hfd : Qn (factn d) == Qmult (Qn d) (Qn (factn (pred d)))).
  { rewrite Hdp at 1. change (factn (S (pred d)))
      with (S (pred d) * factn (pred d))%nat.
    rewrite Qn_mul, <- Hdp. reflexivity. }
  assert (Hdnz : ~ Qn d == 0)
    by (destruct d as [|d']; [lia | apply Qn_nonzero]).
  assert (Hfnz : ~ Qn (factn (pred d)) == 0)
    by (apply Qn_pos_nonzero, factn_pos).
  assert (Hpnz : ~ Qn (4 ^ pred d) == 0)
    by (apply Qn_pos_nonzero, four_pow_pos).
  assert (Hcat : Qn (binomN (2 * pred d) (pred d))
                 == Qmult (Qn d) (Qn (card132 (pred d)))).
  { rewrite <- Qn_mul, <- (card132_binom (pred d)), <- Hdp. reflexivity. }
  assert (Hkey : Qmult (Qn (factn (pred d))) (nth (pred d) (dp d Dg) 0%Q)
                 == Qdiv 1 (Qn d)).
  { apply (Qcancel_l (Qn d)); [exact Hdnz|].
    transitivity (Qmult (Qn (factn d)) (nth (pred d) (dp d Dg) 0%Q)).
    - rewrite Hfd. ring.
    - rewrite Hlead. field. exact Hdnz. }
  rewrite (rcoef_zero d Dg Hd), Hkey, (wQ_div (pred d)), Hcat.
  field. split; assumption.
Qed.

(* C(n,k) <= 2^n, hence C(2i,i) <= 4^i and Cat(i) <= 4^i. *)
Lemma pow2_pos : forall n, (1 <= 2 ^ n)%nat.
Proof. induction n as [|n IH]; cbn [Nat.pow]; lia. Qed.

Lemma binomN_le_pow2 : forall n k, (binomN n k <= 2 ^ n)%nat.
Proof.
  induction n as [|n IH]; intro k.
  - destruct k; cbn [binomN Nat.pow]; lia.
  - destruct k as [|k].
    + rewrite binomN_0. cbn [Nat.pow]. assert (H := pow2_pos n). lia.
    + change (binomN (S n) (S k)) with (binomN n k + binomN n (S k))%nat.
      assert (H1 := IH k). assert (H2 := IH (S k)). cbn [Nat.pow]. lia.
Qed.

Lemma pow2_pow4 : forall i, (2 ^ (2 * i) = 4 ^ i)%nat.
Proof.
  induction i as [|i IH]; [reflexivity|].
  replace (2 * S i)%nat with (S (S (2 * i))) by lia.
  cbn [Nat.pow]. rewrite IH. cbn [Nat.pow]. lia.
Qed.

Lemma binomN_le_pow4 : forall i, (binomN (2 * i) i <= 4 ^ i)%nat.
Proof. intro i. rewrite <- pow2_pow4. apply binomN_le_pow2. Qed.

Lemma card132_le_pow4 : forall m, (card132 m <= 4 ^ m)%nat.
Proof.
  intro m.
  assert (Hb := card132_binom m).
  assert (Hp := binomN_le_pow4 m).
  assert (H : (card132 m <= S m * card132 m)%nat) by nia.
  lia.
Qed.

Lemma Qn_pos : forall b, (1 <= b)%nat -> Qlt 0 (Qn b).
Proof. intros b Hb. unfold Qn, Qlt. cbn. lia. Qed.

(* the exponent law at t = 0, from the leading coefficient alone *)
Theorem exponent_law_at_zero : forall d (Dg : Diagonal d), (1 <= d)%nat ->
  Qmult (Qn (factn d)) (nth (pred d) (dp d Dg) 0%Q) == 1 ->
  Qle (Qabs (rcoef d Dg 0)) (Qmult 1 (Qn (d ^ 0))).
Proof.
  intros d Dg Hd Hlead.
  rewrite (rcoef_zero_catalan d Dg Hd Hlead).
  assert (Hpos : Qlt 0 (Qn (4 ^ pred d)))
    by (apply Qn_pos; apply four_pow_pos).
  assert (Hnn : Qle 0 (Qdiv (Qn (card132 (pred d))) (Qn (4 ^ pred d)))).
  { apply Qle_shift_div_l; [exact Hpos|].
    rewrite Qmult_0_l. apply (Qn_le 0). lia. }
  rewrite (Qabs_pos _ Hnn).
  replace (d ^ 0)%nat with 1%nat by reflexivity.
  rewrite Qn_1, Qmult_1_l.
  apply Qle_shift_div_r; [exact Hpos|].
  rewrite Qmult_1_l. apply Qn_le. apply card132_le_pow4.
Qed.

(* ------------------------------------------------------------------ *)
(* d_A is decreasing under inclusion of the ascent set of the shared cell.
   By domino_criterion a 1324 in a domino is an ascent of the lower cell
   interleaved with an ascent of the upper one, so replacing the lower cell by
   one with fewer ascents, keeping the mask and the upper cell, lands back in
   the class; the mask and upper cell are recovered from the image, so the map
   is injective on each fibre.  dA_le_dec is the case of the decreasing cell,
   which has no ascent at all. *)

Lemma locell_132_pos : forall b w i j k,
  ~ contains_132 (locell b w) ->
  (i < j)%nat -> (j < k)%nat -> (k < length w)%nat ->
  (nth i w 0%nat < b)%nat -> (nth j w 0%nat < b)%nat -> (nth k w 0%nat < b)%nat ->
  ~ ((nth i w 0%nat < nth k w 0%nat)%nat /\ (nth k w 0%nat < nth j w 0%nat)%nat).
Proof.
  intros b w i j k Hno Hij Hjk Hk Bi Bj Bk [H1 H2]. apply Hno. unfold locell.
  apply (filter_132 (fun x => Nat.ltb x b) w i j k);
    [ keep | keep | keep | unfold has_132_at; repeat split; assumption ].
Qed.

Lemma rank_of_mask_hi : forall b w w' p,
  map (fun x => Nat.leb b x) w = map (fun x => Nat.leb b x) w' ->
  rank (fun x => Nat.leb b x) w p = rank (fun x => Nat.leb b x) w' p.
Proof.
  intros b w. induction w as [|x w IH]; intros w' p Hm.
  - destruct w' as [|y w']; [reflexivity | discriminate Hm].
  - destruct w' as [|y w']; [discriminate Hm|].
    cbn [map] in Hm. injection Hm as Hxy Hm'.
    destruct p as [|p]; [rewrite !rank_0; reflexivity|].
    rewrite !rank_cons, Hxy, (IH w' p Hm'). reflexivity.
Qed.

Lemma rank_of_mask : forall b w w' p,
  map (fun x => Nat.leb b x) w = map (fun x => Nat.leb b x) w' ->
  rank (fun x => Nat.ltb x b) w p = rank (fun x => Nat.ltb x b) w' p.
Proof.
  intros b w. induction w as [|x w IH]; intros w' p Hm.
  - destruct w' as [|y w']; [reflexivity | discriminate Hm].
  - destruct w' as [|y w']; [discriminate Hm|].
    cbn [map] in Hm. injection Hm as Hxy Hm'.
    destruct p as [|p]; [rewrite !rank_0; reflexivity|].
    rewrite !rank_cons.
    assert (E : Nat.ltb x b = Nat.ltb y b) by natb.
    rewrite E, (IH w' p Hm'). reflexivity.
Qed.

Definition swaplo (b : nat) (l w : list nat) : list nat :=
  mrg (map (fun x => Nat.leb b x) w) (hicell b w) l.

Lemma swaplo_spec : forall a b l w,
  In w (dominoes a b) -> length l = b ->
  (forall x, In x l -> (x < b)%nat) ->
  locell b (swaplo b l w) = l
  /\ hicell b (swaplo b l w) = hicell b w
  /\ map (fun x => Nat.leb b x) (swaplo b l w) = map (fun x => Nat.leb b x) w.
Proof.
  intros a b l w Hw Hl Hlb. apply dominoes_spec in Hw. destruct Hw as [Hp _].
  assert (Hhi : length (hicell b w) = a).
  { rewrite (hicell_perm_length (a + b) b w Hp ltac:(lia)). lia. }
  assert (Hcnt : countt (map (fun x => Nat.leb b x) w) = a)
    by (rewrite countt_map; exact Hhi).
  assert (Hlen : length (map (fun x => Nat.leb b x) w) = (a + b)%nat)
    by (rewrite len_map_gen; destruct Hp as [K _]; exact K).
  assert (H1 : length (hicell b w) = countt (map (fun x => Nat.leb b x) w))
    by (rewrite Hhi, Hcnt; reflexivity).
  assert (H2 : length l
               = (length (map (fun x => Nat.leb b x) w)
                  - countt (map (fun x => Nat.leb b x) w))%nat)
    by (rewrite Hl, Hlen, Hcnt; lia).
  assert (Hhib : forall x, In x (hicell b w) -> Nat.leb b x = true).
  { intros x Hx. unfold hicell in Hx. apply filter_In in Hx. exact (proj2 Hx). }
  assert (Hlob : forall y, In y l -> Nat.leb b y = false).
  { intros y Hy. assert (K := Hlb y Hy).
    destruct (Nat.leb_spec b y); [exfalso; lia | reflexivity]. }
  destruct (mrg_spec (fun x => Nat.leb b x) (map (fun x => Nat.leb b x) w)
              (hicell b w) l H1 H2 Hhib Hlob) as [Ehi [Elo Emask]].
  unfold swaplo.
  split; [| split; [exact Ehi | exact Emask]].
  rewrite locell_as_negb. exact Elo.
Qed.

Lemma swaplo_perm : forall a b l w,
  In w (dominoes a b) -> length l = b -> NoDup l ->
  (forall x, In x l -> (x < b)%nat) ->
  is_perm (swaplo b l w) (a + b).
Proof.
  intros a b l w Hw Hl Hnd Hlb.
  assert (Hw' := Hw). apply dominoes_spec in Hw'. destruct Hw' as [Hp _].
  destruct (swaplo_spec a b l w Hw Hl Hlb) as [Elo [Ehi Emask]].
  assert (Hperm : Permutation (swaplo b l w) (hicell b w ++ l)).
  { assert (Q := perm_filter_split (fun x => Nat.leb b x) (swaplo b l w)).
    cbn beta in Q.
    assert (K1 : filter (fun x => Nat.leb b x) (swaplo b l w) = hicell b w)
      by exact Ehi.
    assert (K2 : filter (fun x => negb (Nat.leb b x)) (swaplo b l w) = l)
      by (rewrite <- locell_as_negb; exact Elo).
    rewrite K1, K2 in Q. exact Q. }
  assert (Hlw : length (swaplo b l w) = (a + b)%nat).
  { rewrite <- (len_map_gen _ _ (fun x => Nat.leb b x)), Emask,
            len_map_gen. destruct Hp as [K _]. exact K. }
  split; [exact Hlw | split].
  - apply (Permutation_NoDup (Permutation_sym Hperm)).
    apply NoDup_app_disj.
    + unfold hicell. apply NoDup_filter. destruct Hp as [_ [K _]]. exact K.
    + exact Hnd.
    + intros z Hz1 Hz2.
      assert (K1 : (b <= z)%nat).
      { unfold hicell in Hz1. apply filter_In in Hz1.
        apply Nat.leb_le. exact (proj2 Hz1). }
      assert (K2 := Hlb z Hz2). lia.
  - intros x Hx.
    assert (K : In x (hicell b w ++ l))
      by (apply (Permutation_in _ Hperm); exact Hx).
    apply in_app_or in K. destruct K as [K|K].
    + unfold hicell in K. apply filter_In in K.
      destruct Hp as [_ [_ Hb]]. apply Hb. exact (proj1 K).
    + assert (Q := Hlb x K). lia.
Qed.

Lemma swaplo_in : forall a b l w,
  In w (dominoes a b) -> In l (gen132 b) ->
  (forall r1 r2, (r1 < r2)%nat -> (r2 < b)%nat ->
     (nth r1 l 0%nat < nth r2 l 0%nat)%nat ->
     (nth r1 (locell b w) 0%nat < nth r2 (locell b w) 0%nat)%nat) ->
  In (swaplo b l w) (dominoes a b).
Proof.
  intros a b l w Hw Hl Hasc.
  assert (Hlp : is_perm l b) by av.
  assert (Hl132 : ~ contains_132 l)
    by av.
  assert (Hlen : length l = b) by av.
  assert (Hnd : NoDup l) by av.
  assert (Hlb : forall x, In x l -> (x < b)%nat)
    by av.
  destruct (swaplo_spec a b l w Hw Hlen Hlb) as [Elo [Ehi Emask]].
  assert (Hw' := Hw). apply dominoes_spec in Hw'.
  destruct Hw' as [Hp [Hav [Hlo132 Hhi213]]].
  assert (Hip : is_perm (swaplo b l w) (a + b))
    by (apply swaplo_perm; assumption).
  apply dominoes_spec.
  split; [exact Hip | split; [| split]].
  - intro C.
    destruct (domino_criterion (swaplo b l w) b
                (fun i j k Hij Hjk Hk Bi Bj Bk =>
                   locell_132_pos b (swaplo b l w) i j k
                     ltac:(rewrite Elo; exact Hl132) Hij Hjk Hk Bi Bj Bk)
                (fun i j k Hij Hjk Hk Bi Bj Bk =>
                   hicell_213_pos b (swaplo b l w) i j k
                     ltac:(rewrite Ehi; exact Hhi213) Hij Hjk Hk Bi Bj Bk)
                C)
      as [p1 [q1 [p2 [q2 [A1 [A2 [A3 [A4 [A5 [A6 [A7 [A8 [A9 A10]]]]]]]]]]]]].
    assert (Hlw : length (swaplo b l w) = length w).
    { destruct Hip as [K1 _]. destruct Hp as [K2 _]. lia. }
    assert (Kp1 : Nat.ltb (nth p1 (swaplo b l w) 0%nat) b = true)
      by (apply Nat.ltb_lt; exact A5).
    assert (Kp2 : Nat.ltb (nth p2 (swaplo b l w) 0%nat) b = true)
      by (apply Nat.ltb_lt; exact A6).
    destruct (rank_spec (fun x => Nat.ltb x b) (swaplo b l w) p1
                ltac:(lia) Kp1) as [Rp1 Ep1].
    destruct (rank_spec (fun x => Nat.ltb x b) (swaplo b l w) p2
                ltac:(lia) Kp2) as [Rp2 Ep2].
    set (r1 := rank (fun x => Nat.ltb x b) (swaplo b l w) p1) in *.
    set (r2 := rank (fun x => Nat.ltb x b) (swaplo b l w) p2) in *.
    assert (Hr12 : (r1 < r2)%nat)
      by (unfold r1, r2; apply rank_mono; [lia | lia | exact Kp1]).
    assert (Hr2b : (r2 < b)%nat)
      by (unfold r2; change (filter (fun x => Nat.ltb x b) (swaplo b l w))
            with (locell b (swaplo b l w)) in Rp2;
          rewrite Elo, Hlen in Rp2; exact Rp2).
    assert (Hasc12 : (nth r1 l 0%nat < nth r2 l 0%nat)%nat).
    { change (filter (fun x => Nat.ltb x b) (swaplo b l w))
        with (locell b (swaplo b l w)) in Ep1, Ep2.
      rewrite Elo in Ep1, Ep2. rewrite Ep1, Ep2. lia. }
    assert (Hascw := Hasc r1 r2 Hr12 Hr2b Hasc12).
    assert (Emask' : map (fun x => Nat.leb b x) w
                     = map (fun x => Nat.leb b x) (swaplo b l w))
      by (symmetry; exact Emask).
    assert (Erk : forall p, rank (fun x => Nat.ltb x b) w p
                            = rank (fun x => Nat.ltb x b) (swaplo b l w) p)
      by (intro p; apply (rank_of_mask b w (swaplo b l w) p Emask')).
    assert (Klow : forall p, (p < length w)%nat ->
              Nat.ltb (nth p (swaplo b l w) 0%nat) b = true ->
              Nat.ltb (nth p w 0%nat) b = true).
    { intros p Hp2 Hb2.
      assert (E := f_equal (fun z => nth p z false) Emask').
      cbn beta in E.
      rewrite (map_nth_defb (fun x => Nat.leb b x) w p ltac:(lia)) in E.
      rewrite (map_nth_defb (fun x => Nat.leb b x) (swaplo b l w) p
                 ltac:(lia)) in E.
      destruct (Nat.leb_spec b (nth p w 0%nat));
        destruct (Nat.leb_spec b (nth p (swaplo b l w) 0%nat));
        try discriminate E;
        [exfalso; apply Nat.ltb_lt in Hb2; lia | apply Nat.ltb_lt; lia]. }
    assert (Kwp1 : Nat.ltb (nth p1 w 0%nat) b = true)
      by (apply Klow; [lia | exact Kp1]).
    assert (Kwp2 : Nat.ltb (nth p2 w 0%nat) b = true)
      by (apply Klow; [lia | exact Kp2]).
    destruct (rank_spec (fun x => Nat.ltb x b) w p1 ltac:(lia) Kwp1) as [_ Fp1].
    destruct (rank_spec (fun x => Nat.ltb x b) w p2 ltac:(lia) Kwp2) as [_ Fp2].
    change (filter (fun x => Nat.ltb x b) w) with (locell b w) in Fp1, Fp2.
    rewrite (Erk p1) in Fp1. rewrite (Erk p2) in Fp2.
    assert (Khigh : forall q, (q < length w)%nat ->
              (b <= nth q (swaplo b l w) 0%nat)%nat ->
              nth q w 0%nat = nth q (swaplo b l w) 0%nat).
    { intros q Hq Hb2.
      assert (Kq : Nat.leb b (nth q (swaplo b l w) 0%nat) = true)
        by (apply Nat.leb_le; exact Hb2).
      assert (E := f_equal (fun z => nth q z false) Emask').
      cbn beta in E.
      rewrite (map_nth_defb (fun x => Nat.leb b x) w q ltac:(lia)) in E.
      rewrite (map_nth_defb (fun x => Nat.leb b x) (swaplo b l w) q
                 ltac:(lia)) in E.
      rewrite Kq in E.
      assert (Kwq : Nat.leb b (nth q w 0%nat) = true) by exact E.
      destruct (rank_spec (fun x => Nat.leb b x) w q ltac:(lia) Kwq)
        as [_ Gw].
      destruct (rank_spec (fun x => Nat.leb b x) (swaplo b l w) q
                  ltac:(lia) Kq) as [_ Gs].
      change (filter (fun x => Nat.leb b x) w) with (hicell b w) in Gw.
      change (filter (fun x => Nat.leb b x) (swaplo b l w))
        with (hicell b (swaplo b l w)) in Gs.
      rewrite Ehi in Gs.
      assert (Erk2 := rank_of_mask_hi b w (swaplo b l w) q Emask').
      rewrite Erk2, Gs in Gw. symmetry. exact Gw. }
    assert (Eq1 : nth q1 w 0%nat = nth q1 (swaplo b l w) 0%nat)
      by (apply Khigh; [lia | exact A7]).
    assert (Eq2 : nth q2 w 0%nat = nth q2 (swaplo b l w) 0%nat)
      by (apply Khigh; [lia | exact A8]).
    apply Hav.
    apply (domino_criterion_conv w b p1 q1 p2 q2); try lia.
    + apply Nat.ltb_lt. exact Kwp1.
    + apply Nat.ltb_lt. exact Kwp2.
    + rewrite <- Fp1, <- Fp2. exact Hascw.
  - rewrite Elo. exact Hl132.
  - rewrite Ehi. exact Hhi213.
Qed.

Theorem dA_ascent_mono : forall a b l l',
  In l (gen132 b) -> In l' (gen132 b) ->
  (forall r1 r2, (r1 < r2)%nat -> (r2 < b)%nat ->
     (nth r1 l 0%nat < nth r2 l 0%nat)%nat ->
     (nth r1 l' 0%nat < nth r2 l' 0%nat)%nat) ->
  (dA a b l' <= dA a b l)%nat.
Proof.
  intros a b l l' Hl Hl' Hasc.
  assert (Hlp : is_perm l b) by av.
  assert (Hlen : length l = b) by av.
  assert (Hlb : forall x, In x l -> (x < b)%nat)
    by av.
  unfold dA.
  rewrite <- (len_map_gen _ _ (swaplo b l)
    (filter (fun w => if list_eq_dec Nat.eq_dec (locell b w) l'
                      then true else false) (dominoes a b))).
  apply NoDup_incl_length.
  - apply NoDup_map_inj.
    + apply NoDup_filter. apply dominoes_nodup.
    + intros x y Hx Hy He.
      apply filter_In in Hx. destruct Hx as [Hxd Hxl].
      apply filter_In in Hy. destruct Hy as [Hyd Hyl].
      destruct (list_eq_dec Nat.eq_dec (locell b x) l') as [Ex|]; [|discriminate].
      destruct (list_eq_dec Nat.eq_dec (locell b y) l') as [Ey|]; [|discriminate].
      destruct (swaplo_spec a b l x Hxd Hlen Hlb) as [_ [Ehx Emx]].
      destruct (swaplo_spec a b l y Hyd Hlen Hlb) as [_ [Ehy Emy]].
      assert (Ehi : hicell b x = hicell b y)
        by (rewrite <- Ehx, <- Ehy, He; reflexivity).
      assert (Ema : map (fun z => Nat.leb b z) x = map (fun z => Nat.leb b z) y)
        by (rewrite <- Emx, <- Emy, He; reflexivity).
      cells b.
  - intros z Hz. apply in_map_iff in Hz. destruct Hz as [w [Hwz Hwin]].
    subst z. apply filter_In in Hwin. destruct Hwin as [Hwd Hwl].
    destruct (list_eq_dec Nat.eq_dec (locell b w) l') as [Ew|]; [|discriminate].
    apply filter_In. split.
    + apply (swaplo_in a b l w Hwd Hl).
      intros r1 r2 H1 H2 H3. rewrite Ew. apply Hasc; assumption.
    + destruct (swaplo_spec a b l w Hwd Hlen Hlb) as [Elo _].
      destruct (list_eq_dec Nat.eq_dec (locell b (swaplo b l w)) l);
        [reflexivity | contradiction].
Qed.

Corollary dA_le_dec_of_mono : forall a b l, In l (gen132 b) ->
  (dA a b l <= dA a b (decpat b))%nat.
Proof.
  intros a b l Hl. apply (dA_ascent_mono a b (decpat b) l).
  - apply gen132_spec. split; [apply decpat_is_perm | apply decpat_avoids_132].
  - exact Hl.
  - intros r1 r2 H1 H2 H3. exfalso.
    assert (K := decpat_dec b r1 r2 H1 H2). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The capped profile state.  three_values_append says the profile gains
   exactly the values at strict candidate positions, and new_three_append says
   those in turn move by one letter at a time, so a state carrying

     P z    the profile, w |-> three_value u w
     A z w  z <= w and w occurs in u after some entry below z
     B z    u has an entry below z

   closes under appending a letter: each of the three is determined by the
   three and the letter.  Legality is decided by P alone. *)

Definition after (u : list nat) (z w : nat) : Prop :=
  (z <= w)%nat /\ exists j, (j < length u)%nat /\ nth j u 0%nat = w
                            /\ exists i, (i < j)%nat /\ (nth i u 0%nat < z)%nat.

Lemma after_dec : forall u z w, {after u z w} + {~ after u z w}.
Proof.
  intros u z w. unfold after.
  destruct (le_dec z w) as [Hzw|Hzw]; [|right; tauto].
  destruct (bounded_ex_dec
    (fun j => nth j u 0%nat = w /\ exists i, (i < j)%nat /\ (nth i u 0%nat < z)%nat)
    (length u)) as [Hex|Hno].
  { intro j.
    destruct (Nat.eq_dec (nth j u 0%nat) w) as [E|E]; [|right; tauto].
    destruct (bounded_ex_dec (fun i => (nth i u 0%nat < z)%nat) j
                (fun i => lt_dec (nth i u 0%nat) z)) as [K|K].
    - left. split; [exact E | exact K].
    - right. intros [_ C]. exact (K C). }
  - left. split; [exact Hzw|]. destruct Hex as [j [Hj [E Hi]]].
    exists j. split; [exact Hj | split; [exact E | exact Hi]].
  - right. intros [_ [j [Hj [E Hi]]]]. apply Hno. exists j.
    split; [exact Hj | split; [exact E | exact Hi]].
Defined.

Lemma has_below_dec : forall u z, {has_below u z} + {~ has_below u z}.
Proof.
  intros u z. unfold has_below.
  apply (bounded_ex_dec (fun i => (nth i u 0%nat < z)%nat) (length u)).
  intro i. apply lt_dec.
Defined.

(* new_three is the strict part of after *)
Lemma new_three_after : forall u z w,
  new_three u z w <-> (after u z w /\ (z < w)%nat).
Proof.
  intros u z w. unfold new_three, after, candidate_strict. split.
  - intros [j [[Hj [Hzj [i [Hij Hi]]]] Hw]].
    subst w. split; [split; [lia|] | lia].
    exists j. split; [exact Hj | split; [reflexivity|]].
    exists i. split; [exact Hij | exact Hi].
  - intros [[_ [j [Hj [E [i [Hij Hi]]]]]] Hzw].
    exists j. split; [| exact E]. subst w.
    split; [exact Hj | split; [exact Hzw|]].
    exists i. split; [exact Hij | exact Hi].
Qed.

Lemma after_append : forall u y z w,
  after (u ++ [y]) z w
  <-> (after u z w \/ (w = y /\ (z <= y)%nat /\ has_below u z)).
Proof.
  intros u y z w. unfold after, has_below. split.
  - intros [Hzw [j [Hj [E [i [Hij Hi]]]]]].
    rewrite len_app in Hj. cbn [length] in Hj.
    rewrite (nth_app1 u [y] i 0%nat) in Hi by lia.
    destruct (Nat.eq_dec j (length u)) as [Hje|Hje].
    + right. subst j. rewrite nth_last in E.
      split; [symmetry; exact E | split; [lia|]].
      exists i. split; [lia | exact Hi].
    + left. rewrite (nth_app1 u [y] j 0%nat) in E by lia.
      split; [exact Hzw|]. exists j. split; [lia | split; [exact E|]].
      exists i. split; [exact Hij | exact Hi].
  - intros [[Hzw [j [Hj [E [i [Hij Hi]]]]]] | [Hw [Hzy [i [Hi Hiz]]]]].
    + split; [exact Hzw|]. exists j.
      rewrite (nth_app1 u [y] j 0%nat) by lia.
      split; [rewrite len_app; cbn [length]; lia | split; [exact E|]].
      exists i. rewrite (nth_app1 u [y] i 0%nat) by lia.
      split; [exact Hij | exact Hi].
    + subst w. split; [exact Hzy|]. exists (length u).
      rewrite nth_last.
      split; [rewrite len_app; cbn [length]; lia | split; [reflexivity|]].
      exists i. rewrite (nth_app1 u [y] i 0%nat) by lia.
      split; [lia | exact Hiz].
Qed.

Lemma has_below_append : forall u y z,
  has_below (u ++ [y]) z <-> (has_below u z \/ (y < z)%nat).
Proof.
  intros u y z. unfold has_below. split.
  - intros [i [Hi Hiz]]. rewrite len_app in Hi. cbn [length] in Hi.
    destruct (Nat.eq_dec i (length u)) as [E|E].
    + right. subst i. rewrite nth_last in Hiz. exact Hiz.
    + left. exists i. rewrite (nth_app1 u [y] i 0%nat) in Hiz by lia.
      split; [lia | exact Hiz].
  - intros [[i [Hi Hiz]] | Hy].
    + exists i. rewrite (nth_app1 u [y] i 0%nat) by lia.
      split; [rewrite len_app; cbn [length]; lia | exact Hiz].
    + exists (length u). rewrite nth_last.
      split; [rewrite len_app; cbn [length]; lia | exact Hy].
Qed.

(* ------------------------------------------------------------------ *)
(* the state itself, capped at K *)

Lemma nth_map_seq_b : forall (f : nat -> bool) K t, (t < K)%nat ->
  nth t (map f (seq 0 K)) false = f t.
Proof.
  intros f K t H.
  rewrite (map_nth_defb f (seq 0 K) t ltac:(rewrite length_seq; exact H)).
  rewrite seq_nth by exact H. reflexivity.
Qed.

Lemma nth_map_seq_l : forall (f : nat -> list bool) K t, (t < K)%nat ->
  nth t (map f (seq 0 K)) nil = f t.
Proof.
  intros f K t H.
  rewrite (nth_indep (map f (seq 0 K)) nil (f 0))
    by (rewrite len_map_gen, length_seq; exact H).
  rewrite map_nth. rewrite seq_nth by exact H. reflexivity.
Qed.

Definition profv (K : nat) (u : list nat) : list bool :=
  map (fun w => if three_value_dec u w then true else false) (seq 0 K).

Definition afterv (K : nat) (u : list nat) : list (list bool) :=
  map (fun z => map (fun w => if after_dec u z w then true else false)
                    (seq 0 K)) (seq 0 K).

Definition belowv (K : nat) (u : list nat) : list bool :=
  map (fun z => if has_below_dec u z then true else false) (seq 0 K).

Record pstate : Type := mkPst { psP : list bool ;
                                psA : list (list bool) ;
                                psB : list bool }.

Definition pabs (K : nat) (u : list nat) : pstate :=
  mkPst (profv K u) (afterv K u) (belowv K u).

Definition stepP (K : nat) (S : pstate) (y : nat) : list bool :=
  map (fun w => orb (nth w (psP S) false)
                    (andb (nth w (nth y (psA S) nil) false) (Nat.ltb y w)))
      (seq 0 K).

Definition stepA (K : nat) (S : pstate) (y : nat) : list (list bool) :=
  map (fun z => map (fun w => orb (nth w (nth z (psA S) nil) false)
                                  (andb (andb (Nat.eqb w y) (Nat.leb z y))
                                        (nth z (psB S) false)))
                    (seq 0 K))
      (seq 0 K).

Definition stepB (K : nat) (S : pstate) (y : nat) : list bool :=
  map (fun z => orb (nth z (psB S) false) (Nat.ltb y z)) (seq 0 K).

Definition pstp (K : nat) (S : pstate) (y : nat) : pstate :=
  mkPst (stepP K S y) (stepA K S y) (stepB K S y).

Lemma dec_true : forall (P : Prop) (d : {P} + {~ P}),
  ((if d then true else false) = true) <-> P.
Proof.
  intros P d. destruct d as [h|h]; split.
  - intros _. exact h.
  - intros _. reflexivity.
  - intro C. discriminate C.
  - intro C. contradiction.
Qed.

Lemma bool_iff_eq : forall (P : Prop) (d : {P} + {~ P}) (b : bool),
  (P <-> b = true) -> (if d then true else false) = b.
Proof.
  intros P d b H. destruct d as [h|h]; destruct b; try reflexivity.
  - assert (K := proj1 H h). discriminate K.
  - exfalso. apply h. apply H. reflexivity.
Qed.

(* A decider read against a boolean expression: strip the decider, then strip
   whatever connectives and comparisons the expression is built from. *)
Ltac decb :=
  apply bool_iff_eq;
  rewrite ?orb_true_iff, ?andb_true_iff, ?negb_true_iff, ?implb_true_iff,
          ?dec_true, ?Nat.ltb_lt, ?Nat.leb_le, ?Nat.eqb_eq.

(* The state closes under appending a letter. *)
Theorem pabs_append : forall K u y, (y < K)%nat ->
  pabs K (u ++ [y]) = pstp K (pabs K u) y.
Proof.
  intros K u y HyK. unfold pabs, pstp. f_equal.
  - unfold profv, stepP. cbn [psP psA].
    apply map_ext_in. intros w Hw. apply in_seq in Hw. destruct Hw as [_ Hw].
    unfold afterv. rewrite (nth_map_seq_l _ K y HyK).
    rewrite (nth_map_seq_b _ K w Hw), (nth_map_seq_b _ K w Hw).
    decb.
    rewrite (three_values_append u y w).
    split; intros [Q|Q].
    + left. exact Q.
    + right. apply (proj1 (new_three_after u y w)). exact Q.
    + left. exact Q.
    + right. apply (proj2 (new_three_after u y w)). exact Q.
  - unfold afterv, stepA. cbn [psA psB].
    apply map_ext_in. intros z Hz. apply in_seq in Hz. destruct Hz as [_ Hz].
    apply map_ext_in. intros w Hw. apply in_seq in Hw. destruct Hw as [_ Hw].
    rewrite (nth_map_seq_l _ K z Hz), (nth_map_seq_b _ K w Hw).
    unfold belowv. rewrite (nth_map_seq_b _ K z Hz).
    decb.
    rewrite (after_append u y z w). tauto.
  - unfold belowv, stepB. cbn [psB].
    apply map_ext_in. intros z Hz. apply in_seq in Hz. destruct Hz as [_ Hz].
    rewrite (nth_map_seq_b _ K z Hz).
    decb.
    rewrite (has_below_append u y z). tauto.
Qed.

(* ------------------------------------------------------------------ *)
(* The same for ext, which renormalises.  Bumping the alphabet at v shifts
   every threshold by unbump, and the value v itself acquires no occurrence,
   so the state moves by an explicit shift and then one append. *)

Lemma bump_lt_thresh : forall v x z,
  (bump v x < z)%nat <-> (x < unbump v z)%nat.
Proof.
  intros v x z. unfold bump, unbump.
  destruct (Nat.leb_spec v x); destruct (Nat.ltb_spec v z); lia.
Qed.

Lemma bump_eq_iff : forall v x w, bump v x = w <-> (w <> v /\ x = unbump v w).
Proof.
  intros v x w. split.
  - intro E. split.
    + rewrite <- E. apply bump_ne.
    + rewrite <- E, unbump_bump. reflexivity.
  - intros [Hw Hx]. subst x. apply bump_unbump. exact Hw.
Qed.

Lemma unbump_le_iff : forall v z w, w <> v ->
  ((z <= w)%nat <-> (unbump v z <= unbump v w)%nat).
Proof.
  intros v z w Hw. unfold unbump.
  destruct (Nat.ltb_spec v z); destruct (Nat.ltb_spec v w); lia.
Qed.

Lemma three_value_map_bump : forall v u w,
  three_value (map (bump v) u) w <-> (w <> v /\ three_value u (unbump v w)).
Proof.
  intros v u w. unfold three_value. split.
  - intros [i [j [k [H132 Hw]]]].
    assert (Hj : (j < length u)%nat).
    { unfold has_132_at in H132. rewrite len_map in H132.
      destruct H132 as [_ [Hjk [Hk _]]]. lia. }
    rewrite (nth_map_in (bump v) u j Hj) in Hw.
    apply bump_eq_iff in Hw. destruct Hw as [Hne Hval].
    split; [exact Hne|]. exists i, j, k.
    split; [apply (has_132_map v u i j k); exact H132 | exact Hval].
  - intros [Hne [i [j [k [H132 Hw]]]]].
    assert (Hj : (j < length u)%nat).
    { unfold has_132_at in H132. destruct H132 as [_ [Hjk [Hk _]]]. lia. }
    exists i, j, k.
    rewrite (nth_map_in (bump v) u j Hj).
    split; [apply (has_132_map v u i j k); exact H132|].
    apply bump_eq_iff. split; [exact Hne | exact Hw].
Qed.

Lemma has_below_map_bump : forall v u z,
  has_below (map (bump v) u) z <-> has_below u (unbump v z).
Proof.
  intros v u z. unfold has_below. rewrite len_map. split.
  - intros [i [Hi Hiz]]. rewrite (nth_map_in (bump v) u i Hi) in Hiz.
    exists i. split; [exact Hi | apply bump_lt_thresh; exact Hiz].
  - intros [i [Hi Hiz]]. exists i.
    rewrite (nth_map_in (bump v) u i Hi).
    split; [exact Hi | apply bump_lt_thresh; exact Hiz].
Qed.

Lemma after_map_bump : forall v u z w,
  after (map (bump v) u) z w
  <-> (w <> v /\ after u (unbump v z) (unbump v w)).
Proof.
  intros v u z w. unfold after. rewrite len_map. split.
  - intros [Hzw [j [Hj [E [i [Hij Hi]]]]]].
    rewrite (nth_map_in (bump v) u j Hj) in E.
    rewrite (nth_map_in (bump v) u i ltac:(lia)) in Hi.
    apply bump_eq_iff in E. destruct E as [Hne Hval].
    split; [exact Hne|].
    split; [apply (unbump_le_iff v z w Hne); exact Hzw|].
    exists j. split; [exact Hj | split; [exact Hval|]].
    exists i. split; [exact Hij | apply bump_lt_thresh; exact Hi].
  - intros [Hne [Hzw [j [Hj [E [i [Hij Hi]]]]]]].
    split; [apply (unbump_le_iff v z w Hne); exact Hzw|].
    exists j. rewrite (nth_map_in (bump v) u j Hj).
    split; [exact Hj|].
    split; [apply bump_eq_iff; split; [exact Hne | exact E]|].
    exists i. rewrite (nth_map_in (bump v) u i ltac:(lia)).
    split; [exact Hij | apply bump_lt_thresh; exact Hi].
Qed.

Definition shiftP (K v : nat) (Pl : list bool) : list bool :=
  map (fun w => if Nat.eqb w v then false else nth (unbump v w) Pl false)
      (seq 0 K).

Definition shiftB (K v : nat) (Bl : list bool) : list bool :=
  map (fun z => nth (unbump v z) Bl false) (seq 0 K).

Definition shiftA (K v : nat) (Al : list (list bool)) : list (list bool) :=
  map (fun z => map (fun w => if Nat.eqb w v then false
                              else nth (unbump v w)
                                       (nth (unbump v z) Al nil) false)
                    (seq 0 K))
      (seq 0 K).

Definition pshift (K v : nat) (S : pstate) : pstate :=
  mkPst (shiftP K v (psP S)) (shiftA K v (psA S)) (shiftB K v (psB S)).

Lemma unbump_le : forall v w, (unbump v w <= w)%nat.
Proof. intros v w. unfold unbump. destruct (Nat.ltb_spec v w); lia. Qed.

Lemma pabs_map_bump : forall K u v,
  pabs K (map (bump v) u) = pshift K v (pabs K u).
Proof.
  intros K u v. unfold pabs, pshift. f_equal.
  - unfold profv, shiftP. cbn [psP].
    apply map_ext_in. intros w Hw. apply in_seq in Hw. destruct Hw as [_ Hw].
    rewrite (nth_map_seq_b _ K (unbump v w)
               ltac:(assert (H := unbump_le v w); lia)).
    decb.
    destruct (Nat.eqb_spec w v) as [E|E].
    + subst w. split; [| discriminate].
      intro C. exfalso.
      exact (proj1 (proj1 (three_value_map_bump v u v) C) eq_refl).
    + rewrite dec_true, (three_value_map_bump v u w). tauto.
  - unfold afterv, shiftA. cbn [psA].
    apply map_ext_in. intros z Hz. apply in_seq in Hz. destruct Hz as [_ Hz].
    apply map_ext_in. intros w Hw. apply in_seq in Hw. destruct Hw as [_ Hw].
    rewrite (nth_map_seq_l _ K (unbump v z)
               ltac:(assert (H := unbump_le v z); lia)).
    rewrite (nth_map_seq_b _ K (unbump v w)
               ltac:(assert (H := unbump_le v w); lia)).
    decb.
    destruct (Nat.eqb_spec w v) as [E|E].
    + subst w. split; [| discriminate].
      intro C. exfalso.
      exact (proj1 (proj1 (after_map_bump v u z v) C) eq_refl).
    + rewrite dec_true, (after_map_bump v u z w). tauto.
  - unfold belowv, shiftB. cbn [psB].
    apply map_ext_in. intros z Hz. apply in_seq in Hz. destruct Hz as [_ Hz].
    rewrite (nth_map_seq_b _ K (unbump v z)
               ltac:(assert (H := unbump_le v z); lia)).
    decb. apply has_below_map_bump.
Qed.

Definition pext (K : nat) (S : pstate) (v : nat) : pstate :=
  pstp K (pshift K v S) v.

Theorem pabs_ext : forall K u v, (v < K)%nat ->
  pabs K (ext u v) = pext K (pabs K u) v.
Proof.
  intros K u v HvK. unfold ext, pext.
  rewrite (pabs_append K (map (bump v) u) v HvK), (pabs_map_bump K u v).
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Legality is decided by the state, so a level is a transfer over states. *)

Definition plegal (K : nat) (S : pstate) (y : nat) : bool :=
  forallb (fun w => implb (nth w (psP S) false) (Nat.leb y w)) (seq 0 K).

Lemma three_value_in : forall u w, three_value u w -> In w u.
Proof.
  intros u w [i [j [k [H132 Hw]]]]. unfold has_132_at in H132.
  destruct H132 as [_ [Hjk [Hk _]]]. rewrite <- Hw. apply nth_in. lia.
Qed.

Lemma plegal_correct : forall K u y,
  (forall x, In x u -> (x < K)%nat) -> ~ contains_1324 u ->
  plegal K (pabs K u) y = legalb u y.
Proof.
  intros K u y HK Hav.
  destruct (legalb u y) eqn:E.
  - apply forallb_forall. intros w Hw. apply in_seq in Hw. destruct Hw as [_ Hw].
    unfold pabs. cbn [psP]. unfold profv.
    rewrite (nth_map_seq_b _ K w Hw).
    destruct (three_value_dec u w) as [H|H]; cbn [implb]; [|reflexivity].
    apply Nat.leb_le.
    apply (proj1 (append_rule_profile u y Hav) (proj1 (legalb_spec u y) E) w H).
  - destruct (plegal K (pabs K u) y) eqn:F; [|reflexivity]. exfalso.
    assert (Hl : legal u y).
    { apply (append_rule_profile u y Hav). intros w Hw.
      assert (HwK : (w < K)%nat) by (apply HK; apply three_value_in; exact Hw).
      unfold plegal in F. rewrite forallb_forall in F.
      assert (Q := F w ltac:(apply in_seq; lia)).
      unfold pabs in Q. cbn [psP] in Q. unfold profv in Q.
      rewrite (nth_map_seq_b _ K w HwK) in Q.
      destruct (three_value_dec u w) as [H|H]; [|contradiction].
      cbn [implb] in Q. apply Nat.leb_le. exact Q. }
    assert (E2 : legalb u y = true) by (apply legalb_spec; exact Hl).
    rewrite E in E2. discriminate.
Qed.

Lemma map_flat_map : forall (A B C : Type) (f : B -> C) (g : A -> list B) l,
  map f (flat_map g l) = flat_map (fun x => map f (g x)) l.
Proof.
  intros A B C f g. induction l as [|a l IH]; cbn [flat_map map]; [reflexivity|].
  rewrite map_app, IH. reflexivity.
Qed.

Lemma flat_map_map : forall (A B C : Type) (f : A -> B) (g : B -> list C) l,
  flat_map g (map f l) = flat_map (fun x => g (f x)) l.
Proof.
  intros A B C f g. induction l as [|a l IH]; cbn [map flat_map]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

(* the level as a multiset of states, stepped without reference to the words *)
Theorem slist_step : forall K m, (S m <= K)%nat ->
  map (pabs K) (gen (S m))
  = flat_map (fun st => map (pext K st) (filter (plegal K st) (seq 0 (S m))))
             (map (pabs K) (gen m)).
Proof.
  intros K m HK.
  rewrite gen_S, map_flat_map, flat_map_map.
  apply flat_map_ext_in. intros u Hu.
  assert (Hg := Hu). apply gen_spec in Hg. destruct Hg as [Hp Hav].
  assert (HKu : forall x, In x u -> (x < K)%nat).
  { intros x Hx. destruct Hp as [_ [_ Hb]]. assert (Q := Hb x Hx). lia. }
  rewrite (filter_ext_in_nat (legalb u) (plegal K (pabs K u)) (seq 0 (S m)))
    by (intros v _; symmetry; apply plegal_correct; assumption).
  rewrite map_map. apply map_ext_in. intros v Hv.
  apply filter_In in Hv. destruct Hv as [Hvs _]. apply in_seq in Hvs.
  apply pabs_ext. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* the compressed level: states with multiplicities *)

Lemma pstate_eq_dec : forall S T : pstate, {S = T} + {S <> T}.
Proof.
  intros [P1 A1 B1] [P2 A2 B2].
  destruct (list_eq_dec Bool.bool_dec P1 P2) as [E1|E1]; [|right; congruence].
  destruct (list_eq_dec (list_eq_dec Bool.bool_dec) A1 A2) as [E2|E2];
    [|right; congruence].
  destruct (list_eq_dec Bool.bool_dec B1 B2) as [E3|E3]; [|right; congruence].
  left. congruence.
Defined.

Fixpoint addmul (st : pstate) (c : nat) (L : list (pstate * nat))
  : list (pstate * nat) :=
  match L with
  | nil => (st, c) :: nil
  | p :: r => if pstate_eq_dec (fst p) st
              then (fst p, snd p + c) :: r
              else p :: addmul st c r
  end.

Fixpoint compress (l : list pstate) : list (pstate * nat) :=
  match l with
  | nil => nil
  | st :: r => addmul st 1 (compress r)
  end.

Definition expand (L : list (pstate * nat)) : list pstate :=
  flat_map (fun p => repeat (fst p) (snd p)) L.

Lemma expand_addmul : forall st c L,
  Permutation (expand (addmul st c L)) (repeat st c ++ expand L).
Proof.
  intros st c. induction L as [|p L IH]; cbn [addmul expand flat_map fst snd].
  - rewrite !app_nil_r. apply Permutation_refl.
  - destruct (pstate_eq_dec (fst p) st) as [E|E]; cbn [expand flat_map fst snd].
    + subst st. rewrite repeat_app.
      apply Permutation_trans
        with ((repeat (fst p) c ++ repeat (fst p) (snd p)) ++ expand L).
      * apply Permutation_app_tail. apply Permutation_app_comm.
      * rewrite <- app_assoc. apply Permutation_refl.
    + eapply Permutation_trans; [apply Permutation_app_head; apply IH|].
      apply Permutation_trans
        with ((repeat (fst p) (snd p) ++ repeat st c) ++ expand L).
      * rewrite app_assoc. apply Permutation_refl.
      * apply Permutation_trans
          with ((repeat st c ++ repeat (fst p) (snd p)) ++ expand L).
        -- apply Permutation_app_tail. apply Permutation_app_comm.
        -- rewrite <- app_assoc. apply Permutation_refl.
Qed.

Lemma expand_compress : forall l, Permutation (expand (compress l)) l.
Proof.
  induction l as [|st l IH]; cbn [compress expand flat_map];
    [apply Permutation_refl|].
  eapply Permutation_trans; [apply expand_addmul|].
  cbn [repeat app]. apply perm_skip. exact IH.
Qed.

Lemma total_expand : forall L,
  fold_right (fun p acc => snd p + acc) 0 L = length (expand L).
Proof.
  induction L as [|p L IH]; cbn [expand flat_map fold_right]; [reflexivity|].
  rewrite len_app_gen, repeat_length, IH. reflexivity.
Qed.

(* the empty word's state, written out so the transfer computes *)
Lemma map_const_list : forall (A B : Type) (a : A) (l : list B),
  map (fun _ => a) l = repeat a (length l).
Proof.
  intros A B a. induction l as [|x l IH]; cbn [map length repeat];
    [reflexivity | rewrite IH; reflexivity].
Qed.

Definition pnil (K : nat) : pstate :=
  mkPst (repeat false K) (repeat (repeat false K) K) (repeat false K).

Lemma three_value_nil : forall w, ~ three_value nil w.
Proof.
  intros w [i [j [k [H132 _]]]]. unfold has_132_at in H132.
  destruct H132 as [_ [_ [Hk _]]]. cbn [length] in Hk. lia.
Qed.

Lemma after_nil : forall z w, ~ after nil z w.
Proof.
  intros z w [_ [j [Hj _]]]. cbn [length] in Hj. lia.
Qed.

Lemma has_below_nil : forall z, ~ has_below nil z.
Proof. intros z [i [Hi _]]. cbn [length] in Hi. lia. Qed.

Lemma pabs_nil : forall K, pabs K nil = pnil K.
Proof.
  intro K. unfold pabs, pnil. f_equal.
  - unfold profv.
    rewrite (map_ext_in _ (fun _ => false))
      by (intros w _; destruct (three_value_dec nil w) as [H|H];
          [exfalso; exact (three_value_nil w H) | reflexivity]).
    rewrite map_const_list, length_seq. reflexivity.
  - unfold afterv.
    rewrite (map_ext_in _ (fun _ => repeat false K)).
    + rewrite map_const_list, length_seq. reflexivity.
    + intros z _.
      rewrite (map_ext_in _ (fun _ => false))
        by (intros w _; destruct (after_dec nil z w) as [H|H];
            [exfalso; exact (after_nil z w H) | reflexivity]).
      rewrite map_const_list, length_seq. reflexivity.
  - unfold belowv.
    rewrite (map_ext_in _ (fun _ => false))
      by (intros z _; destruct (has_below_dec nil z) as [H|H];
          [exfalso; exact (has_below_nil z H) | reflexivity]).
    rewrite map_const_list, length_seq. reflexivity.
Qed.

(* the level of the transfer, built from states alone *)
Fixpoint slev (K m : nat) : list pstate :=
  match m with
  | O => pnil K :: nil
  | S m' => flat_map (fun st => map (pext K st)
                                    (filter (plegal K st) (seq 0 (S m'))))
                     (slev K m')
  end.

Theorem slev_eq : forall K m, (m <= K)%nat -> slev K m = map (pabs K) (gen m).
Proof.
  intros K m. induction m as [|m IH]; intro HK.
  - cbn [slev gen map]. rewrite pabs_nil. reflexivity.
  - cbn [slev]. rewrite (IH ltac:(lia)). symmetry. apply slist_step. exact HK.
Qed.

(* The transfer counts the class. *)
Theorem transfer_card : forall K m, (m <= K)%nat -> length (slev K m) = card m.
Proof.
  intros K m HK. rewrite (slev_eq K m HK), len_map_gen. reflexivity.
Qed.

(* the compressed level, so the transfer is a transfer rather than a relabelling *)
Fixpoint compressw (L : list (pstate * nat)) : list (pstate * nat) :=
  match L with nil => nil | p :: r => addmul (fst p) (snd p) (compressw r) end.

Lemma expand_compressw : forall L, Permutation (expand (compressw L)) (expand L).
Proof.
  induction L as [|p L IH]; cbn [compressw expand flat_map]; [apply Permutation_refl|].
  eapply Permutation_trans; [apply expand_addmul|].
  apply Permutation_app_head. exact IH.
Qed.

Definition tstep (K m : nat) (L : list (pstate * nat)) : list (pstate * nat) :=
  compressw (flat_map (fun p => map (fun v => (pext K (fst p) v, snd p))
                                    (filter (plegal K (fst p)) (seq 0 (S m))))
                      L).

Fixpoint tlev (K m : nat) : list (pstate * nat) :=
  match m with
  | O => (pnil K, 1%nat) :: nil
  | S m' => tstep K m' (tlev K m')
  end.

Definition tcard (K m : nat) : nat :=
  fold_right (fun p acc => (snd p + acc)%nat) 0%nat (tlev K m).

(* ------------------------------------------------------------------ *)
(* The fast layer, completed.  genf hoists mu out of the inner loop and
   gen132f replaces the quadratic safety decider by the prefix test; every
   quantity that is ever evaluated is given a form built on those two, so a
   reduction cannot reach the definitional enumerators by oversight. *)

Definition cardf (m : nat) : nat := length (genf m).

Lemma cardf_eq : forall m, cardf m = card m.
Proof. intro m. unfold cardf, card. rewrite genf_eq. reflexivity. Qed.

Definition card132f (m : nat) : nat := length (gen132f m).

Lemma card132f_eq : forall m, card132f m = card132 m.
Proof. intro m. unfold card132f, card132. rewrite gen132f_eq. reflexivity. Qed.

Definition Ddiagf (d M : nat) : nat :=
  length (filter (fun w => avoids132b (firstn M w)) (genf (M + d))).

Lemma Ddiagf_eq : forall d M, Ddiagf d M = Ddiag d M.
Proof. intros d M. unfold Ddiagf, Ddiag. rewrite genf_eq. reflexivity. Qed.

Definition Nsigf (d M : nat) (sg : list nat) : nat :=
  length (filter (fun w =>
            andb (avoids132b (firstn M w))
                 (if list_eq_dec Nat.eq_dec (suffix_pat d w) sg
                  then true else false))
          (genf (M + d))).

Lemma Nsigf_eq : forall d M sg, Nsigf d M sg = Nsig d M sg.
Proof. intros d M sg. unfold Nsigf, Nsig. rewrite genf_eq. reflexivity. Qed.

Definition dAf (a b : nat) (l : list nat) : nat := natlook (dAtablef a b) l.

Lemma dAf_eq : forall a b l, In l (gen132 b) -> dAf a b l = dA a b l.
Proof.
  intros a b l H. unfold dAf. rewrite dAtablef_eq.
  apply natlook_dAtable. exact H.
Qed.

Definition gluedf (m : nat) : list (list nat * list nat) :=
  filter (fun p => if list_eq_dec Nat.eq_dec
                       (locell m (snd p)) (pinv (locell m (fst p)))
                   then true else false)
         (list_prod (dominoesf m m) (dominoesf m m)).

Lemma gluedf_eq : forall m, gluedf m = glued m.
Proof. intro m. unfold gluedf, glued. rewrite dominoesf_eq. reflexivity. Qed.

Definition pqd_pairsf (m : nat) : list (nat * nat) :=
  map (fun b => (Pstat b, Pstat (pinv b))) (gen132f m).

Lemma pqd_pairsf_eq : forall m, pqd_pairsf m = pqd_pairs m.
Proof.
  intro m. unfold pqd_pairsf, pqd_pairs. rewrite gen132f_eq. reflexivity.
Qed.

Definition diag_pairsf (m : nat) : list (nat * nat) :=
  let t := dAtablef m m in
  map (fun b => (natlook t b, natlook t (pinv b))) (gen132f m).

Lemma diag_pairsf_eq : forall m, diag_pairsf m = diag_pairs m.
Proof.
  intro m. unfold diag_pairsf, diag_pairs. cbv zeta.
  rewrite dAtablef_eq, gen132f_eq. apply map_ext_in. intros b Hb.
  rewrite (natlook_dAtable m m b Hb).
  rewrite (natlook_dAtable m m (pinv b));
    [reflexivity | apply (Permutation_in _ (pinv_gen132 m)); apply in_map;
     exact Hb].
Qed.

Definition invfibref (m k : nat) : list (list nat) :=
  filter (fun b => if Nat.eq_dec (invcount b) k then true else false)
         (gen132f m).

Lemma invfibref_eq : forall m k, invfibref m k = invfibre m k.
Proof.
  intros m k. unfold invfibref, invfibre. rewrite gen132f_eq. reflexivity.
Qed.

Definition invkeysf (m : nat) : list nat :=
  nodup Nat.eq_dec (map invcount (gen132f m)).

Lemma invkeysf_eq : forall m, invkeysf m = invkeys m.
Proof.
  intro m. unfold invkeysf, invkeys. rewrite gen132f_eq. reflexivity.
Qed.

Definition stratum_off (F : list nat -> Z) (m k : nat) : stratum :=
  mkStratum (length (invfibref m k))
            (csum (map F (invfibref m k)))
            (csum (map (fun b => (F b * F (pinv b))%Z) (invfibref m k))).

Definition strata_off (F : list nat -> Z) (m : nat) : list stratum :=
  map (stratum_off F m) (invkeysf m).

Lemma strata_off_eq : forall F m, strata_off F m = strata_of F m.
Proof.
  intros F m. unfold strata_off, strata_of, stratum_off, stratum_of.
  rewrite invkeysf_eq. apply map_ext. intro k.
  rewrite invfibref_eq. reflexivity.
Qed.

Definition dstrataf (m : nat) : list stratum :=
  let t := dAtablef m m in strata_off (dAlook t) m.

Lemma dstrataf_eq : forall m, dstrataf m = dstrata m.
Proof.
  intro m. unfold dstrataf, dstrata. cbv zeta.
  rewrite dAtablef_eq, strata_off_eq. reflexivity.
Qed.

Definition Tstraightf (m : nat) : Z :=
  let t := dAtablef m m in
  fold_right (fun b acc => (Z.of_nat (natlook t b) * Z.of_nat (natlook t b)
                            + acc)%Z)
             0%Z (gen132f m).

(* ------------------------------------------------------------------ *)
(* The diagonal as a sum over Av(132).  gen_extend factors the enumerator at
   level M + d through the level-M one, and a legal extension only ever bumps
   the prefix, so the 132-freeness test reads the same on an extension as on
   the word it came from.  D(d,M) is therefore the number of legal d-letter
   extensions of a 132-avoider of length M, summed over Av(132)_M, and the same
   holds fibre by fibre, which is the form two_term_law_of_fibres consumes. *)

Lemma filter_none_gen : forall (A : Type) (P : A -> bool) (l : list A),
  (forall x, In x l -> P x = false) -> filter P l = nil.
Proof.
  intros A P. induction l as [|a l IH]; intro H; cbn [filter]; [reflexivity|].
  rewrite (H a (or_introl eq_refl)). apply IH.
  intros x Hx. apply H. right. exact Hx.
Qed.

Lemma nfold_filter : forall (A : Type) (P : A -> bool) (g : A -> nat)
    (l : list A),
  fold_right (fun x acc => ((if P x then g x else 0) + acc)%nat) 0%nat l
  = fold_right (fun x acc => (g x + acc)%nat) 0%nat (filter P l).
Proof.
  intros A P g. induction l as [|a l IH]; cbn [fold_right filter]; [reflexivity|].
  destruct (P a); cbn [fold_right]; rewrite IH; lia.
Qed.

Lemma avoids132b_map_bump : forall y l,
  avoids132b (map (bump y) l) = avoids132b l.
Proof.
  intros y l. unfold avoids132b.
  destruct (contains_132_dec (map (bump y) l)) as [H|H];
  destruct (contains_132_dec l) as [H2|H2]; try reflexivity.
  - exfalso. apply H2. apply (contains_132_map y l). exact H.
  - exfalso. apply H. apply (contains_132_map y l). exact H2.
Qed.

Lemma firstn_ext_le : forall M v y, (M <= length v)%nat ->
  firstn M (ext v y) = map (bump y) (firstn M v).
Proof.
  intros M v y H. unfold ext.
  rewrite firstn_app_le by (rewrite len_map; exact H).
  apply firstn_map_nat.
Qed.

Lemma extend_len : forall m k u w, In w (extend u m k) ->
  length w = (length u + k)%nat.
Proof.
  intros m k. induction k as [|k IH]; intros u w H.
  - cbn [extend] in H. destruct H as [<- | []]. lia.
  - cbn [extend] in H. apply in_flat_map in H. destruct H as [v [Hv Hw]].
    apply in_map_iff in Hw. destruct Hw as [y [Hy _]]. subst w.
    rewrite ext_length, (IH u v Hv). lia.
Qed.

Lemma avoids132b_extend : forall M d u w, length u = M ->
  In w (extend u M d) -> avoids132b (firstn M w) = avoids132b u.
Proof.
  intros M d. induction d as [|d IH]; intros u w HL H.
  - cbn [extend] in H. destruct H as [<- | []].
    rewrite <- HL, firstn_all. reflexivity.
  - cbn [extend] in H. apply in_flat_map in H. destruct H as [v [Hv Hw]].
    apply in_map_iff in Hw. destruct Hw as [y [Hy _]]. subst w.
    assert (Hlv : length v = (M + d)%nat)
      by (rewrite (extend_len M d u v Hv), HL; reflexivity).
    rewrite (firstn_ext_le M v y ltac:(lia)), avoids132b_map_bump.
    exact (IH u v HL Hv).
Qed.

Lemma filter_extend : forall M d u, length u = M ->
  filter (fun w => avoids132b (firstn M w)) (extend u M d)
  = (if avoids132b u then extend u M d else nil).
Proof.
  intros M d u HL. destruct (avoids132b u) eqn:E.
  - apply filter_all_gen. intros w Hw.
    rewrite (avoids132b_extend M d u w HL Hw). exact E.
  - apply filter_none_gen. intros w Hw.
    rewrite (avoids132b_extend M d u w HL Hw). exact E.
Qed.

(* D(d,M) is the number of legal d-letter extensions of a 132-avoider,
   summed over Av(132)_M. *)
Theorem Ddiag_extend : forall d M,
  Ddiag d M
  = fold_right (fun u acc => (length (extend u M d) + acc)%nat) 0%nat
               (gen132 M).
Proof.
  intros d M. unfold Ddiag.
  rewrite gen_extend, filter_flat_map, length_flat_map_gen.
  assert (Key : forall u, In u (gen M) ->
    length (filter (fun w => avoids132b (firstn M w)) (extend u M d))
    = (if avoids132b u then length (extend u M d) else 0)%nat).
  { intros u Hu. assert (HL : length u = M) by av.
    rewrite (filter_extend M d u HL). destruct (avoids132b u); reflexivity. }
  rewrite (nfold_ext_in (list nat)
             (fun u => length (filter (fun w => avoids132b (firstn M w))
                                      (extend u M d)))
             (fun u => if avoids132b u then length (extend u M d) else 0%nat)
             (gen M) Key).
  rewrite (nfold_filter (list nat) (fun u => avoids132b u)
                        (fun u => length (extend u M d)) (gen M)).
  apply nfold_perm. apply filter_gen_gen132.
Qed.

(* and the same at each suffix pattern *)
Theorem Nsig_extend : forall d M sg,
  Nsig d M sg
  = fold_right (fun u acc =>
      (length (filter (fun w => if list_eq_dec Nat.eq_dec (suffix_pat d w) sg
                                then true else false) (extend u M d)) + acc)%nat)
      0%nat (gen132 M).
Proof.
  intros d M sg. unfold Nsig.
  rewrite <- (filter_filter (list nat) (fun w => avoids132b (firstn M w))
                (fun w => if list_eq_dec Nat.eq_dec (suffix_pat d w) sg
                          then true else false) (gen (M + d))).
  rewrite gen_extend, filter_flat_map, filter_flat_map, length_flat_map_gen.
  assert (Key : forall u, In u (gen M) ->
    length (filter (fun w => if list_eq_dec Nat.eq_dec (suffix_pat d w) sg
                             then true else false)
              (filter (fun w => avoids132b (firstn M w)) (extend u M d)))
    = (if avoids132b u
       then length (filter (fun w => if list_eq_dec Nat.eq_dec (suffix_pat d w) sg
                                     then true else false) (extend u M d))
       else 0)%nat).
  { intros u Hu. assert (HL : length u = M) by av.
    rewrite (filter_extend M d u HL). destruct (avoids132b u); reflexivity. }
  rewrite (nfold_ext_in (list nat) _
             (fun u => if avoids132b u
                       then length (filter
                              (fun w => if list_eq_dec Nat.eq_dec
                                             (suffix_pat d w) sg
                                        then true else false) (extend u M d))
                       else 0%nat)
             (gen M) Key).
  rewrite (nfold_filter (list nat) (fun u => avoids132b u)
             (fun u => length (filter
                        (fun w => if list_eq_dec Nat.eq_dec (suffix_pat d w) sg
                                  then true else false) (extend u M d)))
             (gen M)).
  apply nfold_perm. apply filter_gen_gen132.
Qed.

(* At d = 1 the extension count is M + 1 at every 132-avoider, which is
   Ddiag_one read through the reduction. *)
Lemma extend_one_len : forall M u, In u (gen132 M) ->
  length (extend u M 1) = S M.
Proof.
  intros M u Hu.
  assert (H132 : ~ contains_132 u) by av.
  cbn [extend flat_map]. rewrite app_nil_r, Nat.add_0_r, len_map.
  rewrite (filter_all_gen nat (legalb u) (seq 0 (S M)));
    [apply length_seq | intros y _; apply legalb_of_avoids132; exact H132].
Qed.

Corollary Ddiag_extend_one : forall M, Ddiag 1 M = (S M * card132 M)%nat.
Proof.
  intro M. rewrite (Ddiag_extend 1 M).
  rewrite (nfold_ext_in (list nat) (fun u => length (extend u M 1))
             (fun _ => S M) (gen132 M) (extend_one_len M)).
  unfold card132. induction (gen132 M) as [|a l IH]; cbn [fold_right length];
    [lia | rewrite IH; lia].
Qed.

(* One column of the extension count is one mu-step, so the diagonal is a
   d-step transfer over mu rather than an enumeration. *)

Lemma extend_in_gen : forall m k u w, In u (gen m) -> In w (extend u m k) ->
  In w (gen (m + k)).
Proof.
  intros m k u w Hu Hw. rewrite (gen_extend k m). apply in_flat_map.
  exists u. split; [exact Hu | exact Hw].
Qed.

Theorem extend_succ_len : forall u m k, In u (gen m) ->
  length (extend u m (S k))
  = fold_right (fun w acc => (mucount w (m + k) + acc)%nat) 0%nat
               (extend u m k).
Proof.
  intros u m k Hu. cbn [extend]. rewrite length_flat_map_gen.
  apply nfold_ext_in. intros w Hw. rewrite len_map.
  assert (Hg : In w (gen (m + k))) by (apply (extend_in_gen m k u w Hu Hw)).
  assert (Hav : ~ contains_1324 w) by av.
  unfold mucount. destruct (mub w) as [dd|] eqn:E.
  - apply (fibre_count w (m + k) dd Hav). apply mub_is_mu. exact E.
  - apply fibre_count_free. apply mub_none_132free. exact E.
Qed.

Lemma extend_one_eq : forall M u, In u (gen132 M) ->
  extend u M 1 = map (ext u) (seq 0 (S M)).
Proof.
  intros M u Hu. assert (H132 : ~ contains_132 u) by av.
  cbn [extend flat_map]. rewrite app_nil_r, Nat.add_0_r.
  rewrite (filter_all_gen nat (legalb u) (seq 0 (S M)));
    [reflexivity | intros y _; apply legalb_of_avoids132; exact H132].
Qed.

Lemma nfold_map_gen : forall (A B : Type) (g : B -> nat) (f : A -> B)
    (l : list A),
  fold_right (fun x acc => (g x + acc)%nat) 0%nat (map f l)
  = fold_right (fun x acc => (g (f x) + acc)%nat) 0%nat l.
Proof.
  intros A B g f. induction l as [|a l IH]; cbn [map fold_right];
    [reflexivity | rewrite IH; reflexivity].
Qed.

Corollary Ddiag_two_mu : forall M,
  Ddiag 2 M
  = fold_right (fun u acc =>
      (fold_right (fun y acc' => (mucount (ext u y) (S M) + acc')%nat) 0%nat
                  (seq 0 (S M)) + acc)%nat)
      0%nat (gen132 M).
Proof.
  intro M. rewrite (Ddiag_extend 2 M). apply nfold_ext_in. intros u Hu.
  assert (Hg : In u (gen M)) by (apply gen132_incl; exact Hu).
  rewrite (extend_succ_len u M 1 Hg), (extend_one_eq M u Hu).
  rewrite (nfold_map_gen nat (list nat) (fun w => mucount w (M + 1)) (ext u)
                         (seq 0 (S M))).
  apply nfold_ext_in. intros y _.
  assert (E : (M + 1)%nat = S M) by lia. rewrite E. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The d = 2 state.  Appending y to a 132-free word creates exactly those 132
   occurrences whose '3' is a value at or above y sitting after the first value
   below y, so mu after the append is one more than the least such value.
   H u M y is that value capped at M, and it carries the whole d = 2 transfer. *)

Fixpoint firstlt (u : list nat) (y : nat) : nat :=
  match u with
  | nil => O
  | x :: r => if Nat.ltb x y then O else S (firstlt r y)
  end.

Lemma firstlt_le : forall u y, (firstlt u y <= length u)%nat.
Proof.
  induction u as [|x r IH]; intro y; cbn [firstlt length]; [lia|].
  destruct (Nat.ltb x y); [lia | assert (H := IH y); lia].
Qed.

Lemma firstlt_none : forall u y i, (i < firstlt u y)%nat ->
  ~ (nth i u 0%nat < y)%nat.
Proof.
  induction u as [|x r IH]; intros y i H; cbn [firstlt] in H; [lia|].
  destruct (Nat.ltb_spec x y) as [E|E]; [lia|].
  destruct i as [|i]; cbn [nth]; [lia | apply IH; lia].
Qed.

Lemma firstlt_hit : forall u y, (firstlt u y < length u)%nat ->
  (nth (firstlt u y) u 0%nat < y)%nat.
Proof.
  induction u as [|x r IH]; intros y H; cbn [firstlt length] in *; [lia|].
  destruct (Nat.ltb_spec x y) as [E|E]; cbn [nth]; [exact E|].
  apply IH. lia.
Qed.

Lemma firstlt_min : forall u y i,
  (i < length u)%nat -> (nth i u 0%nat < y)%nat -> (firstlt u y <= i)%nat.
Proof.
  intros u y i H1 H2.
  destruct (Nat.le_gt_cases (firstlt u y) i) as [K|K]; [exact K|].
  exfalso. exact (firstlt_none u y i K H2).
Qed.

Lemma in_skipn_nth : forall (u : list nat) k w,
  In w (skipn k u)
  <-> exists j, (k <= j)%nat /\ (j < length u)%nat /\ nth j u 0%nat = w.
Proof.
  induction u as [|x r IH]; intros k w.
  - rewrite skipn_nil. cbn [In length]. split;
      [contradiction | intros [j [_ [H _]]]; lia].
  - destruct k as [|k]; cbn [skipn].
    + cbn [In length]. split.
      * intros [He | H].
        -- exists 0%nat. cbn [nth]. split; [lia | split; [lia | exact He]].
        -- apply (IH 0%nat w) in H. destruct H as [j [_ [Hj Hn]]].
           exists (S j). cbn [nth]. split; [lia | split; [lia | exact Hn]].
      * intros [j [_ [Hj Hn]]]. destruct j as [|j]; cbn [nth] in Hn.
        -- left. exact Hn.
        -- right. apply (IH 0%nat w). exists j. cbn [length] in Hj.
           split; [lia | split; [lia | exact Hn]].
    + rewrite (IH k w). split.
      * intros [j [H1 [H2 H3]]]. exists (S j). cbn [length nth].
        split; [lia | split; [lia | exact H3]].
      * intros [j [H1 [H2 H3]]]. destruct j as [|j]; [lia|].
        cbn [nth] in H3. cbn [length] in H2.
        exists j. split; [lia | split; [lia | exact H3]].
Qed.

Definition hvals (u : list nat) (y : nat) : list nat :=
  filter (fun w => Nat.leb y w) (skipn (S (firstlt u y)) u).

Lemma in_hvals : forall u y w,
  In w (hvals u y)
  <-> (exists i j, (i < j)%nat /\ (j < length u)%nat /\
        (nth i u 0%nat < y)%nat /\ (y <= nth j u 0%nat)%nat /\
        nth j u 0%nat = w).
Proof.
  intros u y w. unfold hvals. rewrite filter_In, in_skipn_nth. split.
  - intros [[j [H1 [H2 H3]]] Hb]. apply Nat.leb_le in Hb.
    assert (Hf : (firstlt u y < length u)%nat) by lia.
    assert (Hhit : (nth (firstlt u y) u 0%nat < y)%nat)
      by (apply firstlt_hit; exact Hf).
    exists (firstlt u y), j. repeat split; lia.
  - intros [i [j [Hij [Hj [Hi [Hyj Hn]]]]]].
    assert (Hf : (firstlt u y <= i)%nat) by (apply firstlt_min; [lia | exact Hi]).
    split.
    + exists j. split; [lia | split; [exact Hj | exact Hn]].
    + apply Nat.leb_le. rewrite Hn in Hyj. exact Hyj.
Qed.

Theorem three_value_ext : forall u y w, ~ contains_132 u ->
  (three_value (ext u y) w <-> exists v, In v (hvals u y) /\ w = S v).
Proof.
  intros u y w Hu. unfold ext.
  rewrite (three_values_append (map (bump y) u) y w).
  assert (Hnf : forall z, ~ three_value (map (bump y) u) z).
  { apply profile_empty_iff. intro C. apply Hu.
    apply (contains_132_map y u). exact C. }
  split.
  - intros [K | [j [Hc Hw]]]; [exfalso; exact (Hnf w K)|].
    destruct Hc as [Hj [Hyj [i [Hij Hi]]]]. rewrite len_map in Hj.
    rewrite (nth_map_in (bump y) u j Hj) in Hyj, Hw.
    rewrite (nth_map_in (bump y) u i ltac:(lia)) in Hi.
    apply (bump_gt_v y (nth j u 0%nat)) in Hyj.
    apply (bump_lt_v y (nth i u 0%nat)) in Hi.
    exists (nth j u 0%nat). split.
    + apply in_hvals. exists i, j. repeat split; lia.
    + rewrite <- Hw. unfold bump.
      destruct (Nat.leb_spec y (nth j u 0%nat)); [reflexivity | lia].
  - intros [v [Hv Hw]]. right.
    apply in_hvals in Hv. destruct Hv as [i [j [Hij [Hj [Hi [Hyj Hn]]]]]].
    exists j. split.
    + unfold candidate_strict. rewrite len_map.
      rewrite (nth_map_in (bump y) u j Hj).
      split; [exact Hj | split].
      * apply (bump_gt_v y (nth j u 0%nat)). exact Hyj.
      * exists i. rewrite (nth_map_in (bump y) u i ltac:(lia)).
        split; [exact Hij | apply (bump_lt_v y (nth i u 0%nat)); exact Hi].
    + rewrite (nth_map_in (bump y) u j Hj), Hn, Hw. unfold bump.
      destruct (Nat.leb_spec y v); [reflexivity | lia].
Qed.

Definition Hu (u : list nat) (M y : nat) : nat :=
  fold_right Nat.min M (hvals u y).

Lemma foldmin_char : forall l c v0, In v0 l ->
  (forall v, In v l -> (v0 <= v)%nat) ->
  fold_right Nat.min c l = Nat.min v0 c.
Proof.
  induction l as [|a l IH]; intros c v0 Hin Hle; [contradiction|].
  cbn [fold_right]. destruct l as [|b l].
  - cbn [fold_right]. destruct Hin as [He | []]. subst a. reflexivity.
  - assert (Hex : exists v1, In v1 (b :: l) /\ forall v, In v (b :: l) -> (v1 <= v)%nat).
    { destruct (least_dec (fun z => In z (b :: l))
                  (fun z => in_dec Nat.eq_dec z (b :: l)) b
                  (or_introl eq_refl)) as [v1 [H1 H2]].
      exists v1. split; [exact H1 | exact H2]. }
    destruct Hex as [v1 [H1 H2]].
    rewrite (IH c v1 H1 H2).
    assert (Hv0 : (v0 <= a)%nat /\ (v0 <= v1)%nat)
      by (split; apply Hle; [left; reflexivity | right; exact H1]).
    destruct Hin as [He | Hin].
    + subst a. lia.
    + assert (K := H2 v0 Hin). lia.
Qed.

Lemma is_mu_unique : forall u d d', is_mu u d -> is_mu u d' -> d = d'.
Proof.
  intros u d d' [H1 H2] [H3 H4].
  assert (K1 := H2 d' H3). assert (K2 := H4 d H1). lia.
Qed.

Theorem mucount_ext : forall u M y, ~ contains_132 u -> length u = M ->
  mucount (ext u y) (S M) = S (S (Hu u M y)).
Proof.
  intros u M y Hu132 HL. unfold mucount, Hu.
  destruct (mub (ext u y)) as [d|] eqn:E.
  - assert (Hmu : is_mu (ext u y) d) by (apply mub_is_mu; exact E).
    assert (Hd := proj1 Hmu).
    apply (three_value_ext u y d Hu132) in Hd.
    destruct Hd as [v0 [Hv0 Hdv]].
    assert (Hmin : forall v, In v (hvals u y) -> (v0 <= v)%nat).
    { intros v Hv.
      assert (Hsv : three_value (ext u y) (S v)).
      { apply (three_value_ext u y (S v) Hu132). exists v. split;
          [exact Hv | reflexivity]. }
      assert (K := proj2 Hmu (S v) Hsv). lia. }
    rewrite (foldmin_char (hvals u y) M v0 Hv0 Hmin). lia.
  - assert (Hnf : ~ contains_132 (ext u y))
      by (apply mub_none_132free; exact E).
    assert (He : hvals u y = nil).
    { destruct (hvals u y) as [|v l] eqn:Ev; [reflexivity|].
      exfalso.
      assert (Hno := proj1 (profile_empty_iff (ext u y)) Hnf).
      apply (Hno (S v)).
      apply (three_value_ext u y (S v) Hu132). exists v.
      split; [rewrite Ev; left; reflexivity | reflexivity]. }
    rewrite He. cbn [fold_right]. lia.
Qed.

Theorem Ddiag_two_H : forall M,
  Ddiag 2 M
  = fold_right (fun u acc =>
      (fold_right (fun y acc' => (S (S (Hu u M y)) + acc')%nat) 0%nat
                  (seq 0 (S M)) + acc)%nat) 0%nat (gen132 M).
Proof.
  intro M. rewrite (Ddiag_two_mu M). apply nfold_ext_in. intros u Hu.
  assert (H132 : ~ contains_132 u) by av.
  assert (HL : length u = M) by av.
  apply nfold_ext_in. intros y _. apply mucount_ext; assumption.
Qed.

Lemma Tstraightf_eq : forall m, Tstraightf m = Z.of_nat (Tstraight m).
Proof.
  intro m. unfold Tstraightf, Tstraight. cbv zeta.
  rewrite dAtablef_eq, gen132f_eq.
  rewrite (foldZ_of_nat (natlook (dAtable m m)) (natlook (dAtable m m))
             (gen132 m)).
  f_equal. apply nfold_ext_in. intros b Hb.
  rewrite (natlook_dAtable m m b Hb). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Linear independence of C(2M,M) and 4^M over the polynomials.

   The central binomial square sits between 16^M/(4M+1) and 16^M/(3M+1), both
   by induction on the ratio (M+1) C(2M+2,M+1) = (4M+2) C(2M,M).  A vanishing
   combination p(M) C(2M,M) + q(M) 4^M = 0 therefore forces

       (3M+1) q(M)^2  <=  p(M)^2  <=  (4M+1) q(M)^2

   at every M.  A polynomial of degree f is bounded above by a multiple of M^f
   everywhere and below by a multiple of M^f past a threshold, so those two
   bounds place the degree of p strictly between the degree of q and one more
   than it.  Hence both polynomials vanish, and the pair of coefficient lists a
   Diagonal carries is determined by the diagonal it describes. *)

Require Import Lqa.

Lemma nat_cancel_le : forall k a b,
  (0 < k)%nat -> (k * a <= k * b)%nat -> (a <= b)%nat.
Proof.
  intros k a b Hk H.
  destruct (Nat.le_gt_cases a b) as [K|K]; [exact K|].
  exfalso. assert (k * b < k * a)%nat by nia. lia.
Qed.

Lemma nat_pow_ge1 : forall M n, (1 <= M)%nat -> (1 <= M ^ n)%nat.
Proof. intros M n H. induction n as [|n IH]; cbn [Nat.pow]; nia. Qed.

Lemma pow16 : forall M, (16 ^ M = 4 ^ M * 4 ^ M)%nat.
Proof.
  induction M as [|M IH]; [reflexivity|].
  cbn [Nat.pow]. rewrite IH. ring.
Qed.

Lemma binomN_pos : forall n k, (k <= n)%nat -> (1 <= binomN n k)%nat.
Proof.
  induction n as [|n IH]; intros k Hk.
  - assert (E : k = 0%nat) by lia. subst k. reflexivity.
  - destruct k as [|k]; [rewrite binomN_0; lia|].
    change (binomN (S n) (S k)) with (binomN n k + binomN n (S k))%nat.
    assert (H1 := IH k ltac:(lia)). lia.
Qed.

Lemma cb_ratio : forall M,
  (S M * binomN (2 * S M) (S M) = (4 * M + 2) * binomN (2 * M) M)%nat.
Proof.
  intro M. replace (2 * S M)%nat with (2 * M + 2)%nat by lia.
  assert (K := binomN_central M). lia.
Qed.

Lemma cb_upper : forall M,
  ((3 * M + 1) * (binomN (2 * M) M * binomN (2 * M) M) <= 16 ^ M)%nat.
Proof.
  induction M as [|M IH]; [cbn; lia|].
  assert (Hc := cb_ratio M).
  remember (binomN (2 * M) M) as C eqn:HC.
  remember (binomN (2 * S M) (S M)) as D eqn:HD.
  assert (Hsq : ((M + 1) * (M + 1) * (D * D)
                 = (4 * M + 2) * (4 * M + 2) * (C * C))%nat) by nia.
  apply (nat_cancel_le ((3 * M + 1) * ((M + 1) * (M + 1)))); [nia|].
  replace ((3 * M + 1) * ((M + 1) * (M + 1)) * ((3 * S M + 1) * (D * D)))%nat
    with (((3 * M + 4) * (3 * M + 1)) * ((M + 1) * (M + 1) * (D * D)))%nat
    by ring.
  rewrite Hsq.
  replace (16 ^ S M)%nat with (16 * 16 ^ M)%nat by (cbn [Nat.pow]; ring).
  transitivity (((3 * M + 4) * ((4 * M + 2) * (4 * M + 2))) * 16 ^ M)%nat.
  - replace ((3 * M + 4) * (3 * M + 1)
             * ((4 * M + 2) * (4 * M + 2) * (C * C)))%nat
      with (((3 * M + 4) * ((4 * M + 2) * (4 * M + 2)))
            * ((3 * M + 1) * (C * C)))%nat by ring.
    apply Nat.mul_le_mono_l. exact IH.
  - replace ((3 * M + 1) * ((M + 1) * (M + 1)) * (16 * 16 ^ M))%nat
      with ((16 * ((3 * M + 1) * ((M + 1) * (M + 1)))) * 16 ^ M)%nat by ring.
    apply Nat.mul_le_mono_r.
    replace ((3 * M + 4) * ((4 * M + 2) * (4 * M + 2)))%nat
      with (48 * (M * M * M) + 112 * (M * M) + 76 * M + 16)%nat by ring.
    replace (16 * ((3 * M + 1) * ((M + 1) * (M + 1))))%nat
      with (48 * (M * M * M) + 112 * (M * M) + 80 * M + 16)%nat by ring.
    lia.
Qed.

Lemma cb_lower : forall M,
  (16 ^ M <= (4 * M + 1) * (binomN (2 * M) M * binomN (2 * M) M))%nat.
Proof.
  induction M as [|M IH]; [cbn; lia|].
  assert (Hc := cb_ratio M).
  remember (binomN (2 * M) M) as C eqn:HC.
  remember (binomN (2 * S M) (S M)) as D eqn:HD.
  assert (Hsq : ((M + 1) * (M + 1) * (D * D)
                 = (4 * M + 2) * (4 * M + 2) * (C * C))%nat) by nia.
  apply (nat_cancel_le ((M + 1) * (M + 1))); [nia|].
  replace ((M + 1) * (M + 1) * 16 ^ S M)%nat
    with ((16 * ((M + 1) * (M + 1))) * 16 ^ M)%nat
    by (cbn [Nat.pow]; ring).
  transitivity ((16 * ((M + 1) * (M + 1))) * ((4 * M + 1) * (C * C)))%nat.
  - apply Nat.mul_le_mono_l. exact IH.
  - replace ((M + 1) * (M + 1) * ((4 * S M + 1) * (D * D)))%nat
      with ((4 * M + 5) * ((M + 1) * (M + 1) * (D * D)))%nat by ring.
    rewrite Hsq.
    replace (16 * ((M + 1) * (M + 1)) * ((4 * M + 1) * (C * C)))%nat
      with ((16 * ((M + 1) * (M + 1)) * (4 * M + 1)) * (C * C))%nat by ring.
    replace ((4 * M + 5) * ((4 * M + 2) * (4 * M + 2) * (C * C)))%nat
      with (((4 * M + 5) * ((4 * M + 2) * (4 * M + 2))) * (C * C))%nat by ring.
    apply Nat.mul_le_mono_r.
    replace (16 * ((M + 1) * (M + 1)) * (4 * M + 1))%nat
      with (64 * (M * M * M) + 144 * (M * M) + 96 * M + 16)%nat by ring.
    replace ((4 * M + 5) * ((4 * M + 2) * (4 * M + 2)))%nat
      with (64 * (M * M * M) + 144 * (M * M) + 96 * M + 20)%nat by ring.
    lia.
Qed.

(* Rational scaffolding: absolute values, the archimedean step and the two
   cancellation rules the estimates run on. *)

Lemma Qabs_zero : forall x, Qabs x == 0 -> x == 0.
Proof.
  intros [n d] H. unfold Qabs, Qeq in *. cbn in *. lia.
Qed.

Lemma Qabs_pos_of_ne : forall x, ~ (x == 0) -> Qlt 0 (Qabs x).
Proof.
  intros x H. destruct (Qlt_le_dec 0 (Qabs x)) as [K|K]; [exact K|].
  exfalso. apply H. apply Qabs_zero.
  apply Qle_antisym; [exact K | apply Qabs_nonneg].
Qed.

Lemma Qsq_abs : forall x, Qmult x x == Qmult (Qabs x) (Qabs x).
Proof.
  intro x. rewrite <- Qabs_Qmult. symmetry. apply Qabs_pos. nra.
Qed.

Lemma Qabs_rev : forall x y, Qle (Qabs y) (Qplus (Qabs (Qplus x y)) (Qabs x)).
Proof.
  intros x y.
  assert (E : y == Qplus (Qplus x y) (Qopp x)) by ring.
  rewrite E at 1.
  eapply Qle_trans; [apply Qabs_triangle|].
  rewrite Qabs_opp. apply Qle_refl.
Qed.

Lemma Qcancel_le_r : forall x y t,
  Qlt 0 t -> Qle (Qmult x t) (Qmult y t) -> Qle x y.
Proof.
  intros x y t Ht H.
  destruct (Qlt_le_dec y x) as [K|K]; [exfalso | exact K]. nra.
Qed.

Lemma Qmul_le_r : forall x y z, Qle x y -> Qle 0 z -> Qle (Qmult x z) (Qmult y z).
Proof. intros x y z H Hz. nra. Qed.

Lemma Qmul_le_l : forall x y z, Qle x y -> Qle 0 z -> Qle (Qmult z x) (Qmult z y).
Proof. intros x y z H Hz. nra. Qed.

Lemma Zof_to_nat_ge : forall z : Z, (z <= Z.of_nat (Z.to_nat z))%Z.
Proof.
  intro z. destruct (Z.le_gt_cases 0 z) as [H|H].
  - rewrite (Z2Nat.id z H). apply Z.le_refl.
  - destruct z; [lia | lia | cbn; lia].
Qed.

Lemma Qn_above : forall q : Q, exists n : nat, Qle q (Qn n).
Proof.
  intro q. exists (Z.to_nat (Qnum q)).
  unfold Qn, Qle, inject_Z. cbn [Qnum Qden].
  assert (H := Zof_to_nat_ge (Qnum q)).
  assert (Ht : (0 <= Z.of_nat (Z.to_nat (Qnum q)))%Z) by lia.
  assert (Hd : (1 <= Z.pos (Qden q))%Z) by lia.
  nia.
Qed.

Lemma Qn_nonneg : forall n : nat, Qle 0 (Qn n).
Proof. intro n. rewrite <- Qn_0. apply Qn_le. lia. Qed.

Lemma Qn3 : Qn 3 == 3.
Proof. unfold Qn, Qeq. simpl. lia. Qed.

Lemma Qn4 : Qn 4 == 4.
Proof. unfold Qn, Qeq. simpl. lia. Qed.

Lemma Qn_lin : forall k M c,
  Qn (k * M + c)%nat == Qplus (Qmult (Qn k) (Qn M)) (Qn c).
Proof. intros k M c. rewrite Qn_add, Qn_mul. reflexivity. Qed.

Lemma no_linear_bound : forall alpha beta M0,
  Qlt 0 alpha ->
  (forall M : nat, (M0 <= M)%nat -> Qle (Qmult alpha (Qn M)) beta) -> False.
Proof.
  intros alpha beta M0 Ha H.
  destruct (Qn_above (Qdiv beta alpha)) as [M1 HM1].
  assert (HM := H (M0 + M1 + 1)%nat ltac:(lia)).
  assert (Hge : Qle (Qplus (Qn M1) 1) (Qn (M0 + M1 + 1)%nat)).
  { assert (E : Qn (M1 + 1)%nat == Qplus (Qn M1) 1)
      by (rewrite Qn_add, Qn_1; reflexivity).
    rewrite <- E. apply Qn_le. lia. }
  assert (Hb : Qmult alpha (Qdiv beta alpha) == beta).
  { field. intro C. rewrite C in Ha. exact (Qlt_irrefl 0 Ha). }
  nra.
Qed.

(* Polynomial size.  sumabs bounds a polynomial above by a multiple of M^deg,
   and past an explicit threshold the leading term bounds it below. *)

Fixpoint sumabs (c : list Q) : Q :=
  match c with nil => 0 | u :: r => Qplus (Qabs u) (sumabs r) end.

Lemma sumabs_nonneg : forall c, Qle 0 (sumabs c).
Proof.
  induction c as [|u c IH]; cbn [sumabs]; [apply Qle_refl|].
  assert (H := Qabs_nonneg u). nra.
Qed.

Lemma polyQ_upper : forall c M, (1 <= M)%nat ->
  Qle (Qabs (polyQ c (Qn M))) (Qmult (sumabs c) (Qn (M ^ pred (length c)))).
Proof.
  intros c M HM.
  assert (HQM : Qle 0 (Qn M)) by apply Qn_nonneg.
  induction c as [|u c IH].
  - cbn [polyQ sumabs length pred].
    replace (M ^ 0)%nat with 1%nat by reflexivity. rewrite Qn_1.
    setoid_replace (Qabs 0) with (0%Q) by reflexivity. nra.
  - destruct c as [|v c'].
    + cbn [polyQ sumabs length pred].
      replace (M ^ 0)%nat with 1%nat by reflexivity. rewrite Qn_1.
      setoid_replace (Qplus u (Qmult (Qn M) 0)) with u by ring.
      assert (H := Qabs_nonneg u). nra.
    + cbn [length pred] in *.
      assert (HP : Qle (Qabs (polyQ (v :: c') (Qn M)))
                       (Qmult (sumabs (v :: c')) (Qn (M ^ length c'))))
        by exact IH.
      assert (Eg : polyQ (u :: v :: c') (Qn M)
                   == Qplus u (Qmult (Qn M) (polyQ (v :: c') (Qn M))))
        by reflexivity.
      assert (Es : sumabs (u :: v :: c')
                   == Qplus (Qabs u) (sumabs (v :: c'))) by reflexivity.
      rewrite Eg, Es.
      assert (T := Qabs_triangle u (Qmult (Qn M) (polyQ (v :: c') (Qn M)))).
      assert (Hm : Qabs (Qmult (Qn M) (polyQ (v :: c') (Qn M)))
                   == Qmult (Qn M) (Qabs (polyQ (v :: c') (Qn M))))
        by (rewrite Qabs_Qmult, (Qabs_pos (Qn M) HQM); reflexivity).
      rewrite Hm in T.
      assert (HQ : Qn (M ^ S (length c')) == Qmult (Qn M) (Qn (M ^ length c'))).
      { cbn [Nat.pow]. rewrite Qn_mul. reflexivity. }
      assert (Hge1 : Qle 1 (Qn (M ^ S (length c')))).
      { rewrite <- Qn_1. apply Qn_le. apply nat_pow_ge1. exact HM. }
      assert (Hu := Qabs_nonneg u).
      assert (Hs := sumabs_nonneg (v :: c')).
      assert (Hq := Qabs_nonneg (polyQ (v :: c') (Qn M))).
      rewrite HQ. nra.
Qed.

Lemma polyQ_upper_deg : forall c n M, (1 <= M)%nat ->
  (forall j, (n < j)%nat -> nth j c 0%Q == 0) ->
  Qle (Qabs (polyQ c (Qn M)))
      (Qmult (sumabs (firstn (S n) c)) (Qn (M ^ n))).
Proof.
  intros c n M HM Hz.
  assert (E : polyQ c (Qn M) == polyQ (firstn (S n) c) (Qn M)).
  { symmetry. apply polyQ_firstn. intros j Hj. apply Hz. lia. }
  rewrite E.
  assert (H := polyQ_upper (firstn (S n) c) M HM).
  assert (Hpow : Qle (Qn (M ^ pred (length (firstn (S n) c)))) (Qn (M ^ n))).
  { apply Qn_le. apply Nat.pow_le_mono_r; [lia|].
    rewrite length_firstn. lia. }
  assert (Hs := sumabs_nonneg (firstn (S n) c)).
  assert (Hq := Qabs_nonneg (polyQ (firstn (S n) c) (Qn M))).
  nra.
Qed.

Lemma polyQ_split_nat : forall n c M,
  (forall j, (n < j)%nat -> nth j c 0%Q == 0) ->
  polyQ c (Qn M) == Qplus (polyQ (firstn n c) (Qn M))
                          (Qmult (nth n c 0%Q) (Qn (M ^ n))).
Proof.
  induction n as [|n IH]; intros c M Hz.
  - destruct c as [|u r].
    + cbn [firstn polyQ nth]. replace (M ^ 0)%nat with 1%nat by reflexivity.
      rewrite Qn_1. ring.
    + assert (Hr : polyQ r (Qn M) == 0).
      { apply polyQ_zero_list. intro j. exact (Hz (S j) ltac:(lia)). }
      cbn [firstn polyQ nth]. replace (M ^ 0)%nat with 1%nat by reflexivity.
      rewrite Qn_1, Hr. ring.
  - destruct c as [|u r].
    + cbn [firstn polyQ nth]. ring.
    + assert (Hz' : forall j, (n < j)%nat -> nth j r 0%Q == 0)
        by (intros j Hj; exact (Hz (S j) ltac:(lia))).
      assert (IHr := IH r M Hz').
      assert (E : Qn (M ^ S n) == Qmult (Qn M) (Qn (M ^ n)))
        by (cbn [Nat.pow]; rewrite Qn_mul; reflexivity).
      cbn [firstn polyQ nth]. rewrite IHr, E. ring.
Qed.

Lemma polyQ_lower : forall c n,
  (forall j, (n < j)%nat -> nth j c 0%Q == 0) ->
  exists M0 : nat, (1 <= M0)%nat /\
    forall M, (M0 <= M)%nat ->
      Qle (Qmult (Qabs (nth n c 0%Q)) (Qn (M ^ n)))
          (Qmult 2 (Qabs (polyQ c (Qn M)))).
Proof.
  intros c n Hz.
  destruct (Qeq_dec (nth n c 0%Q) 0) as [HA|HA].
  { exists 1%nat. split; [lia|]. intros M HM.
    assert (E : Qabs (nth n c 0%Q) == 0) by (rewrite HA; reflexivity).
    rewrite E.
    assert (H := Qabs_nonneg (polyQ c (Qn M))). nra. }
  destruct n as [|n'].
  { exists 1%nat. split; [lia|]. intros M HM.
    assert (E := polyQ_split_nat 0 c M Hz).
    cbn [firstn polyQ] in E.
    replace (M ^ 0)%nat with 1%nat in E by reflexivity.
    rewrite Qn_1 in E.
    assert (E2 : polyQ c (Qn M) == nth 0 c 0%Q) by (rewrite E; ring).
    rewrite E2. replace (M ^ 0)%nat with 1%nat by reflexivity. rewrite Qn_1.
    assert (H := Qabs_nonneg (nth 0 c 0%Q)). nra. }
  assert (HK : Qle 0 (sumabs (firstn (S n') c))) by apply sumabs_nonneg.
  assert (HAp : Qlt 0 (Qabs (nth (S n') c 0%Q))) by (apply Qabs_pos_of_ne; exact HA).
  destruct (Qn_above (Qdiv (Qmult 2 (sumabs (firstn (S n') c)))
                           (Qabs (nth (S n') c 0%Q)))) as [M1 HM1].
  exists (Nat.max 1 M1). split; [lia|]. intros M HM.
  assert (HMge : (1 <= M)%nat) by lia.
  assert (HQM : Qle 0 (Qn M)) by apply Qn_nonneg.
  assert (Hstep : Qle (Qdiv (Qmult 2 (sumabs (firstn (S n') c)))
                            (Qabs (nth (S n') c 0%Q))) (Qn M)).
  { apply (Qle_trans _ (Qn M1)); [exact HM1 | apply Qn_le; lia]. }
  assert (Ht : Qmult (Qabs (nth (S n') c 0%Q))
                     (Qdiv (Qmult 2 (sumabs (firstn (S n') c)))
                           (Qabs (nth (S n') c 0%Q)))
               == Qmult 2 (sumabs (firstn (S n') c))).
  { field. intro C. rewrite C in HAp. exact (Qlt_irrefl 0 HAp). }
  assert (Hthr : Qle (Qmult 2 (sumabs (firstn (S n') c)))
                     (Qmult (Qabs (nth (S n') c 0%Q)) (Qn M))) by nra.
  assert (Esp := polyQ_split_nat (S n') c M Hz).
  assert (Hlow := polyQ_upper (firstn (S n') c) M HMge).
  assert (Hpow : Qle (Qn (M ^ pred (length (firstn (S n') c)))) (Qn (M ^ n'))).
  { apply Qn_le. apply Nat.pow_le_mono_r; [lia|].
    rewrite length_firstn. lia. }
  assert (Hlow2 : Qle (Qabs (polyQ (firstn (S n') c) (Qn M)))
                      (Qmult (sumabs (firstn (S n') c)) (Qn (M ^ n')))).
  { assert (Hq := Qabs_nonneg (polyQ (firstn (S n') c) (Qn M))). nra. }
  assert (Hrev := Qabs_rev (polyQ (firstn (S n') c) (Qn M))
                           (Qmult (nth (S n') c 0%Q) (Qn (M ^ S n')))).
  assert (Habs : Qabs (Qmult (nth (S n') c 0%Q) (Qn (M ^ S n')))
                 == Qmult (Qabs (nth (S n') c 0%Q)) (Qn (M ^ S n'))).
  { rewrite Qabs_Qmult, (Qabs_pos (Qn (M ^ S n')) (Qn_nonneg _)). reflexivity. }
  rewrite Habs, <- Esp in Hrev.
  assert (HE : Qn (M ^ S n') == Qmult (Qn M) (Qn (M ^ n')))
    by (cbn [Nat.pow]; rewrite Qn_mul; reflexivity).
  assert (HXn : Qle 0 (Qn (M ^ n'))) by apply Qn_nonneg.
  rewrite HE in Hrev |- *. nra.
Qed.

(* The index of the top nonzero coefficient. *)

Fixpoint nzlen (c : list Q) : nat :=
  match c with
  | nil => O
  | u :: r => match nzlen r with
              | O => if Qeq_dec u 0 then O else 1%nat
              | S k => S (S k)
              end
  end.

Lemma nzlen_cons : forall u c,
  nzlen (u :: c) = match nzlen c with
                   | O => if Qeq_dec u 0 then O else 1%nat
                   | S k => S (S k)
                   end.
Proof. intros u c. reflexivity. Qed.

Lemma nzlen_above : forall c j, (nzlen c <= j)%nat -> nth j c 0%Q == 0.
Proof.
  induction c as [|u c IH]; intros j Hj.
  - rewrite nth_nil. reflexivity.
  - rewrite nzlen_cons in Hj. destruct (nzlen c) as [|k] eqn:Ec.
    + destruct (Qeq_dec u 0) as [Hu|Hu].
      * destruct j as [|j']; [exact Hu | cbn [nth]; apply IH; lia].
      * destruct j as [|j']; [lia | cbn [nth]; apply IH; lia].
    + destruct j as [|j']; [lia | cbn [nth]; apply IH; lia].
Qed.

Lemma nzlen_top : forall c n, nzlen c = S n -> ~ (nth n c 0%Q == 0).
Proof.
  induction c as [|u c IH]; intros n Hn; [cbn in Hn; discriminate|].
  rewrite nzlen_cons in Hn. destruct (nzlen c) as [|k] eqn:Ec.
  - destruct (Qeq_dec u 0) as [Hu|Hu]; [discriminate|].
    injection Hn as Hn. subst n. cbn [nth]. exact Hu.
  - injection Hn as Hn. subst n. cbn [nth]. apply IH. reflexivity.
Qed.

Lemma nzlen_zero_poly : forall c x, nzlen c = 0%nat -> polyQ c x == 0.
Proof.
  intros c x H. apply polyQ_zero_list. intro j. apply nzlen_above. lia.
Qed.

(* The two-sided bound the vanishing combination forces. *)

Theorem two_term_sandwich : forall a b : list Q,
  (forall M : nat,
     Qplus (Qmult (polyQ a (Qn M)) (Qn (binomN (2 * M) M)))
           (Qmult (polyQ b (Qn M)) (Qn (4 ^ M))) == 0) ->
  forall M : nat,
    Qle (Qmult (Qn (3 * M + 1)%nat)
               (Qmult (polyQ b (Qn M)) (polyQ b (Qn M))))
        (Qmult (polyQ a (Qn M)) (polyQ a (Qn M)))
    /\ Qle (Qmult (polyQ a (Qn M)) (polyQ a (Qn M)))
           (Qmult (Qn (4 * M + 1)%nat)
                  (Qmult (polyQ b (Qn M)) (polyQ b (Qn M)))).
Proof.
  intros a b H M.
  assert (HM := H M).
  assert (HF : Qlt 0 (Qn (4 ^ M))) by (apply Qn_pos; apply four_pow_pos).
  assert (HFF : Qmult (Qn (4 ^ M)) (Qn (4 ^ M)) == Qn (16 ^ M)).
  { rewrite <- Qn_mul, <- pow16. reflexivity. }
  assert (HG : Qlt 0 (Qn (16 ^ M))) by (rewrite <- HFF; nra).
  assert (Kop : Qmult (polyQ a (Qn M)) (Qn (binomN (2 * M) M))
                == Qopp (Qmult (polyQ b (Qn M)) (Qn (4 ^ M)))).
  { setoid_replace (Qmult (polyQ a (Qn M)) (Qn (binomN (2 * M) M)))
      with (Qminus (Qplus (Qmult (polyQ a (Qn M)) (Qn (binomN (2 * M) M)))
                          (Qmult (polyQ b (Qn M)) (Qn (4 ^ M))))
                   (Qmult (polyQ b (Qn M)) (Qn (4 ^ M)))) by ring.
    rewrite HM. ring. }
  assert (Hsq : Qmult (Qmult (polyQ a (Qn M)) (polyQ a (Qn M)))
                      (Qmult (Qn (binomN (2 * M) M)) (Qn (binomN (2 * M) M)))
                == Qmult (Qmult (polyQ b (Qn M)) (polyQ b (Qn M)))
                         (Qn (16 ^ M))).
  { rewrite <- HFF.
    setoid_replace (Qmult (Qmult (polyQ a (Qn M)) (polyQ a (Qn M)))
                          (Qmult (Qn (binomN (2 * M) M))
                                 (Qn (binomN (2 * M) M))))
      with (Qmult (Qmult (polyQ a (Qn M)) (Qn (binomN (2 * M) M)))
                  (Qmult (polyQ a (Qn M)) (Qn (binomN (2 * M) M)))) by ring.
    rewrite Kop. ring. }
  assert (Hup : Qle (Qmult (Qn (3 * M + 1)%nat)
                           (Qmult (Qn (binomN (2 * M) M))
                                  (Qn (binomN (2 * M) M))))
                    (Qn (16 ^ M))).
  { assert (E : Qmult (Qn (3 * M + 1)%nat)
                      (Qmult (Qn (binomN (2 * M) M)) (Qn (binomN (2 * M) M)))
                == Qn ((3 * M + 1)
                       * (binomN (2 * M) M * binomN (2 * M) M))%nat)
      by (rewrite !Qn_mul; reflexivity).
    rewrite E. apply Qn_le. apply cb_upper. }
  assert (Hlo : Qle (Qn (16 ^ M))
                    (Qmult (Qn (4 * M + 1)%nat)
                           (Qmult (Qn (binomN (2 * M) M))
                                  (Qn (binomN (2 * M) M))))).
  { assert (E : Qmult (Qn (4 * M + 1)%nat)
                      (Qmult (Qn (binomN (2 * M) M)) (Qn (binomN (2 * M) M)))
                == Qn ((4 * M + 1)
                       * (binomN (2 * M) M * binomN (2 * M) M))%nat)
      by (rewrite !Qn_mul; reflexivity).
    rewrite E. apply Qn_le. apply cb_lower. }
  assert (HAA : Qle 0 (Qmult (polyQ a (Qn M)) (polyQ a (Qn M)))) by nra.
  assert (E3 : Qmult (Qmult (Qn (3 * M + 1)%nat)
                            (Qmult (polyQ b (Qn M)) (polyQ b (Qn M))))
                     (Qn (16 ^ M))
               == Qmult (Qn (3 * M + 1)%nat)
                        (Qmult (Qmult (polyQ b (Qn M)) (polyQ b (Qn M)))
                               (Qn (16 ^ M)))) by ring.
  assert (E4 : Qmult (Qmult (Qn (4 * M + 1)%nat)
                            (Qmult (polyQ b (Qn M)) (polyQ b (Qn M))))
                     (Qn (16 ^ M))
               == Qmult (Qn (4 * M + 1)%nat)
                        (Qmult (Qmult (polyQ b (Qn M)) (polyQ b (Qn M)))
                               (Qn (16 ^ M)))) by ring.
  split; apply (Qcancel_le_r _ _ (Qn (16 ^ M)) HG).
  - rewrite E3, <- Hsq.
    setoid_replace (Qmult (Qn (3 * M + 1)%nat)
                          (Qmult (Qmult (polyQ a (Qn M)) (polyQ a (Qn M)))
                                 (Qmult (Qn (binomN (2 * M) M))
                                        (Qn (binomN (2 * M) M)))))
      with (Qmult (Qmult (polyQ a (Qn M)) (polyQ a (Qn M)))
                  (Qmult (Qn (3 * M + 1)%nat)
                         (Qmult (Qn (binomN (2 * M) M))
                                (Qn (binomN (2 * M) M))))) by ring.
    apply Qmul_le_l; [exact Hup | exact HAA].
  - rewrite E4, <- Hsq.
    setoid_replace (Qmult (Qn (4 * M + 1)%nat)
                          (Qmult (Qmult (polyQ a (Qn M)) (polyQ a (Qn M)))
                                 (Qmult (Qn (binomN (2 * M) M))
                                        (Qn (binomN (2 * M) M)))))
      with (Qmult (Qmult (polyQ a (Qn M)) (polyQ a (Qn M)))
                  (Qmult (Qn (4 * M + 1)%nat)
                         (Qmult (Qn (binomN (2 * M) M))
                                (Qn (binomN (2 * M) M))))) by ring.
    apply Qmul_le_l; [exact Hlo | exact HAA].
Qed.

Theorem two_term_indep : forall a b : list Q,
  (forall M : nat,
     Qplus (Qmult (polyQ a (Qn M)) (Qn (binomN (2 * M) M)))
           (Qmult (polyQ b (Qn M)) (Qn (4 ^ M))) == 0) ->
  (forall j, nth j a 0%Q == 0) /\ (forall j, nth j b 0%Q == 0).
Proof.
  intros a b H.
  assert (Hs := two_term_sandwich a b H).
  assert (Hkey : nzlen a = 0%nat /\ nzlen b = 0%nat).
  { destruct (nzlen a) as [|nf] eqn:Ea; destruct (nzlen b) as [|ng] eqn:Eb.
    - split; reflexivity.
    - exfalso.
      assert (HBz : forall j, (ng < j)%nat -> nth j b 0%Q == 0)
        by (intros j Hj; apply nzlen_above; lia).
      destruct (polyQ_lower b ng HBz) as [Mb [Mb1 HMb]].
      assert (HBp : Qlt 0 (Qabs (nth ng b 0%Q)))
        by (apply Qabs_pos_of_ne; apply (nzlen_top b ng Eb)).
      assert (HZ := HMb Mb (Nat.le_refl Mb)).
      assert (Haz : polyQ a (Qn Mb) == 0) by (apply nzlen_zero_poly; exact Ea).
      assert (HMb2 := H Mb). rewrite Haz in HMb2.
      assert (HF : Qlt 0 (Qn (4 ^ Mb))) by (apply Qn_pos; apply four_pow_pos).
      assert (Hb0 : polyQ b (Qn Mb) == 0).
      { assert (K : Qmult (polyQ b (Qn Mb)) (Qn (4 ^ Mb)) == 0)
          by (rewrite <- HMb2; ring).
        destruct (Qmult_integral _ _ K) as [Kk|Kk]; [exact Kk|].
        exfalso. rewrite Kk in HF. exact (Qlt_irrefl 0 HF). }
      assert (E : Qabs (polyQ b (Qn Mb)) == 0) by (rewrite Hb0; reflexivity).
      rewrite E in HZ.
      assert (HX : Qlt 0 (Qn (Mb ^ ng)))
        by (apply Qn_pos; apply nat_pow_ge1; lia).
      nra.
    - exfalso.
      assert (HAz : forall j, (nf < j)%nat -> nth j a 0%Q == 0)
        by (intros j Hj; apply nzlen_above; lia).
      destruct (polyQ_lower a nf HAz) as [Ma [Ma1 HMa]].
      assert (HAp : Qlt 0 (Qabs (nth nf a 0%Q)))
        by (apply Qabs_pos_of_ne; apply (nzlen_top a nf Ea)).
      assert (HZ := HMa Ma (Nat.le_refl Ma)).
      assert (Hbz : polyQ b (Qn Ma) == 0) by (apply nzlen_zero_poly; exact Eb).
      assert (HMa2 := H Ma). rewrite Hbz in HMa2.
      assert (HC : Qlt 0 (Qn (binomN (2 * Ma) Ma)))
        by (apply Qn_pos; apply binomN_pos; lia).
      assert (Ha0 : polyQ a (Qn Ma) == 0).
      { assert (K : Qmult (polyQ a (Qn Ma)) (Qn (binomN (2 * Ma) Ma)) == 0)
          by (rewrite <- HMa2; ring).
        destruct (Qmult_integral _ _ K) as [Kk|Kk]; [exact Kk|].
        exfalso. rewrite Kk in HC. exact (Qlt_irrefl 0 HC). }
      assert (E : Qabs (polyQ a (Qn Ma)) == 0) by (rewrite Ha0; reflexivity).
      rewrite E in HZ.
      assert (HX : Qlt 0 (Qn (Ma ^ nf)))
        by (apply Qn_pos; apply nat_pow_ge1; lia).
      nra.
    - exfalso.
      assert (HAz : forall j, (nf < j)%nat -> nth j a 0%Q == 0)
        by (intros j Hj; apply nzlen_above; lia).
      assert (HBz : forall j, (ng < j)%nat -> nth j b 0%Q == 0)
        by (intros j Hj; apply nzlen_above; lia).
      destruct (polyQ_lower a nf HAz) as [Ma [Ma1 HMa]].
      destruct (polyQ_lower b ng HBz) as [Mb [Mb1 HMb]].
      assert (HAp : Qlt 0 (Qabs (nth nf a 0%Q)))
        by (apply Qabs_pos_of_ne; apply (nzlen_top a nf Ea)).
      assert (HBp : Qlt 0 (Qabs (nth ng b 0%Q)))
        by (apply Qabs_pos_of_ne; apply (nzlen_top b ng Eb)).
      assert (HKa := sumabs_nonneg (firstn (S nf) a)).
      assert (HKb := sumabs_nonneg (firstn (S ng) b)).
      destruct (Nat.le_gt_cases nf ng) as [Hle|Hgt].
      + apply (no_linear_bound
                 (Qmult 3 (Qmult (Qabs (nth ng b 0%Q)) (Qabs (nth ng b 0%Q))))
                 (Qmult 4 (Qmult (sumabs (firstn (S nf) a))
                                 (sumabs (firstn (S nf) a))))
                 (Nat.max 1 (Nat.max Ma Mb))); [nra|].
        intros M HM.
        assert (HM1 : (1 <= M)%nat) by lia.
        assert (HQM : Qle 0 (Qn M)) by apply Qn_nonneg.
        assert (HX : Qlt 0 (Qn (M ^ ng)))
          by (apply Qn_pos; apply nat_pow_ge1; exact HM1).
        assert (S1 := proj1 (Hs M)).
        assert (E3 : Qn (3 * M + 1)%nat == Qplus (Qmult 3 (Qn M)) 1)
          by (rewrite Qn_lin, Qn3, Qn_1; reflexivity).
        rewrite E3 in S1.
        assert (U := polyQ_upper_deg a nf M HM1 HAz).
        assert (Pow : Qle (Qn (M ^ nf)) (Qn (M ^ ng)))
          by (apply Qn_le; apply Nat.pow_le_mono_r; lia).
        assert (L := HMb M ltac:(lia)).
        assert (HBnn := Qabs_nonneg (polyQ b (Qn M))).
        assert (HAnn := Qabs_nonneg (polyQ a (Qn M))).
        assert (HAsq : Qle (Qmult (polyQ a (Qn M)) (polyQ a (Qn M)))
                           (Qmult (Qmult (sumabs (firstn (S nf) a))
                                         (sumabs (firstn (S nf) a)))
                                  (Qmult (Qn (M ^ ng)) (Qn (M ^ ng))))).
        { rewrite (Qsq_abs (polyQ a (Qn M))).
          assert (HU2 : Qle (Qabs (polyQ a (Qn M)))
                            (Qmult (sumabs (firstn (S nf) a)) (Qn (M ^ ng))))
            by nra.
          nra. }
        assert (HBsq : Qle (Qmult (Qmult (Qabs (nth ng b 0%Q))
                                         (Qabs (nth ng b 0%Q)))
                                  (Qmult (Qn (M ^ ng)) (Qn (M ^ ng))))
                           (Qmult 4 (Qmult (polyQ b (Qn M))
                                           (polyQ b (Qn M))))).
        { rewrite (Qsq_abs (polyQ b (Qn M))).
          assert (Hnn : Qle 0 (Qmult (Qabs (nth ng b 0%Q)) (Qn (M ^ ng))))
            by nra.
          nra. }
        apply (Qcancel_le_r _ _ (Qmult (Qn (M ^ ng)) (Qn (M ^ ng)))); [nra|].
        assert (HBB : Qle 0 (Qmult (polyQ b (Qn M)) (polyQ b (Qn M)))) by nra.
        assert (Hmid : Qle (Qmult (Qmult 3 (Qn M))
                                  (Qmult (Qmult (Qabs (nth ng b 0%Q))
                                                (Qabs (nth ng b 0%Q)))
                                         (Qmult (Qn (M ^ ng)) (Qn (M ^ ng)))))
                           (Qmult 4 (Qmult (polyQ a (Qn M))
                                           (polyQ a (Qn M))))).
        { assert (K2 : Qle (Qmult (Qmult 3 (Qn M))
                                  (Qmult (polyQ b (Qn M)) (polyQ b (Qn M))))
                           (Qmult (polyQ a (Qn M)) (polyQ a (Qn M)))) by nra.
          nra. }
        nra.
      + apply (no_linear_bound
                 (Qmult (Qabs (nth nf a 0%Q)) (Qabs (nth nf a 0%Q)))
                 (Qmult 20 (Qmult (sumabs (firstn (S ng) b))
                                  (sumabs (firstn (S ng) b))))
                 (Nat.max 1 (Nat.max Ma Mb))); [nra|].
        intros M HM.
        assert (HM1 : (1 <= M)%nat) by lia.
        assert (HQM1 : Qle 1 (Qn M)) by (rewrite <- Qn_1; apply Qn_le; lia).
        assert (HQM : Qle 0 (Qn M)) by apply Qn_nonneg.
        assert (HX : Qlt 0 (Qn (M ^ ng)))
          by (apply Qn_pos; apply nat_pow_ge1; exact HM1).
        assert (S2 := proj2 (Hs M)).
        assert (E4 : Qn (4 * M + 1)%nat == Qplus (Qmult 4 (Qn M)) 1)
          by (rewrite Qn_lin, Qn4, Qn_1; reflexivity).
        rewrite E4 in S2.
        assert (U := polyQ_upper_deg b ng M HM1 HBz).
        assert (L := HMa M ltac:(lia)).
        assert (Pow : Qle (Qmult (Qn M) (Qn (M ^ ng))) (Qn (M ^ nf))).
        { assert (E : Qn (M ^ S ng) == Qmult (Qn M) (Qn (M ^ ng)))
            by (cbn [Nat.pow]; rewrite Qn_mul; reflexivity).
          rewrite <- E. apply Qn_le. apply Nat.pow_le_mono_r; lia. }
        assert (HBnn := Qabs_nonneg (polyQ b (Qn M))).
        assert (HAnn := Qabs_nonneg (polyQ a (Qn M))).
        assert (HBsq : Qle (Qmult (polyQ b (Qn M)) (polyQ b (Qn M)))
                           (Qmult (Qmult (sumabs (firstn (S ng) b))
                                         (sumabs (firstn (S ng) b)))
                                  (Qmult (Qn (M ^ ng)) (Qn (M ^ ng))))).
        { rewrite (Qsq_abs (polyQ b (Qn M))). nra. }
        assert (HQX : Qle 0 (Qmult (Qn M) (Qn (M ^ ng)))) by nra.
        assert (HXX : Qlt 0 (Qmult (Qn (M ^ ng)) (Qn (M ^ ng)))) by nra.
        assert (HAsq : Qle (Qmult (Qmult (Qabs (nth nf a 0%Q))
                                         (Qabs (nth nf a 0%Q)))
                                  (Qmult (Qmult (Qn M) (Qn (M ^ ng)))
                                         (Qmult (Qn M) (Qn (M ^ ng)))))
                           (Qmult 4 (Qmult (polyQ a (Qn M))
                                           (polyQ a (Qn M))))).
        { rewrite (Qsq_abs (polyQ a (Qn M))).
          assert (HL2 : Qle (Qmult (Qabs (nth nf a 0%Q))
                                   (Qmult (Qn M) (Qn (M ^ ng))))
                            (Qmult 2 (Qabs (polyQ a (Qn M))))) by nra.
          assert (Hnn : Qle 0 (Qmult (Qabs (nth nf a 0%Q))
                                     (Qmult (Qn M) (Qn (M ^ ng))))) by nra.
          nra. }
        apply (Qcancel_le_r _ _ (Qmult (Qn M)
                                       (Qmult (Qn (M ^ ng)) (Qn (M ^ ng)))));
          [nra|].
        assert (HBB : Qle 0 (Qmult (polyQ b (Qn M)) (polyQ b (Qn M)))) by nra.
        assert (Hmid : Qle (Qmult (polyQ a (Qn M)) (polyQ a (Qn M)))
                           (Qmult (Qmult 5 (Qn M))
                                  (Qmult (Qmult (sumabs (firstn (S ng) b))
                                                (sumabs (firstn (S ng) b)))
                                         (Qmult (Qn (M ^ ng))
                                                (Qn (M ^ ng)))))).
        { assert (K1 : Qle (Qmult (polyQ a (Qn M)) (polyQ a (Qn M)))
                           (Qmult (Qmult 5 (Qn M))
                                  (Qmult (polyQ b (Qn M)) (polyQ b (Qn M)))))
            by nra.
          nra. }
        nra. }
  destruct Hkey as [Ha0 Hb0].
  split; intro j; apply nzlen_above; lia.
Qed.

(* Hence the coefficient lists a Diagonal carries are determined. *)

Lemma polyQ_nth_eq : forall c c' x,
  (forall j, nth j c 0%Q == nth j c' 0%Q) -> polyQ c x == polyQ c' x.
Proof.
  induction c as [|u c IH]; intros c' x H.
  - cbn [polyQ]. symmetry. apply polyQ_zero_list. intro j.
    assert (K := H j). rewrite nth_nil in K. rewrite <- K. reflexivity.
  - destruct c' as [|v c'].
    + assert (Hc : polyQ c x == polyQ (@nil Q) x).
      { apply IH. intro j. assert (K := H (S j)). cbn [nth] in K.
        rewrite nth_nil. exact K. }
      assert (Hu : u == 0).
      { assert (K := H 0%nat). cbn [nth] in K. exact K. }
      cbn [polyQ] in *. rewrite Hc, Hu. ring.
    + assert (Hc : polyQ c x == polyQ c' x)
        by (apply IH; intro j; exact (H (S j))).
      assert (Hu : u == v) by (assert (K := H 0%nat); cbn [nth] in K; exact K).
      cbn [polyQ]. rewrite Hc, Hu. reflexivity.
Qed.

Theorem diagonal_unique : forall d (Dg Dg' : Diagonal d),
  (forall j, nth j (dp d Dg) 0%Q == nth j (dp d Dg') 0%Q)
  /\ (forall j, nth j (dq d Dg) 0%Q == nth j (dq d Dg') 0%Q).
Proof.
  intros d Dg Dg'.
  assert (H : forall M : nat,
    Qplus (Qmult (polyQ (psub (dp d Dg) (dp d Dg')) (Qn M))
                 (Qn (binomN (2 * M) M)))
          (Qmult (polyQ (psub (dq d Dg) (dq d Dg')) (Qn M))
                 (Qn (4 ^ M))) == 0).
  { intro M. rewrite !psub_spec.
    assert (K1 := d_law d Dg M). assert (K2 := d_law d Dg' M).
    rewrite K1 in K2.
    setoid_replace
      (Qplus (Qmult (Qminus (polyQ (dp d Dg) (Qn M)) (polyQ (dp d Dg') (Qn M)))
                    (Qn (binomN (2 * M) M)))
             (Qmult (Qminus (polyQ (dq d Dg) (Qn M)) (polyQ (dq d Dg') (Qn M)))
                    (Qn (4 ^ M))))
      with (Qminus
              (Qplus (Qmult (polyQ (dp d Dg) (Qn M)) (Qn (binomN (2 * M) M)))
                     (Qmult (polyQ (dq d Dg) (Qn M)) (Qn (4 ^ M))))
              (Qplus (Qmult (polyQ (dp d Dg') (Qn M)) (Qn (binomN (2 * M) M)))
                     (Qmult (polyQ (dq d Dg') (Qn M)) (Qn (4 ^ M)))))
      by ring.
    rewrite K2. ring. }
  destruct (two_term_indep _ _ H) as [Ha Hb].
  split; intro j.
  - assert (K := Ha j). rewrite nth_psub in K.
    setoid_replace (nth j (dp d Dg) 0%Q)
      with (Qplus (Qminus (nth j (dp d Dg) 0%Q) (nth j (dp d Dg') 0%Q))
                  (nth j (dp d Dg') 0%Q)) by ring.
    rewrite K. ring.
  - assert (K := Hb j). rewrite nth_psub in K.
    setoid_replace (nth j (dq d Dg) 0%Q)
      with (Qplus (Qminus (nth j (dq d Dg) 0%Q) (nth j (dq d Dg') 0%Q))
                  (nth j (dq d Dg') 0%Q)) by ring.
    rewrite K. ring.
Qed.

Corollary diagonal_unique_poly : forall d (Dg Dg' : Diagonal d) x,
  polyQ (dp d Dg) x == polyQ (dp d Dg') x
  /\ polyQ (dq d Dg) x == polyQ (dq d Dg') x.
Proof.
  intros d Dg Dg' x. destruct (diagonal_unique d Dg Dg') as [Hp Hq].
  split; apply polyQ_nth_eq; assumption.
Qed.

(* The results proved at a constructed record now hold at every inhabitant.
   At d = 1 the record exists outright, so these are unconditional. *)

Theorem p_lead_one_any : forall Dg : Diagonal 1,
  Qmult (Qn (factn 1)) (nth 0 (dp 1 Dg) 0%Q) == 1.
Proof.
  intro Dg. destruct (diagonal_unique 1 Dg diagonal_one) as [Hp _].
  rewrite (Hp 0%nat). reflexivity.
Qed.

Theorem R_at_minus_one_one_any : forall Dg : Diagonal 1,
  Qminus (polyQ (dp 1 Dg) 0) (polyQ (dq 1 Dg) 0) == 1.
Proof.
  intro Dg. destruct (diagonal_unique_poly 1 Dg diagonal_one 0) as [Hp Hq].
  assert (E1 : dp 1 diagonal_one = 1%Q :: nil) by reflexivity.
  assert (E2 : dq 1 diagonal_one = @nil Q) by reflexivity.
  rewrite Hp, Hq, E1, E2. cbn [polyQ]. ring.
Qed.

Corollary exponent_law_at_zero_one : forall Dg : Diagonal 1,
  Qle (Qabs (rcoef 1 Dg 0)) (Qmult 1 (Qn (1 ^ 0))).
Proof.
  intro Dg. apply exponent_law_at_zero; [lia | apply p_lead_one_any].
Qed.

(* At d = 2 the record exists as soon as the increasing fibre closes, and then
   the leading coefficient and R_d(-1) are the same at every inhabitant. *)

Theorem p_lead_two_any : NSIG_TWO_CLOSED -> forall Dg : Diagonal 2,
  Qmult (Qn (factn 2)) (nth 1 (dp 2 Dg) 0%Q) == 1.
Proof.
  intros HN Dg.
  destruct (diagonal_unique 2 Dg (diagonal_two_fib HN)) as [Hp _].
  rewrite (Hp 1%nat). exact p_lead_two.
Qed.

Theorem R_at_minus_one_two_any : NSIG_TWO_CLOSED -> forall Dg : Diagonal 2,
  Qminus (polyQ (dp 2 Dg) 0) (polyQ (dq 2 Dg) 0) == 1.
Proof.
  intros HN Dg.
  destruct (diagonal_unique_poly 2 Dg (diagonal_two_fib HN) 0) as [Hp Hq].
  rewrite Hp, Hq. exact (R_at_minus_one_of_two HN).
Qed.

Corollary exponent_law_at_zero_two : NSIG_TWO_CLOSED -> forall Dg : Diagonal 2,
  Qle (Qabs (rcoef 2 Dg 0)) (Qmult 1 (Qn (2 ^ 0))).
Proof.
  intros HN Dg. apply exponent_law_at_zero; [lia | apply p_lead_two_any; exact HN].
Qed.

(* ------------------------------------------------------------------ *)
(* The state function under the max-split.  H is a capped minimum, so it is
   fixed by three clauses: it lies at or below the cap, at or below every high
   value, and is one of the two.  That characterisation is the whole interface;
   hvals is reached only through in_hvals, never through firstlt. *)

Lemma foldmin_le_cap : forall (l : list nat) c, fold_right Nat.min c l <= c.
Proof.
  induction l as [|a l IH]; intro c; cbn [fold_right]; [lia|].
  assert (H := IH c). lia.
Qed.

Lemma foldmin_le_in : forall (l : list nat) c v,
  In v l -> fold_right Nat.min c l <= v.
Proof.
  induction l as [|a l IH]; intros c v Hv; [contradiction|].
  cbn [fold_right]. destruct Hv as [<- | Hv]; [lia|].
  assert (H := IH c v Hv). lia.
Qed.

Lemma foldmin_wit : forall (l : list nat) c,
  fold_right Nat.min c l = c \/ In (fold_right Nat.min c l) l.
Proof.
  induction l as [|a l IH]; intro c; cbn [fold_right]; [left; reflexivity|].
  destruct (Nat.min_dec a (fold_right Nat.min c l)) as [K|K]; rewrite K.
  - right. left. reflexivity.
  - destruct (IH c) as [E|E]; [left; exact E | right; right; exact E].
Qed.

Lemma Hu_le_cap : forall u M y, Hu u M y <= M.
Proof. intros u M y. unfold Hu. apply foldmin_le_cap. Qed.

Lemma Hu_le_in : forall u M y v, In v (hvals u y) -> Hu u M y <= v.
Proof. intros u M y v H. unfold Hu. apply (foldmin_le_in _ M v H). Qed.

Lemma Hu_wit : forall u M y, Hu u M y = M \/ In (Hu u M y) (hvals u y).
Proof. intros u M y. unfold Hu. apply foldmin_wit. Qed.

Lemma Hu_char : forall u M y v,
  v <= M ->
  (forall t, In t (hvals u y) -> v <= t) ->
  (v = M \/ In v (hvals u y)) ->
  Hu u M y = v.
Proof.
  intros u M y v Hv Hmin Hw.
  assert (H1 : Hu u M y <= v).
  { destruct Hw as [E|E]; [subst v; apply Hu_le_cap | apply Hu_le_in; exact E]. }
  assert (H2 : v <= Hu u M y).
  { destruct (Hu_wit u M y) as [E|E];
      [rewrite E; exact Hv | apply Hmin; exact E]. }
  lia.
Qed.

Lemma Hu_same_members : forall u u' M y,
  (forall v, In v (hvals u y) <-> In v (hvals u' y)) ->
  Hu u M y = Hu u' M y.
Proof.
  intros u u' M y Hsame. apply Hu_char.
  - apply Hu_le_cap.
  - intros t Ht. apply Hu_le_in. apply Hsame. exact Ht.
  - destruct (Hu_wit u' M y) as [E|E];
      [left; exact E | right; apply Hsame; exact E].
Qed.

Lemma hvals_ge : forall u y v, In v (hvals u y) -> y <= v.
Proof.
  intros u y v H. apply in_hvals in H.
  destruct H as [i [j [_ [_ [_ [Hyj Hn]]]]]]. lia.
Qed.

Lemma Hu_ge : forall u M y, y <= M -> y <= Hu u M y.
Proof.
  intros u M y HM. destruct (Hu_wit u M y) as [E|E].
  - rewrite E. exact HM.
  - assert (K := hvals_ge u y _ E). lia.
Qed.

Lemma hvals_zero_empty : forall u v, ~ In v (hvals u 0).
Proof.
  intros u v H. apply in_hvals in H.
  destruct H as [i [j [_ [_ [Hi _]]]]]. lia.
Qed.

Lemma Hu_zero : forall u M, Hu u M 0 = M.
Proof.
  intros u M. destruct (Hu_wit u M 0) as [E|E];
    [exact E | exfalso; exact (hvals_zero_empty u _ E)].
Qed.

Lemma Hu_top : forall u M, Hu u M M = M.
Proof.
  intros u M. assert (H1 := Hu_le_cap u M M).
  assert (H2 := Hu_ge u M M (Nat.le_refl M)). lia.
Qed.

(* An empty high set is exactly safety at that value. *)
Lemma hvals_empty_safe : forall u y,
  safe_at u y <-> (forall v, ~ In v (hvals u y)).
Proof.
  intros u y. unfold safe_at. split.
  - intros Hs v Hv. apply in_hvals in Hv.
    destruct Hv as [i [j [Hij [Hj [Hi [Hyj _]]]]]].
    apply Hs. exists i, j. repeat split; assumption.
  - intros Hno [i [j [Hij [Hj [Hi Hyj]]]]].
    apply (Hno (nth j u 0)). apply in_hvals.
    exists i, j. repeat split; assumption.
Qed.

Lemma Hu_safe : forall u M y, safe_at u y -> Hu u M y = M.
Proof.
  intros u M y Hs. destruct (Hu_wit u M y) as [E|E]; [exact E|].
  exfalso. exact (proj1 (hvals_empty_safe u y) Hs _ E).
Qed.

(* Below the split the high values are exactly the right factor's. *)
Lemma hvals_midmax_lo : forall a b y v,
  1 <= y -> y <= length b ->
  (In v (hvals (midmax a b) y) <-> In v (hvals b y)).
Proof.
  intros a b y v Hy1 Hyb. rewrite !in_hvals. split.
  - intros [i [j [Hij [Hj [Hi [Hyj Hn]]]]]].
    rewrite midmax_length in Hj.
    assert (Hia : length a < i).
    { destruct (Nat.lt_trichotomy i (length a)) as [K|[K|K]]; [| |exact K].
      - exfalso. rewrite (midmax_lo a b i K) in Hi. lia.
      - exfalso. rewrite K, (midmax_mid a b) in Hi. lia. }
    assert (Hja : length a < j) by lia.
    rewrite (midmax_hi a b i Hia) in Hi.
    rewrite (midmax_hi a b j Hja) in Hyj.
    rewrite (midmax_hi a b j Hja) in Hn.
    exists (i - S (length a)), (j - S (length a)).
    repeat split; try lia.
  - intros [i [j [Hij [Hj [Hi [Hyj Hn]]]]]].
    assert (Hqi : length a < S (length a) + i) by lia.
    assert (Hqj : length a < S (length a) + j) by lia.
    exists (S (length a) + i), (S (length a) + j).
    rewrite (midmax_hi a b (S (length a) + i) Hqi).
    rewrite (midmax_hi a b (S (length a) + j) Hqj).
    replace (S (length a) + i - S (length a)) with i by lia.
    replace (S (length a) + j - S (length a)) with j by lia.
    rewrite midmax_length. repeat split; try lia.
Qed.

(* Above it they are the left factor's, lifted, together with the maximum. *)
Lemma hvals_midmax_hi : forall a b y v,
  is_perm a (length a) -> is_perm b (length b) ->
  length b < y -> y <= length a + length b ->
  (In v (hvals (midmax a b) y)
   <-> (v = length a + length b
        \/ exists v', In v' (hvals a (y - length b)) /\ v = v' + length b)).
Proof.
  intros a b y v Hpa Hpb Hy1 Hy2.
  assert (Hbv : forall t, t < length b -> nth t b 0 < length b).
  { intros t Ht. destruct Hpb as [_ [_ Hb]]. apply Hb. apply nth_In. lia. }
  assert (Hal : 1 <= length a) by lia.
  rewrite in_hvals. split.
  - intros [i [j [Hij [Hj [Hi [Hyj Hn]]]]]].
    rewrite midmax_length in Hj.
    assert (Hjle : j <= length a).
    { destruct (Nat.le_gt_cases j (length a)) as [K|K]; [exact K|].
      exfalso. rewrite (midmax_hi a b j K) in Hyj.
      assert (K2 := Hbv (j - S (length a)) ltac:(lia)). lia. }
    destruct (Nat.eq_dec j (length a)) as [Ej|Ej].
    + left. rewrite Ej, (midmax_mid a b) in Hn. lia.
    + right.
      assert (Hja : j < length a) by lia.
      rewrite (midmax_lo a b i ltac:(lia)) in Hi.
      rewrite (midmax_lo a b j Hja) in Hyj, Hn.
      exists (nth j a 0). split; [| lia].
      apply in_hvals. exists i, j. repeat split; lia.
  - assert (Hzero : exists i, i < length a /\ nth i a 0 = 0).
    { assert (Hin : In 0 a) by (apply (perm_full a (length a) Hpa); lia).
      apply In_nth with (d := 0) in Hin. destruct Hin as [i [Hi Hn]].
      exists i. split; [exact Hi | exact Hn]. }
    destruct Hzero as [i0 [Hi0 Hn0]].
    intros [Ev | [v' [Hv' Ev]]].
    + exists i0, (length a).
      rewrite (midmax_lo a b i0 Hi0), (midmax_mid a b), midmax_length, Hn0.
      repeat split; lia.
    + apply in_hvals in Hv'.
      destruct Hv' as [i [j [Hij [Hj [Hi [Hyj Hn]]]]]].
      exists i, j.
      rewrite (midmax_lo a b i ltac:(lia)), (midmax_lo a b j Hj), midmax_length.
      repeat split; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The three evaluations of H at a max-split.  Below the split H is the right
   factor's, except where that factor is safe and the cap moves; above it H is
   the left factor's, lifted by the right factor's size. *)

Lemma unsafe_hvals_member : forall u y,
  ~ safe_at u y -> exists v, In v (hvals u y).
Proof.
  intros u y H. destruct (hvals u y) as [|v l] eqn:E.
  - exfalso. apply H. apply hvals_empty_safe. intros z Hz.
    rewrite E in Hz. contradiction.
  - exists v. left. reflexivity.
Qed.

Lemma safe_at_zero : forall u, safe_at u 0.
Proof. intros u [i [j [_ [_ [Hi _]]]]]. lia. Qed.

Lemma Hu_midmax_lo_safe : forall a b y,
  1 <= y -> y <= length b -> safe_at b y ->
  Hu (midmax a b) (length a + S (length b)) y = length a + S (length b).
Proof.
  intros a b y H1 H2 Hs. apply Hu_safe. apply hvals_empty_safe.
  intros v Hv.
  exact (proj1 (hvals_empty_safe b y) Hs v
           (proj1 (hvals_midmax_lo a b y v H1 H2) Hv)).
Qed.

Lemma Hu_midmax_lo_unsafe : forall a b y,
  1 <= y -> y <= length b -> is_perm b (length b) -> ~ safe_at b y ->
  Hu (midmax a b) (length a + S (length b)) y = Hu b (length b) y.
Proof.
  intros a b y H1 H2 Hpb Hns.
  destruct (unsafe_hvals_member b y Hns) as [v0 Hv0].
  assert (Hbnd : forall v, In v (hvals b y) -> v < length b).
  { intros v Hv. apply in_hvals in Hv.
    destruct Hv as [_ [j [_ [Hj [_ [_ Hn]]]]]].
    rewrite <- Hn. destruct Hpb as [_ [_ Hb]]. apply Hb. apply nth_In. lia. }
  assert (Hlt : Hu b (length b) y < length b).
  { assert (K := Hu_le_in b (length b) y v0 Hv0).
    assert (K2 := Hbnd v0 Hv0). lia. }
  apply Hu_char.
  - lia.
  - intros t Ht. apply Hu_le_in.
    exact (proj1 (hvals_midmax_lo a b y t H1 H2) Ht).
  - destruct (Hu_wit b (length b) y) as [E|E]; [exfalso; lia|].
    right. exact (proj2 (hvals_midmax_lo a b y _ H1 H2) E).
Qed.

Lemma Hu_midmax_hi : forall a b y,
  is_perm a (length a) -> is_perm b (length b) ->
  length b < y -> y <= length a + length b ->
  Hu (midmax a b) (length a + S (length b)) y
  = length b + Hu a (length a) (y - length b).
Proof.
  intros a b y Hpa Hpb H1 H2.
  assert (Hcap := Hu_le_cap a (length a) (y - length b)).
  apply Hu_char.
  - lia.
  - intros t Ht.
    destruct (proj1 (hvals_midmax_hi a b y t Hpa Hpb H1 H2) Ht)
      as [Ev | [v' [Hv' Ev]]].
    + lia.
    + assert (K := Hu_le_in a (length a) (y - length b) v' Hv'). lia.
  - right. apply (proj2 (hvals_midmax_hi a b y _ Hpa Hpb H1 H2)).
    destruct (Hu_wit a (length a) (y - length b)) as [E|E].
    + left. lia.
    + right. exists (Hu a (length a) (y - length b)). split; [exact E | lia].
Qed.

(* ------------------------------------------------------------------ *)
(* The level sum, and the arithmetic of a range split. *)

Definition hgap (u : list nat) (M y : nat) : nat := Hu u M y - y.

Definition Lsum (u : list nat) (M : nat) : nat :=
  fold_right (fun y acc => (hgap u M y + acc)%nat) 0%nat (seq 0 (S M)).

Lemma nfold_app : forall (A : Type) (g : A -> nat) (l1 l2 : list A),
  fold_right (fun x acc => (g x + acc)%nat) 0%nat (l1 ++ l2)
  = (fold_right (fun x acc => (g x + acc)%nat) 0%nat l1
     + fold_right (fun x acc => (g x + acc)%nat) 0%nat l2)%nat.
Proof.
  intros A g. induction l1 as [|a l1 IH]; intro l2; cbn [app fold_right];
    [reflexivity | rewrite IH; lia].
Qed.

Lemma nfold_scal : forall (A : Type) (c : nat) (g : A -> nat) (l : list A),
  fold_right (fun x acc => (c * g x + acc)%nat) 0%nat l
  = (c * fold_right (fun x acc => (g x + acc)%nat) 0%nat l)%nat.
Proof.
  intros A c g. induction l as [|a l IH]; cbn [fold_right]; [lia|].
  rewrite IH. lia.
Qed.

Lemma seq_break : forall n m s, seq s (n + m) = seq s n ++ seq (s + n) m.
Proof.
  induction n as [|n IH]; intros m s.
  - cbn [Nat.add seq app]. rewrite Nat.add_0_r. reflexivity.
  - replace (S n + m) with (S (n + m)) by lia.
    cbn [seq app]. rewrite (IH m (S s)).
    replace (S s + n) with (s + S n) by lia. reflexivity.
Qed.

Lemma seq_add_map : forall n s c, map (fun t => t + c) (seq s n) = seq (s + c) n.
Proof.
  induction n as [|n IH]; intros s c; cbn [seq map]; [reflexivity|].
  rewrite (IH (S s) c). replace (S s + c) with (S (s + c)) by lia. reflexivity.
Qed.

Lemma seq_split_three : forall al bl,
  seq 0 (S (al + S bl))
  = seq 0 1 ++ seq 1 bl ++ seq (S bl) al ++ seq (al + S bl) 1.
Proof.
  intros al bl.
  replace (S (al + S bl)) with (1 + (bl + (al + 1))) by lia.
  rewrite (seq_break 1 (bl + (al + 1)) 0).
  replace (0 + 1) with 1 by lia.
  rewrite (seq_break bl (al + 1) 1).
  replace (1 + bl) with (S bl) by lia.
  rewrite (seq_break al 1 (S bl)).
  replace (S bl + al) with (al + S bl) by lia.
  reflexivity.
Qed.

Lemma Lsum_split : forall u al bl,
  Lsum u (al + S bl)
  = (hgap u (al + S bl) 0
     + (fold_right (fun y acc => (hgap u (al + S bl) y + acc)%nat) 0%nat
                   (seq 1 bl)
        + (fold_right (fun y acc => (hgap u (al + S bl) y + acc)%nat) 0%nat
                      (seq (S bl) al)
           + hgap u (al + S bl) (al + S bl))))%nat.
Proof.
  intros u al bl. unfold Lsum. rewrite (seq_split_three al bl).
  rewrite !(nfold_app nat (hgap u (al + S bl))).
  cbn [seq fold_right]. lia.
Qed.

Lemma Lsum_tail : forall u M,
  Lsum u M
  = (M + fold_right (fun y acc => (hgap u M y + acc)%nat) 0%nat (seq 1 M))%nat.
Proof.
  intros u M. unfold Lsum. cbn [seq fold_right].
  unfold hgap at 1. rewrite Hu_zero. lia.
Qed.

Lemma safecount_head : forall b bl,
  safecount b bl = S (length (filter (safeb b) (seq 1 bl))).
Proof.
  intros b bl. unfold safecount.
  assert (E : safeb b 0 = true) by (apply safeb_spec; apply safe_at_zero).
  cbn [seq filter]. rewrite E. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The recursion the max-split carries.  The left factor contributes its own
   sum, the right factor contributes its own sum together with one copy of the
   left column per safe value, and the split point contributes one. *)

Theorem Lsum_midmax : forall a b,
  is_perm a (length a) -> is_perm b (length b) ->
  (Lsum (midmax a b) (length a + S (length b)) + (length a + 1)
   = 1 + Lsum a (length a) + Lsum b (length b)
     + (length a + 1) * safecount b (length b))%nat.
Proof.
  intros a b Hpa Hpb.
  rewrite (Lsum_split (midmax a b) (length a) (length b)).
  assert (E0 : hgap (midmax a b) (length a + S (length b)) 0
               = length a + S (length b)).
  { unfold hgap. rewrite Hu_zero. lia. }
  assert (EN : hgap (midmax a b) (length a + S (length b))
                    (length a + S (length b)) = 0).
  { unfold hgap. rewrite Hu_top. lia. }
  rewrite E0, EN.
  assert (EA : fold_right (fun y acc =>
                 (hgap (midmax a b) (length a + S (length b)) y + acc)%nat)
                 0%nat (seq (S (length b)) (length a))
               = fold_right (fun y acc => (hgap a (length a) y + acc)%nat)
                            0%nat (seq 1 (length a))).
  { replace (seq (S (length b)) (length a))
      with (map (fun t => t + length b) (seq 1 (length a)))
      by (rewrite seq_add_map; reflexivity).
    rewrite (nfold_map_gen nat nat
               (hgap (midmax a b) (length a + S (length b)))
               (fun t => t + length b) (seq 1 (length a))).
    cbn beta.
    apply (nfold_ext_in nat
             (fun t => hgap (midmax a b) (length a + S (length b))
                            (t + length b))
             (hgap a (length a)) (seq 1 (length a))).
    intros t Ht. apply in_seq in Ht. destruct Ht as [Ht1 Ht2].
    assert (Hy1 : length b < t + length b) by lia.
    assert (Hy2 : t + length b <= length a + length b) by lia.
    unfold hgap.
    rewrite (Hu_midmax_hi a b (t + length b) Hpa Hpb Hy1 Hy2).
    replace (t + length b - length b) with t by lia. lia. }
  rewrite EA.
  assert (EB : fold_right (fun y acc =>
                 (hgap (midmax a b) (length a + S (length b)) y + acc)%nat)
                 0%nat (seq 1 (length b))
               = (fold_right (fun y acc => (hgap b (length b) y + acc)%nat)
                             0%nat (seq 1 (length b))
                  + (length a + 1)
                    * length (filter (safeb b) (seq 1 (length b))))%nat).
  { transitivity (fold_right (fun k acc =>
        (hgap b (length b) k
         + (length a + 1) * (if safeb b k then 1 else 0) + acc)%nat)
        0%nat (seq 1 (length b))).
    - apply (nfold_ext_in nat
               (hgap (midmax a b) (length a + S (length b)))
               (fun k => (hgap b (length b) k
                          + (length a + 1) * (if safeb b k then 1 else 0))%nat)
               (seq 1 (length b))).
      intros y Hy. apply in_seq in Hy. destruct Hy as [Hy1 Hy2].
      assert (Hy1' : 1 <= y) by lia.
      assert (Hy2' : y <= length b) by lia.
      destruct (safeb b y) eqn:Es.
      + assert (Hs : safe_at b y) by (apply safeb_spec; exact Es).
        unfold hgap.
        rewrite (Hu_midmax_lo_safe a b y Hy1' Hy2' Hs).
        rewrite (Hu_safe b (length b) y Hs). lia.
      + assert (Hns : ~ safe_at b y).
        { intro C. assert (K : safeb b y = true) by (apply safeb_spec; exact C).
          rewrite Es in K. discriminate. }
        unfold hgap.
        rewrite (Hu_midmax_lo_unsafe a b y Hy1' Hy2' Hpb Hns). lia.
    - rewrite (fold_add_split nat (fun k => hgap b (length b) k)
                 (fun k => ((length a + 1) * (if safeb b k then 1 else 0))%nat)
                 (seq 1 (length b))).
      f_equal.
      rewrite (nfold_scal nat (length a + 1)
                 (fun k => if safeb b k then 1 else 0) (seq 1 (length b))).
      f_equal. symmetry. apply length_filter_fold. }
  rewrite EB.
  rewrite (Lsum_tail a (length a)), (Lsum_tail b (length b)),
          (safecount_head b (length b)).
  nia.
Qed.

(* ------------------------------------------------------------------ *)
(* Summing the recursion over the class.  The max-split is a bijection onto
   ordered pairs of 132-avoiders, so a sum over Av(132)_{m+1} is a triple sum
   over the split point and the two factors. *)

Lemma nfold_flat_map : forall (A B : Type) (g : B -> nat) (f : A -> list B)
    (l : list A),
  fold_right (fun x acc => (g x + acc)%nat) 0%nat (flat_map f l)
  = fold_right (fun x acc =>
      (fold_right (fun y acc' => (g y + acc')%nat) 0%nat (f x) + acc)%nat)
      0%nat l.
Proof.
  intros A B g f. induction l as [|a l IH]; cbn [flat_map fold_right];
    [reflexivity|]. rewrite nfold_app, IH. reflexivity.
Qed.

Lemma nfold_const : forall (A : Type) (c : nat) (l : list A),
  fold_right (fun _ acc => (c + acc)%nat) 0%nat l = (c * length l)%nat.
Proof.
  intros A c. induction l as [|a l IH]; cbn [fold_right length]; [lia|].
  rewrite IH. lia.
Qed.

Lemma nfold_three : forall (A : Type) (g1 g2 g3 : A -> nat) (l : list A),
  fold_right (fun x acc => (g1 x + g2 x + g3 x + acc)%nat) 0%nat l
  = (fold_right (fun x acc => (g1 x + acc)%nat) 0%nat l
     + fold_right (fun x acc => (g2 x + acc)%nat) 0%nat l
     + fold_right (fun x acc => (g3 x + acc)%nat) 0%nat l)%nat.
Proof.
  intros A g1 g2 g3. induction l as [|a l IH]; cbn [fold_right]; [reflexivity|].
  rewrite IH. lia.
Qed.

Lemma gen132_pairs132_perm : forall m, Permutation (gen132 (S m)) (pairs132 m).
Proof.
  intro m. apply NoDup_Permutation;
    [apply gen132_nodup | apply pairs132_nodup |].
  intro w. split; [apply pairs132_complete | apply pairs132_sound].
Qed.

Lemma nfold_pairs132 : forall m (F : list nat -> nat),
  fold_right (fun w acc => (F w + acc)%nat) 0%nat (gen132 (S m))
  = fold_right (fun k acc =>
      (fold_right (fun a acc' =>
         (fold_right (fun v acc'' => (F (midmax a v) + acc'')%nat) 0%nat
                     (gen132 (m - k)) + acc')%nat) 0%nat (gen132 k)
       + acc)%nat) 0%nat (seq 0 (S m)).
Proof.
  intros m F.
  rewrite (nfold_perm (list nat) F (gen132 (S m)) (pairs132 m)
             (gen132_pairs132_perm m)).
  unfold pairs132.
  rewrite (nfold_flat_map nat (list nat) F
             (fun k => flat_map (fun u => map (midmax u) (gen132 (m - k)))
                                (gen132 k)) (seq 0 (S m))).
  apply nfold_ext_in. intros k _.
  rewrite (nfold_flat_map (list nat) (list nat) F
             (fun u => map (midmax u) (gen132 (m - k))) (gen132 k)).
  apply nfold_ext_in. intros a _.
  apply (nfold_map_gen (list nat) (list nat) F (midmax a) (gen132 (m - k))).
Qed.

Definition Ltot (M : nat) : nat :=
  fold_right (fun u acc => (Lsum u M + acc)%nat) 0%nat (gen132 M).

Definition sctot (M : nat) : nat :=
  fold_right (fun u acc => (length (filter (safeb u) (seq 1 M)) + acc)%nat)
             0%nat (gen132 M).

Lemma sctot_card : forall M, card132 (S M) = (card132 M + sctot M)%nat.
Proof.
  intro M. rewrite card132_recurrence.
  transitivity (fold_right (fun u acc =>
      (1 + length (filter (safeb u) (seq 1 M)) + acc)%nat) 0%nat (gen132 M)).
  - apply nfold_ext_in. intros u _. rewrite safecount_head. lia.
  - rewrite (fold_add_split (list nat) (fun _ => 1)
               (fun u => length (filter (safeb u) (seq 1 M))) (gen132 M)).
    cbn beta.
    rewrite (nfold_const (list nat) 1 (gen132 M)).
    unfold card132, sctot. lia.
Qed.

(* The level sum, split at the maximum. *)
Theorem Ltot_expand : forall M,
  Ltot (S M)
  = fold_right (fun k acc =>
      (card132 (M - k) * Ltot k
       + (card132 (M - k) + Ltot (M - k) + (k + 1) * sctot (M - k))
         * card132 k
       + acc)%nat) 0%nat (seq 0 (S M)).
Proof.
  intro M. unfold Ltot at 1.
  rewrite (nfold_pairs132 M (fun w => Lsum w (S M))).
  apply nfold_ext_in. intros k Hk. apply in_seq in Hk. destruct Hk as [_ Hk].
  assert (HkM : k <= M) by lia.
  transitivity (fold_right (fun a acc =>
      ((card132 (M - k) * Lsum a k
        + (card132 (M - k) + Ltot (M - k) + (k + 1) * sctot (M - k)))
       + acc)%nat) 0%nat (gen132 k)).
  - apply nfold_ext_in. intros a Ha.
    assert (Hpa0 : is_perm a k) by (apply gen132_perm; exact Ha).
    assert (Hla : length a = k) by (apply (perm_len a k); exact Hpa0).
    transitivity (fold_right (fun v acc =>
        ((1 + Lsum a k)
         + Lsum v (M - k)
         + (k + 1) * length (filter (safeb v) (seq 1 (M - k)))
         + acc)%nat) 0%nat (gen132 (M - k))).
    + apply nfold_ext_in. intros v Hv.
      assert (Hpv0 : is_perm v (M - k)) by (apply gen132_perm; exact Hv).
      assert (Hlv : length v = (M - k)%nat)
        by (apply (perm_len v (M - k)); exact Hpv0).
      assert (Hpa : is_perm a (length a)) by (rewrite Hla; exact Hpa0).
      assert (Hpv : is_perm v (length v)) by (rewrite Hlv; exact Hpv0).
      assert (K := Lsum_midmax a v Hpa Hpv).
      rewrite Hla, Hlv in K.
      rewrite (safecount_head v (M - k)) in K.
      replace (k + S (M - k)) with (S M) in K by lia.
      nia.
    + rewrite (nfold_three (list nat)
                 (fun _ : list nat => (1 + Lsum a k)%nat)
                 (fun v => Lsum v (M - k))
                 (fun v => ((k + 1)
                            * length (filter (safeb v) (seq 1 (M - k))))%nat)
                 (gen132 (M - k))).
      cbn beta.
      rewrite (nfold_const (list nat) (1 + Lsum a k) (gen132 (M - k))).
      rewrite (nfold_scal (list nat) (k + 1)
                 (fun v => length (filter (safeb v) (seq 1 (M - k))))
                 (gen132 (M - k))).
      unfold Ltot, sctot, card132. nia.
  - rewrite (fold_add_split (list nat)
               (fun a => (card132 (M - k) * Lsum a k)%nat)
               (fun _ : list nat =>
                  (card132 (M - k) + Ltot (M - k)
                   + (k + 1) * sctot (M - k))%nat)
               (gen132 k)).
    cbn beta.
    rewrite (nfold_scal (list nat) (card132 (M - k))
               (fun a => Lsum a k) (gen132 k)).
    rewrite (nfold_const (list nat)
               (card132 (M - k) + Ltot (M - k) + (k + 1) * sctot (M - k))
               (gen132 k)).
    unfold Ltot, card132. nia.
Qed.

(* ------------------------------------------------------------------ *)
(* The convolution the expansion runs into.  Aconv is the 4-against-Catalan
   convolution, which obeys the two-term law outright. *)

Definition Aconv (M : nat) : nat :=
  fold_right (fun k acc => (4 ^ k * card132 (M - k) + acc)%nat) 0%nat
             (seq 0 (S M)).

Lemma nfold_single : forall (A : Type) (g : A -> nat) (a : A),
  fold_right (fun x acc => (g x + acc)%nat) 0%nat (a :: nil) = g a.
Proof. intros A g a. cbn [fold_right]. lia. Qed.

Lemma nfold_four : forall (A : Type) (g1 g2 g3 g4 : A -> nat) (l : list A),
  fold_right (fun x acc => (g1 x + g2 x + g3 x + g4 x + acc)%nat) 0%nat l
  = (fold_right (fun x acc => (g1 x + acc)%nat) 0%nat l
     + fold_right (fun x acc => (g2 x + acc)%nat) 0%nat l
     + fold_right (fun x acc => (g3 x + acc)%nat) 0%nat l
     + fold_right (fun x acc => (g4 x + acc)%nat) 0%nat l)%nat.
Proof.
  intros A g1 g2 g3 g4. induction l as [|a l IH]; cbn [fold_right];
    [reflexivity|]. rewrite IH. lia.
Qed.

Lemma nfold_cons : forall (A : Type) (g : A -> nat) (a : A) (l : list A),
  fold_right (fun x acc => (g x + acc)%nat) 0%nat (a :: l)
  = (g a + fold_right (fun x acc => (g x + acc)%nat) 0%nat l)%nat.
Proof. intros A g a l. reflexivity. Qed.

Lemma Aconv_rec : forall M, Aconv (S M) = (card132 (S M) + 4 * Aconv M)%nat.
Proof.
  intro M. unfold Aconv at 1.
  change (seq 0 (S (S M))) with (0 :: seq 1 (S M)).
  rewrite (nfold_cons nat (fun k => (4 ^ k * card132 (S M - k))%nat) 0
             (seq 1 (S M))).
  cbn beta.
  replace (4 ^ 0 * card132 (S M - 0))%nat with (card132 (S M))
    by (cbn [Nat.pow]; rewrite Nat.sub_0_r; lia).
  f_equal.
  rewrite <- (seq_shift (S M) 0).
  rewrite (nfold_map_gen nat nat (fun k => (4 ^ k * card132 (S M - k))%nat) S
             (seq 0 (S M))).
  cbn beta. unfold Aconv.
  rewrite <- (nfold_scal nat 4 (fun j => (4 ^ j * card132 (M - j))%nat)
                (seq 0 (S M))).
  apply nfold_ext_in. intros j _. cbn [Nat.pow Nat.sub]. ring.
Qed.

Lemma Aconv_closed : forall M,
  (2 * Aconv M + binomN (2 * S M) (S M) = 4 ^ S M)%nat.
Proof.
  induction M as [|M IH]; [vm_compute; reflexivity|].
  rewrite (Aconv_rec M).
  assert (Hc := central_step (S M)).
  replace (4 ^ S (S M))%nat with (4 * 4 ^ S M)%nat by (cbn [Nat.pow]; ring).
  lia.
Qed.

(* The three weighted convolutions the expansion needs. *)

Lemma conv_weight : forall n,
  fold_right (fun k acc =>
    ((k + 1) * card132 k * card132 (n - k) + acc)%nat) 0%nat (seq 0 (S n))
  = wsum S n.
Proof.
  intro n. unfold wsum. apply nfold_ext_in. intros k _. ring.
Qed.

Lemma conv_weight_rev : forall n,
  fold_right (fun k acc =>
    ((n - k + 1) * card132 k * card132 (n - k) + acc)%nat) 0%nat (seq 0 (S n))
  = wsum S n.
Proof.
  intro n. rewrite <- (conv_weight n).
  transitivity (fold_right (fun k acc =>
    (((fun j => ((j + 1) * card132 j * card132 (n - j))%nat) (n - k)) + acc)%nat)
    0%nat (seq 0 (S n))).
  - apply nfold_ext_in. intros k Hk. apply in_seq in Hk. destruct Hk as [_ Hk].
    cbn beta. replace (n - (n - k))%nat with k by lia. ring.
  - apply (nfold_rev_seq (fun j => ((j + 1) * card132 j * card132 (n - j))%nat) n).
Qed.

Lemma conv_pow_rev : forall n,
  fold_right (fun k acc => (card132 k * 4 ^ (n - k) + acc)%nat) 0%nat
             (seq 0 (S n))
  = Aconv n.
Proof.
  intro n. unfold Aconv.
  transitivity (fold_right (fun k acc =>
    (((fun j => (4 ^ j * card132 (n - j))%nat) (n - k)) + acc)%nat)
    0%nat (seq 0 (S n))).
  - apply nfold_ext_in. intros k Hk. apply in_seq in Hk. destruct Hk as [_ Hk].
    cbn beta. replace (n - (n - k))%nat with k by lia. ring.
  - apply (nfold_rev_seq (fun j => (4 ^ j * card132 (n - j))%nat) n).
Qed.

Lemma conv_shift : forall n,
  (fold_right (fun k acc =>
     ((k + 1) * card132 k * card132 (S (n - k)) + acc)%nat) 0%nat (seq 0 (S n))
   + (n + 2) * card132 (S n))%nat
  = wsum S (S n).
Proof.
  intro n. unfold wsum. rewrite (seq_snoc (S n) 0).
  rewrite (nfold_app nat
             (fun k => (S k * (card132 k * card132 (S n - k)))%nat)).
  rewrite (nfold_single nat
             (fun k => (S k * (card132 k * card132 (S n - k)))%nat) (0 + S n)).
  f_equal.
  - apply nfold_ext_in. intros k Hk. apply in_seq in Hk. destruct Hk as [_ Hk].
    replace (S n - k)%nat with (S (n - k)) by lia. ring.
  - cbn beta. replace (0 + S n)%nat with (S n) by lia.
    rewrite Nat.sub_diag. change (card132 0) with 1%nat. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* The level sum in closed form. *)

Lemma Ltot_step : forall n,
  (forall j, j <= n -> (2 * Ltot j + binomN (2 * j) j = 4 ^ j)%nat) ->
  Ltot (S n) = Aconv n.
Proof.
  intros n IH.
  assert (Key :
    (2 * fold_right (fun k acc =>
        (card132 (n - k) * Ltot k
         + (card132 (n - k) + Ltot (n - k) + (k + 1) * sctot (n - k))
           * card132 k + acc)%nat) 0%nat (seq 0 (S n))
     + 3 * fold_right (fun k acc =>
        ((k + 1) * card132 k * card132 (n - k) + acc)%nat) 0%nat (seq 0 (S n))
     + fold_right (fun k acc =>
        ((n - k + 1) * card132 k * card132 (n - k) + acc)%nat) 0%nat
        (seq 0 (S n))
     = fold_right (fun k acc => (4 ^ k * card132 (n - k) + acc)%nat) 0%nat
                  (seq 0 (S n))
       + fold_right (fun k acc => (card132 k * 4 ^ (n - k) + acc)%nat) 0%nat
                    (seq 0 (S n))
       + 2 * fold_right (fun k acc =>
           (card132 k * card132 (n - k) + acc)%nat) 0%nat (seq 0 (S n))
       + 2 * fold_right (fun k acc =>
           ((k + 1) * card132 k * card132 (S (n - k)) + acc)%nat) 0%nat
           (seq 0 (S n)))%nat).
  { rewrite <- (nfold_scal nat 2 (fun k =>
        (card132 (n - k) * Ltot k
         + (card132 (n - k) + Ltot (n - k) + (k + 1) * sctot (n - k))
           * card132 k)%nat) (seq 0 (S n))).
    rewrite <- (nfold_scal nat 3 (fun k =>
        ((k + 1) * card132 k * card132 (n - k))%nat) (seq 0 (S n))).
    rewrite <- (nfold_scal nat 2 (fun k =>
        (card132 k * card132 (n - k))%nat) (seq 0 (S n))).
    rewrite <- (nfold_scal nat 2 (fun k =>
        ((k + 1) * card132 k * card132 (S (n - k)))%nat) (seq 0 (S n))).
    rewrite <- (nfold_three nat
        (fun k => (2 * (card132 (n - k) * Ltot k
                        + (card132 (n - k) + Ltot (n - k)
                           + (k + 1) * sctot (n - k)) * card132 k))%nat)
        (fun k => (3 * ((k + 1) * card132 k * card132 (n - k)))%nat)
        (fun k => ((n - k + 1) * card132 k * card132 (n - k))%nat)
        (seq 0 (S n))).
    rewrite <- (nfold_four nat
        (fun k => (4 ^ k * card132 (n - k))%nat)
        (fun k => (card132 k * 4 ^ (n - k))%nat)
        (fun k => (2 * (card132 k * card132 (n - k)))%nat)
        (fun k => (2 * ((k + 1) * card132 k * card132 (S (n - k))))%nat)
        (seq 0 (S n))).
    apply nfold_ext_in. intros k Hk. apply in_seq in Hk.
    destruct Hk as [_ Hkn].
    assert (HkleN : k <= n) by lia.
    assert (Hjle : n - k <= n) by lia.
    assert (H1 := IH k HkleN).
    assert (H2 := IH (n - k) Hjle).
    rewrite <- (card132_binom k) in H1.
    rewrite <- (card132_binom (n - k)) in H2.
    rewrite (sctot_card (n - k)).
    rewrite <- H1, <- H2.
    remember (n - k) as j eqn:Hj. clear Hj.
    ring. }
  rewrite <- (Ltot_expand n) in Key.
  rewrite (conv_weight n), (conv_weight_rev n), (conv_pow_rev n) in Key.
  change (fold_right (fun k acc => (4 ^ k * card132 (n - k) + acc)%nat) 0%nat
                     (seq 0 (S n))) with (Aconv n) in Key.
  rewrite <- (card132_convolution n) in Key.
  assert (H6 := conv_shift n).
  assert (W1 := wsum_S_sym n).
  assert (W2 := wsum_S_sym (S n)).
  assert (R := card132_ratio (S n)).
  nia.
Qed.

Theorem Ltot_closed_upto : forall N M, M <= N ->
  (2 * Ltot M + binomN (2 * M) M = 4 ^ M)%nat.
Proof.
  induction N as [|N IHN]; intros M HM.
  - assert (E : M = 0) by lia. subst M. vm_compute. reflexivity.
  - destruct (le_lt_dec M N) as [H|H]; [apply IHN; exact H|].
    assert (EM : M = S N) by lia. subst M.
    rewrite (Ltot_step N (fun j Hj => IHN j Hj)).
    apply Aconv_closed.
Qed.

Theorem Ltot_closed : forall M,
  (2 * Ltot M + binomN (2 * M) M = 4 ^ M)%nat.
Proof. intro M. apply (Ltot_closed_upto M M). lia. Qed.

(* ------------------------------------------------------------------ *)
(* Back to the diagonal.  Each word contributes two more than H at every
   letter, so the level total is the triangular number, the class size and the
   level sum; against Ddiag_two that leaves the increasing fibre. *)

Definition tri (M : nat) : nat :=
  fold_right (fun y acc => (y + acc)%nat) 0%nat (seq 0 (S M)).

Lemma nfold_seq_snoc : forall (g : nat -> nat) m,
  fold_right (fun y acc => (g y + acc)%nat) 0%nat (seq 0 (S m))
  = (fold_right (fun y acc => (g y + acc)%nat) 0%nat (seq 0 m) + g m)%nat.
Proof.
  intros g m. rewrite (seq_snoc m 0).
  rewrite (nfold_app nat g (seq 0 m) ((0 + m)%nat :: nil)).
  rewrite (nfold_single nat g (0 + m)).
  replace (0 + m)%nat with m by lia. reflexivity.
Qed.

Lemma tri_val : forall M, (2 * tri M = M * (M + 1))%nat.
Proof.
  induction M as [|M IH]; [reflexivity|].
  unfold tri. rewrite (nfold_seq_snoc (fun y => y) (S M)).
  cbn beta. unfold tri in IH. nia.
Qed.

Lemma binom_tri : forall M, binomN (M + 2) 2 = (S M + tri M)%nat.
Proof.
  intro M.
  assert (H1 : (2 * binomN (S (M + 1)) 2 = S (M + 1) * (M + 1))%nat)
    by apply binomN_two_val.
  assert (H2 := tri_val M).
  replace (M + 2)%nat with (S (M + 1)) by lia.
  nia.
Qed.

Lemma Hu_split : forall u M y, y <= M -> Hu u M y = (y + hgap u M y)%nat.
Proof. intros u M y H. unfold hgap. assert (K := Hu_ge u M y H). lia. Qed.

Lemma level_sum_word : forall u M,
  fold_right (fun y acc => (S (S (Hu u M y)) + acc)%nat) 0%nat (seq 0 (S M))
  = (2 * S M + tri M + Lsum u M)%nat.
Proof.
  intros u M.
  transitivity (fold_right (fun y acc =>
      ((2 + y) + hgap u M y + acc)%nat) 0%nat (seq 0 (S M))).
  - apply nfold_ext_in. intros y Hy. apply in_seq in Hy.
    rewrite (Hu_split u M y ltac:(lia)). lia.
  - rewrite (fold_add_split nat (fun y => (2 + y)%nat) (hgap u M)
               (seq 0 (S M))).
    cbn beta. unfold Lsum. f_equal.
    rewrite (fold_add_split nat (fun _ : nat => 2) (fun y => y)
               (seq 0 (S M))).
    cbn beta.
    rewrite (nfold_const nat 2 (seq 0 (S M))), length_seq.
    unfold tri. lia.
Qed.

Theorem Ddiag_two_L : forall M,
  Ddiag 2 M = (card132 M * (S M + binomN (M + 2) 2) + Ltot M)%nat.
Proof.
  intro M. rewrite (Ddiag_two_H M).
  transitivity (fold_right (fun u acc =>
      ((S M + binomN (M + 2) 2) + Lsum u M + acc)%nat) 0%nat (gen132 M)).
  - apply nfold_ext_in. intros u _.
    rewrite (level_sum_word u M), (binom_tri M). lia.
  - rewrite (fold_add_split (list nat)
               (fun _ : list nat => (S M + binomN (M + 2) 2)%nat)
               (fun u => Lsum u M) (gen132 M)).
    cbn beta.
    rewrite (nfold_const (list nat) (S M + binomN (M + 2) 2) (gen132 M)).
    unfold Ltot, card132. nia.
Qed.

(* The increasing fibre of the d = 2 diagonal, in closed form. *)
Theorem nsig_two_closed : NSIG_TWO_CLOSED.
Proof.
  intro M.
  assert (H1 := Ddiag_two M).
  assert (H2 := Ddiag_two_L M).
  assert (H3 := Ltot_closed M).
  assert (H4 := card132_binom M).
  nia.
Qed.

(* Hence the d = 2 diagonal outright, with the record no longer hypothetical. *)
Definition diagonal_two_closed : Diagonal 2 := diagonal_two_fib nsig_two_closed.

Theorem Ddiag_two_val : forall M,
  (2 * Ddiag 2 M = (M + 3) * binomN (2 * M) M + 4 ^ M)%nat.
Proof. intro M. apply Ddiag_two_closed. apply nsig_two_closed. Qed.

Theorem nsig_two_rec : NSIG_TWO_REC.
Proof. apply nsig_two_rec_of_closed. exact nsig_two_closed. Qed.

Theorem p_lead_two_all : forall Dg : Diagonal 2,
  Qmult (Qn (factn 2)) (nth 1 (dp 2 Dg) 0%Q) == 1.
Proof. apply p_lead_two_any. exact nsig_two_closed. Qed.

Theorem R_at_minus_one_two_all : forall Dg : Diagonal 2,
  Qminus (polyQ (dp 2 Dg) 0) (polyQ (dq 2 Dg) 0) == 1.
Proof. apply R_at_minus_one_two_any. exact nsig_two_closed. Qed.

Corollary exponent_law_at_zero_two_all : forall Dg : Diagonal 2,
  Qle (Qabs (rcoef 2 Dg 0)) (Qmult 1 (Qn (2 ^ 0))).
Proof. apply exponent_law_at_zero_two. exact nsig_two_closed. Qed.

(* ------------------------------------------------------------------ *)
(* The state of a d-letter extension, at every d.  For a permutation v the
   pair (Mu v, H v) decides the whole extension count: Mu is the number of
   legal letters less one, and both components transition exactly under ext.
   The intervals [t, H t] are laminar, which is the tree carrying the state. *)

Lemma Hu_laminar : forall u n y z,
  y <= z -> z <= Hu u n y -> Hu u n z <= Hu u n y.
Proof.
  intros u n y z Hyz Hzh.
  destruct (Hu_wit u n y) as [E|E].
  - rewrite E. apply Hu_le_cap.
  - apply Hu_le_in.
    apply in_hvals in E. destruct E as [i [j [Hij [Hj [Hi [Hyj Hn]]]]]].
    apply in_hvals. exists i, j. repeat split; lia.
Qed.

Lemma nth_ext_lo : forall v z i, i < length v ->
  nth i (ext v z) 0 = bump z (nth i v 0).
Proof.
  intros v z i H. unfold ext.
  rewrite nth_app1 by (rewrite len_map; exact H).
  apply nth_map_in. exact H.
Qed.

Lemma nth_ext_hi : forall v z, nth (length v) (ext v z) 0 = z.
Proof.
  intros v z. unfold ext.
  replace (length v) with (length (map (bump z) v)) by apply len_map.
  apply nth_last.
Qed.

Lemma bump_ge : forall z x, x <= bump z x.
Proof. intros z x. unfold bump. destruct (Nat.leb_spec z x); lia. Qed.

Lemma bump_le_mono : forall z a b, a <= b -> bump z a <= bump z b.
Proof.
  intros z a b H. unfold bump.
  destruct (Nat.leb_spec z a); destruct (Nat.leb_spec z b); lia.
Qed.

Lemma bump_at_cap : forall z n, z <= n -> bump z n = S n.
Proof. intros z n H. unfold bump. destruct (Nat.leb_spec z n); lia. Qed.

Lemma bump_ge_iff : forall z x, z <= bump z x <-> z <= x.
Proof. intros z x. unfold bump. destruct (Nat.leb_spec z x); lia. Qed.

(* Below the insertion point a threshold does not see the bump; above it the
   threshold shifts by one. *)

Lemma bump_lt_below : forall z x t, t <= z -> (bump z x < t <-> x < t).
Proof. intros z x t H. unfold bump. destruct (Nat.leb_spec z x); lia. Qed.

Lemma bump_ge_below : forall z x t, t <= z -> (t <= bump z x <-> t <= x).
Proof. intros z x t H. unfold bump. destruct (Nat.leb_spec z x); lia. Qed.

Lemma bump_lt_above : forall z x t, z < t -> (bump z x < t <-> x < t - 1).
Proof. intros z x t H. unfold bump. destruct (Nat.leb_spec z x); lia. Qed.

Lemma bump_ge_above : forall z x t, z < t -> (t <= bump z x <-> t - 1 <= x).
Proof. intros z x t H. unfold bump. destruct (Nat.leb_spec z x); lia. Qed.

Lemma hvals_ext_lo : forall v z t w,
  is_perm v (length v) -> z <= length v -> 1 <= t -> t <= z ->
  (In w (hvals (ext v z) t)
   <-> (w = z \/ exists w', In w' (hvals v t) /\ w = bump z w')).
Proof.
  intros v z t w Hp Hzn Ht1 Htz.
  assert (Hzero : exists i, i < length v /\ nth i v 0 = 0).
  { assert (Hin : In 0 v) by (apply (perm_full v (length v) Hp); lia).
    apply In_nth with (d := 0) in Hin. destruct Hin as [i [Hi Hn]].
    exists i. split; [exact Hi | exact Hn]. }
  destruct Hzero as [i0 [Hi0 Hn0]].
  rewrite in_hvals. split.
  - intros [i [j [Hij [Hj [Hi [Hyj Hn]]]]]].
    rewrite ext_length in Hj.
    destruct (Nat.eq_dec j (length v)) as [Ej|Ej].
    + left. rewrite Ej, nth_ext_hi in Hn. lia.
    + right.
      assert (Hjv : j < length v) by lia.
      rewrite (nth_ext_lo v z i ltac:(lia)) in Hi.
      rewrite (nth_ext_lo v z j Hjv) in Hyj, Hn.
      assert (Ki : nth i v 0 < t)
        by (apply (bump_lt_below z (nth i v 0) t Htz); exact Hi).
      assert (Kj : t <= nth j v 0)
        by (apply (bump_ge_below z (nth j v 0) t Htz); exact Hyj).
      exists (nth j v 0). split; [| symmetry; exact Hn].
      apply in_hvals. exists i, j. repeat split; lia.
  - intros [Ew | [w' [Hw' Ew]]].
    + subst w. exists i0, (length v).
      rewrite (nth_ext_lo v z i0 Hi0), nth_ext_hi, ext_length, Hn0.
      assert (Ki : bump z 0 < t)
        by (apply (bump_lt_below z 0 t Htz); lia).
      repeat split; lia.
    + apply in_hvals in Hw'.
      destruct Hw' as [i [j [Hij [Hj [Hi [Hyj Hn]]]]]].
      subst w'. subst w.
      assert (Ki : bump z (nth i v 0) < t)
        by (apply (bump_lt_below z (nth i v 0) t Htz); exact Hi).
      assert (Kj : t <= bump z (nth j v 0))
        by (apply (bump_ge_below z (nth j v 0) t Htz); exact Hyj).
      exists i, j.
      rewrite (nth_ext_lo v z i ltac:(lia)), (nth_ext_lo v z j Hj), ext_length.
      repeat split; lia.
Qed.

Lemma hvals_ext_hi : forall v z t w,
  z < t ->
  (In w (hvals (ext v z) t)
   <-> exists w', In w' (hvals v (t - 1)) /\ w = bump z w').
Proof.
  intros v z t w Hzt. rewrite in_hvals. split.
  - intros [i [j [Hij [Hj [Hi [Hyj Hn]]]]]].
    rewrite ext_length in Hj.
    assert (Ej : j < length v).
    { destruct (Nat.eq_dec j (length v)) as [E|E]; [|lia].
      exfalso. rewrite E, nth_ext_hi in Hyj. lia. }
    rewrite (nth_ext_lo v z i ltac:(lia)) in Hi.
    rewrite (nth_ext_lo v z j Ej) in Hyj, Hn.
    assert (Ki : nth i v 0 < t - 1)
      by (apply (bump_lt_above z (nth i v 0) t Hzt); exact Hi).
    assert (Kj : t - 1 <= nth j v 0)
      by (apply (bump_ge_above z (nth j v 0) t Hzt); exact Hyj).
    exists (nth j v 0). split; [| symmetry; exact Hn].
    apply in_hvals. exists i, j. repeat split; lia.
  - intros [w' [Hw' Ew]].
    apply in_hvals in Hw'.
    destruct Hw' as [i [j [Hij [Hj [Hi [Hyj Hn]]]]]].
    subst w'. subst w.
    assert (Ki : bump z (nth i v 0) < t)
      by (apply (bump_lt_above z (nth i v 0) t Hzt); exact Hi).
    assert (Kj : t <= bump z (nth j v 0))
      by (apply (bump_ge_above z (nth j v 0) t Hzt); exact Hyj).
    exists i, j.
    rewrite (nth_ext_lo v z i ltac:(lia)), (nth_ext_lo v z j Hj), ext_length.
    repeat split; lia.
Qed.

(* The transition of H: unchanged below the inserted letter but clipped there,
   and shifted above it. *)

Theorem Hu_ext_zero : forall v z,
  Hu (ext v z) (S (length v)) 0 = S (length v).
Proof. intros v z. apply Hu_zero. Qed.

Theorem Hu_ext_lo : forall v z t,
  is_perm v (length v) -> z <= length v -> 1 <= t -> t <= z ->
  Hu (ext v z) (S (length v)) t = Nat.min z (Hu v (length v) t).
Proof.
  intros v z t Hp Hzn Ht1 Htz.
  assert (Hcap := Hu_le_cap v (length v) t).
  apply Hu_char.
  - lia.
  - intros s Hs.
    destruct (proj1 (hvals_ext_lo v z t s Hp Hzn Ht1 Htz) Hs)
      as [Es | [w' [Hw' Es]]].
    + lia.
    + assert (K := Hu_le_in v (length v) t w' Hw').
      assert (Q := bump_ge z w'). lia.
  - destruct (Nat.le_gt_cases z (Hu v (length v) t)) as [K|K].
    + rewrite (Nat.min_l z _ K). right.
      apply (hvals_ext_lo v z t z Hp Hzn Ht1 Htz). left. reflexivity.
    + rewrite (Nat.min_r z (Hu v (length v) t) ltac:(lia)). right.
      apply (hvals_ext_lo v z t (Hu v (length v) t) Hp Hzn Ht1 Htz).
      destruct (Hu_wit v (length v) t) as [E|E]; [exfalso; lia|].
      right. exists (Hu v (length v) t). split; [exact E|].
      unfold bump. destruct (Nat.leb_spec z (Hu v (length v) t)); lia.
Qed.

Theorem Hu_ext_hi : forall v z t,
  z <= length v -> z < t -> t <= S (length v) ->
  Hu (ext v z) (S (length v)) t = bump z (Hu v (length v) (t - 1)).
Proof.
  intros v z t Hzn Hzt Htn.
  assert (Hcap := Hu_le_cap v (length v) (t - 1)).
  apply Hu_char.
  - assert (K := bump_le_mono z (Hu v (length v) (t - 1)) (length v) Hcap).
    rewrite (bump_at_cap z (length v) Hzn) in K. exact K.
  - intros s Hs.
    destruct (proj1 (hvals_ext_hi v z t s Hzt) Hs) as [w' [Hw' Es]].
    assert (K := Hu_le_in v (length v) (t - 1) w' Hw').
    rewrite Es. apply bump_le_mono. exact K.
  - destruct (Hu_wit v (length v) (t - 1)) as [E|E].
    + left. rewrite E. apply bump_at_cap. exact Hzn.
    + right. apply (hvals_ext_hi v z t _ Hzt).
      exists (Hu v (length v) (t - 1)). split; [exact E | reflexivity].
Qed.

(* The transition of mu.  The profile of an ext is the bumped union of the old
   profile with the high set at the inserted letter. *)

Lemma after_hvals : forall u z w, after u z w <-> In w (hvals u z).
Proof.
  intros u z w. unfold after. rewrite in_hvals. split.
  - intros [Hzw [j [Hj [Hn [i [Hij Hi]]]]]].
    exists i, j. repeat split; lia.
  - intros [i [j [Hij [Hj [Hi [Hzj Hn]]]]]].
    split; [lia|]. exists j. split; [exact Hj | split; [exact Hn|]].
    exists i. split; [exact Hij | exact Hi].
Qed.

Lemma hvals_map_bump_at : forall v z w,
  In w (hvals (map (bump z) v) z)
  <-> exists w', In w' (hvals v z) /\ w = bump z w'.
Proof.
  intros v z w. rewrite in_hvals. split.
  - intros [i [j [Hij [Hj [Hi [Hzj Hn]]]]]].
    rewrite len_map in Hj.
    rewrite (nth_map_in (bump z) v i ltac:(lia)) in Hi.
    rewrite (nth_map_in (bump z) v j Hj) in Hzj, Hn.
    assert (Ki : nth i v 0 < z)
      by (apply (bump_lt_v z (nth i v 0)); exact Hi).
    assert (Kj : z <= nth j v 0)
      by (apply (bump_ge_iff z (nth j v 0)); exact Hzj).
    exists (nth j v 0). split; [| symmetry; exact Hn].
    apply in_hvals. exists i, j. repeat split; lia.
  - intros [w' [Hw' Ew]].
    apply in_hvals in Hw'.
    destruct Hw' as [i [j [Hij [Hj [Hi [Hzj Hn]]]]]].
    subst w'. subst w.
    assert (Ki : bump z (nth i v 0) < z)
      by (apply (bump_lt_v z (nth i v 0)); exact Hi).
    assert (Kj : z <= bump z (nth j v 0))
      by (apply (bump_ge_iff z (nth j v 0)); exact Hzj).
    exists i, j. rewrite len_map.
    rewrite (nth_map_in (bump z) v i ltac:(lia)).
    rewrite (nth_map_in (bump z) v j Hj).
    repeat split; lia.
Qed.

Theorem three_value_ext_gen : forall v z w,
  three_value (ext v z) w
  <-> exists w', (three_value v w' \/ In w' (hvals v z)) /\ w = bump z w'.
Proof.
  intros v z w. unfold ext.
  rewrite (three_values_append (map (bump z) v) z w). split.
  - intros [K | K].
    + apply (three_value_map_bump z v w) in K. destruct K as [Hne Ht].
      exists (unbump z w). split; [left; exact Ht|].
      symmetry. apply bump_unbump. exact Hne.
    + assert (K2 : new_three (map (bump z) v) z w) by exact K.
      apply new_three_after in K2. destruct K2 as [Haf _].
      apply after_hvals in Haf.
      apply hvals_map_bump_at in Haf. destruct Haf as [w' [Hw' Ew]].
      exists w'. split; [right; exact Hw' | exact Ew].
  - intros [w' [[K | K] Ew]].
    + left. apply (three_value_map_bump z v w). split.
      * rewrite Ew. apply bump_ne.
      * rewrite Ew, unbump_bump. exact K.
    + right. apply new_three_after. split.
      * apply after_hvals. apply hvals_map_bump_at.
        exists w'. split; [exact K | exact Ew].
      * assert (Hge : z <= w') by (apply (hvals_ge v z w'); exact K).
        rewrite Ew. apply (bump_gt_v z w'). exact Hge.
Qed.

Definition Mu (v : list nat) (n : nat) : nat :=
  match mub v with None => n | Some d => Nat.min d n end.

Lemma mucount_Mu : forall v n, mucount v n = S (Mu v n).
Proof. intros v n. unfold mucount, Mu. destruct (mub v); reflexivity. Qed.

Lemma Mu_le_cap : forall v n, Mu v n <= n.
Proof. intros v n. unfold Mu. destruct (mub v); lia. Qed.

Lemma Mu_le_in : forall v n w, three_value v w -> Mu v n <= w.
Proof.
  intros v n w H. unfold Mu. destruct (mub v) as [d|] eqn:E.
  - assert (K := mub_is_mu v d E). destruct K as [_ Hl].
    assert (Q := Hl w H). lia.
  - exfalso.
    exact (proj1 (profile_empty_iff v) (mub_none_132free v E) w H).
Qed.

Lemma Mu_wit : forall v n, Mu v n = n \/ three_value v (Mu v n).
Proof.
  intros v n. unfold Mu. destruct (mub v) as [d|] eqn:E; [|left; reflexivity].
  assert (K := mub_is_mu v d E). destruct K as [Hd _].
  destruct (Nat.min_dec d n) as [M|M]; rewrite M;
    [right; exact Hd | left; reflexivity].
Qed.

Lemma Mu_char : forall v n x,
  x <= n -> (forall w, three_value v w -> x <= w) ->
  (x = n \/ three_value v x) -> Mu v n = x.
Proof.
  intros v n x Hx Hmin Hw.
  assert (H1 : Mu v n <= x).
  { destruct Hw as [E|E]; [subst x; apply Mu_le_cap | apply Mu_le_in; exact E]. }
  assert (H2 : x <= Mu v n).
  { destruct (Mu_wit v n) as [E|E]; [rewrite E; exact Hx | apply Hmin; exact E]. }
  lia.
Qed.

Theorem Mu_ext : forall v z n,
  is_perm v n -> z <= n ->
  Mu (ext v z) (S n) = bump z (Nat.min (Mu v n) (Hu v n z)).
Proof.
  intros v z n Hp Hzn.
  assert (HM := Mu_le_cap v n).
  assert (HH := Hu_le_cap v n z).
  apply Mu_char.
  - assert (K := bump_le_mono z (Nat.min (Mu v n) (Hu v n z)) n ltac:(lia)).
    rewrite (bump_at_cap z n Hzn) in K. exact K.
  - intros w Hw.
    apply three_value_ext_gen in Hw. destruct Hw as [w' [[K|K] Ew]].
    + assert (Q := Mu_le_in v n w' K). rewrite Ew.
      apply bump_le_mono. lia.
    + assert (Q : Hu v n z <= w') by (apply Hu_le_in; exact K).
      rewrite Ew. apply bump_le_mono. lia.
  - destruct (Nat.le_ge_cases (Mu v n) (Hu v n z)) as [K|K].
    + rewrite (Nat.min_l _ _ K).
      destruct (Mu_wit v n) as [E|E].
      * left. rewrite E. apply bump_at_cap. exact Hzn.
      * right. apply three_value_ext_gen.
        exists (Mu v n). split; [left; exact E | reflexivity].
    + rewrite (Nat.min_r _ _ K).
      destruct (Hu_wit v n z) as [E|E].
      * left. rewrite E. apply bump_at_cap. exact Hzn.
      * right. apply three_value_ext_gen.
        exists (Hu v n z). split; [right; exact E | reflexivity].
Qed.

(* The legal-letter count, in state terms. *)
Corollary mucount_ext_state : forall v z n,
  is_perm v n -> z <= n -> z <= Mu v n ->
  mucount (ext v z) (S n) = S (S (Nat.min (Mu v n) (Hu v n z))).
Proof.
  intros v z n Hp Hzn Hzm.
  rewrite mucount_Mu, (Mu_ext v z n Hp Hzn).
  assert (HH : z <= Hu v n z) by (apply Hu_ge; exact Hzn).
  f_equal. unfold bump.
  destruct (Nat.leb_spec z (Nat.min (Mu v n) (Hu v n z))); lia.
Qed.

(* Peeling an extension from the front, so the transfer runs letter by letter
   from the 132-free prefix outward. *)

Theorem extend_front : forall u m k,
  extend u m (S k) = flat_map (fun v => extend v (S m) k) (extend u m 1).
Proof.
  intros u m k. revert u m. induction k as [|k IH]; intros u m.
  - transitivity (flat_map (fun x : list nat => x :: nil) (extend u m 1)).
    + symmetry. apply flat_map_singleton.
    + apply flat_map_ext_in. intros v _. reflexivity.
  - change (extend u m (S (S k)))
      with (flat_map (fun v => map (ext v)
                       (filter (legalb v) (seq 0 (S (m + S k)))))
                     (extend u m (S k))).
    rewrite (IH u m), flat_map_assoc.
    apply flat_map_ext_in. intros v _.
    change (extend v (S m) (S k))
      with (flat_map (fun v' => map (ext v')
                       (filter (legalb v') (seq 0 (S (S m + k)))))
                     (extend v (S m) k)).
    replace (S m + k) with (m + S k) by lia. reflexivity.
Qed.

Corollary extend_front_len : forall M u k, In u (gen132 M) ->
  length (extend u M (S k))
  = fold_right (fun y acc => (length (extend (ext u y) (S M) k) + acc)%nat)
               0%nat (seq 0 (S M)).
Proof.
  intros M u k Hu.
  rewrite (extend_front u M k), length_flat_map_gen, (extend_one_eq M u Hu).
  apply (nfold_map_gen nat (list nat) (fun v => length (extend v (S M) k))
           (ext u) (seq 0 (S M))).
Qed.

Corollary Ddiag_front : forall d M,
  Ddiag (S d) M
  = fold_right (fun u acc =>
      (fold_right (fun y acc' =>
         (length (extend (ext u y) (S M) d) + acc')%nat) 0%nat (seq 0 (S M))
       + acc)%nat) 0%nat (gen132 M).
Proof.
  intros d M. rewrite (Ddiag_extend (S d) M).
  apply nfold_ext_in. intros u Hu. apply extend_front_len. exact Hu.
Qed.

(* ------------------------------------------------------------------ *)
(* The extension count read off the state.  The legal letters at a word are an
   initial segment of the alphabet cut at Mu, so a one-letter extension is a
   segment and a two-letter one is a sum over that segment of the next Mu. *)

Lemma Mu_free : forall u n, ~ contains_132 u -> Mu u n = n.
Proof.
  intros u n H. unfold Mu. destruct (mub u) as [d|] eqn:E; [|reflexivity].
  exfalso. assert (K := mub_is_mu u d E). destruct K as [Hd _].
  exact (proj1 (profile_empty_iff u) H d Hd).
Qed.

Lemma filter_legalb_count : forall v n, ~ contains_1324 v ->
  length (filter (legalb v) (seq 0 (S n))) = mucount v n.
Proof.
  intros v n Hav. unfold mucount. destruct (mub v) as [d|] eqn:E.
  - apply (fibre_count v n d Hav). apply mub_is_mu. exact E.
  - apply fibre_count_free. apply mub_none_132free. exact E.
Qed.

Lemma legal_iff_le_Mu : forall v n y, ~ contains_1324 v -> y <= n ->
  (legal v y <-> y <= Mu v n).
Proof.
  intros v n y Hav Hyn. unfold Mu. destruct (mub v) as [d|] eqn:E.
  - assert (Hmu : is_mu v d) by (apply mub_is_mu; exact E).
    rewrite (legal_iff_le_mu v d Hav Hmu y). lia.
  - split; [intros _; lia | intros _].
    apply legal_all_when_132_free. apply mub_none_132free. exact E.
Qed.

Lemma filter_leb_seq : forall N K, K < N ->
  filter (fun y => Nat.leb y K) (seq 0 N) = seq 0 (S K).
Proof.
  induction N as [|N IH]; intros K H; [lia|].
  rewrite (seq_snoc N 0), filter_app, Nat.add_0_l.
  destruct (Nat.eq_dec K N) as [E|E].
  - subst K. rewrite (filter_all_gen nat (fun y => Nat.leb y N) (seq 0 N)).
    + cbn [filter]. rewrite Nat.leb_refl.
      rewrite (seq_snoc N 0), Nat.add_0_l. reflexivity.
    + intros y Hy. apply in_seq in Hy. apply Nat.leb_le. lia.
  - rewrite (IH K ltac:(lia)). cbn [filter].
    assert (Hf : Nat.leb N K = false) by (apply Nat.leb_gt; lia).
    rewrite Hf, app_nil_r. reflexivity.
Qed.

Lemma filter_legalb_seq : forall v n, ~ contains_1324 v ->
  filter (legalb v) (seq 0 (S n)) = seq 0 (S (Mu v n)).
Proof.
  intros v n Hav.
  assert (HM := Mu_le_cap v n).
  rewrite (filter_ext_in_nat (legalb v) (fun y => Nat.leb y (Mu v n))
             (seq 0 (S n))).
  - apply filter_leb_seq. lia.
  - intros y Hy. apply in_seq in Hy.
    destruct (legalb v y) eqn:El.
    + symmetry. apply Nat.leb_le.
      apply (legal_iff_le_Mu v n y Hav ltac:(lia)).
      apply legalb_spec. exact El.
    + symmetry. apply Nat.leb_gt.
      destruct (Nat.le_gt_cases y (Mu v n)) as [K|K]; [exfalso | exact K].
      assert (Hl : legal v y)
        by (apply (legal_iff_le_Mu v n y Hav ltac:(lia)); exact K).
      assert (E2 : legalb v y = true) by (apply legalb_spec; exact Hl).
      rewrite El in E2. discriminate.
Qed.

Lemma extend_one_unfold : forall v n,
  extend v n 1 = map (ext v) (filter (legalb v) (seq 0 (S n))).
Proof.
  intros v n. cbn [extend flat_map]. rewrite app_nil_r, Nat.add_0_r.
  reflexivity.
Qed.

Lemma extend_one_state : forall v n, ~ contains_1324 v ->
  extend v n 1 = map (ext v) (seq 0 (S (Mu v n))).
Proof.
  intros v n Hav.
  rewrite (extend_one_unfold v n), (filter_legalb_seq v n Hav). reflexivity.
Qed.

Lemma extend_len_one : forall v n, ~ contains_1324 v ->
  length (extend v n 1) = S (Mu v n).
Proof.
  intros v n Hav.
  rewrite (extend_one_state v n Hav), len_map_gen, length_seq. reflexivity.
Qed.

Lemma ext_avoids : forall v n z, ~ contains_1324 v -> z <= Mu v n -> z <= n ->
  ~ contains_1324 (ext v z).
Proof.
  intros v n z Hav Hzm Hzn.
  apply ext_legal_iff. apply (legal_iff_le_Mu v n z Hav Hzn). exact Hzm.
Qed.

Theorem extend_two_state : forall v n, is_perm v n -> ~ contains_1324 v ->
  length (extend v n 2)
  = fold_right (fun z acc =>
      (S (S (Nat.min (Mu v n) (Hu v n z))) + acc)%nat) 0%nat
      (seq 0 (S (Mu v n))).
Proof.
  intros v n Hp Hav.
  assert (HM := Mu_le_cap v n).
  change 2 with (S 1).
  rewrite (extend_front v n 1), length_flat_map_gen,
          (extend_one_state v n Hav).
  rewrite (nfold_map_gen nat (list nat)
             (fun w => length (extend w (S n) 1)) (ext v) (seq 0 (S (Mu v n)))).
  apply nfold_ext_in. intros z Hz. apply in_seq in Hz.
  assert (Hzm : z <= Mu v n) by lia.
  assert (Hzn : z <= n) by lia.
  rewrite (extend_len_one (ext v z) (S n) (ext_avoids v n z Hav Hzm Hzn)).
  rewrite <- (mucount_Mu (ext v z) (S n)).
  apply (mucount_ext_state v z n Hp Hzn Hzm).
Qed.

Lemma Mu_ext_free : forall u M y, is_perm u M -> ~ contains_132 u -> y <= M ->
  Mu (ext u y) (S M) = S (Hu u M y).
Proof.
  intros u M y Hp H132 HyM.
  rewrite (Mu_ext u y M Hp HyM), (Mu_free u M H132).
  assert (Hc := Hu_le_cap u M y).
  assert (Hg : y <= Hu u M y) by (apply Hu_ge; exact HyM).
  rewrite (Nat.min_r M (Hu u M y) Hc).
  unfold bump. destruct (Nat.leb_spec y (Hu u M y)); lia.
Qed.

(* the transitions with the length written as the alphabet size *)

Lemma Hu_ext_zero_M : forall u M y, length u = M ->
  Hu (ext u y) (S M) 0 = S M.
Proof. intros u M y H. subst M. apply Hu_ext_zero. Qed.

Lemma Hu_ext_lo_M : forall u M y z, length u = M ->
  is_perm u M -> y <= M -> 1 <= z -> z <= y ->
  Hu (ext u y) (S M) z = Nat.min y (Hu u M z).
Proof. intros u M y z HL Hp Hy Hz1 Hzy. subst M. apply Hu_ext_lo; assumption. Qed.

Lemma Hu_ext_hi_M : forall u M y z, length u = M ->
  y <= M -> y < z -> z <= S M ->
  Hu (ext u y) (S M) z = bump y (Hu u M (z - 1)).
Proof. intros u M y z HL Hy Hyz Hz. subst M. apply Hu_ext_hi; assumption. Qed.

(* ------------------------------------------------------------------ *)
(* The d = 3 diagonal through the state function.  Laminarity collapses the
   nested minima: above the inserted letter the second minimum is always the
   inner one, so the two-letter extension count is one boundary term, one sum
   over the letters below the insertion point, and one over the subtree at it. *)

Lemma seq_split_d3 : forall y h, y <= h ->
  seq 0 (S (S h)) = seq 0 1 ++ seq 1 y ++ seq (S y) (S h - y).
Proof.
  intros y h H.
  replace (S (S h)) with (1 + (y + (S h - y))) by lia.
  rewrite (seq_break 1 (y + (S h - y)) 0).
  replace (0 + 1) with 1 by lia.
  rewrite (seq_break y (S h - y) 1).
  replace (1 + y) with (S y) by lia.
  reflexivity.
Qed.

Theorem extend_two_at : forall M u y, In u (gen132 M) -> y <= M ->
  length (extend (ext u y) (S M) 2)
  = (3 + Hu u M y
     + fold_right (fun z acc => (2 + Nat.min y (Hu u M z) + acc)%nat) 0%nat
                  (seq 1 y)
     + fold_right (fun z acc => (3 + Hu u M z + acc)%nat) 0%nat
                  (seq y (S (Hu u M y - y))))%nat.
Proof.
  intros M u y Hin HyM.
  assert (Hp : is_perm u M) by (apply gen132_perm; exact Hin).
  assert (H132 : ~ contains_132 u) by (exact (gen132_av M u Hin)).
  assert (Hlu : length u = M) by (apply (perm_len u M); exact Hp).
  assert (Hc := Hu_le_cap u M y).
  assert (Hg : y <= Hu u M y) by (apply Hu_ge; exact HyM).
  assert (Hpe : is_perm (ext u y) (S M)) by (apply ext_perm; assumption).
  assert (Hae : ~ contains_1324 (ext u y))
    by (apply ext_all_legal_when_132_free; exact H132).
  rewrite (extend_two_state (ext u y) (S M) Hpe Hae).
  rewrite (Mu_ext_free u M y Hp H132 HyM).
  rewrite (seq_split_d3 y (Hu u M y) Hg).
  rewrite !(nfold_app nat (fun z =>
    S (S (Nat.min (S (Hu u M y)) (Hu (ext u y) (S M) z))))).
  assert (P1 : fold_right (fun z acc =>
      (S (S (Nat.min (S (Hu u M y)) (Hu (ext u y) (S M) z))) + acc)%nat)
      0%nat (seq 0 1) = (3 + Hu u M y)%nat).
  { cbn [seq fold_right].
    rewrite (Hu_ext_zero_M u M y Hlu).
    rewrite (Nat.min_l (S (Hu u M y)) (S M) ltac:(lia)). lia. }
  assert (P2 : fold_right (fun z acc =>
      (S (S (Nat.min (S (Hu u M y)) (Hu (ext u y) (S M) z))) + acc)%nat)
      0%nat (seq 1 y)
    = fold_right (fun z acc => (2 + Nat.min y (Hu u M z) + acc)%nat) 0%nat
                 (seq 1 y)).
  { apply nfold_ext_in. intros z Hz. apply in_seq in Hz.
    assert (Hz1 : 1 <= z) by lia.
    assert (Hzy : z <= y) by lia.
    rewrite (Hu_ext_lo_M u M y z Hlu Hp HyM Hz1 Hzy).
    assert (K : Nat.min y (Hu u M z) <= y) by lia.
    rewrite (Nat.min_r (S (Hu u M y)) (Nat.min y (Hu u M z)) ltac:(lia)). lia. }
  assert (P3 : fold_right (fun z acc =>
      (S (S (Nat.min (S (Hu u M y)) (Hu (ext u y) (S M) z))) + acc)%nat)
      0%nat (seq (S y) (S (Hu u M y) - y))
    = fold_right (fun z acc => (3 + Hu u M z + acc)%nat) 0%nat
                 (seq y (S (Hu u M y - y)))).
  { replace (S (Hu u M y) - y) with (S (Hu u M y - y)) by lia.
    rewrite <- (seq_shift (S (Hu u M y - y)) y).
    rewrite (nfold_map_gen nat nat
      (fun z => S (S (Nat.min (S (Hu u M y)) (Hu (ext u y) (S M) z)))) S
      (seq y (S (Hu u M y - y)))).
    cbn beta.
    apply nfold_ext_in. intros z Hz. apply in_seq in Hz.
    assert (Hyz : y < S z) by lia.
    assert (Hzn : S z <= S M) by lia.
    rewrite (Hu_ext_hi_M u M y (S z) Hlu HyM Hyz Hzn).
    replace (S z - 1) with z by lia.
    assert (Hzh : Hu u M z <= Hu u M y)
      by (apply (Hu_laminar u M y z); lia).
    assert (Hgz : z <= Hu u M z) by (apply Hu_ge; lia).
    assert (Eb : bump y (Hu u M z) = S (Hu u M z))
      by (unfold bump; destruct (Nat.leb_spec y (Hu u M z)); lia).
    rewrite Eb.
    rewrite (Nat.min_r (S (Hu u M y)) (S (Hu u M z)) ltac:(lia)). lia. }
  rewrite P1, P2, P3. lia.
Qed.

Theorem Ddiag_three_H : forall M,
  Ddiag 3 M
  = fold_right (fun u acc =>
      (fold_right (fun y acc' =>
         (3 + Hu u M y
          + fold_right (fun z acc'' => (2 + Nat.min y (Hu u M z) + acc'')%nat)
                       0%nat (seq 1 y)
          + fold_right (fun z acc'' => (3 + Hu u M z + acc'')%nat)
                       0%nat (seq y (S (Hu u M y - y)))
          + acc')%nat) 0%nat (seq 0 (S M))
       + acc)%nat) 0%nat (gen132 M).
Proof.
  intro M. change 3 with (S 2). rewrite (Ddiag_front 2 M).
  apply nfold_ext_in. intros u Hu.
  apply nfold_ext_in. intros y Hy. apply in_seq in Hy.
  apply extend_two_at; [exact Hu | lia].
Qed.

(* The d = 3 two-term law, in the cleared form the state sum has to reach.
   Fitted and checked against the enumerator at every size it reaches:
   p_3 = (M^2 + 11M + 21)/6 of degree 2 with leading coefficient 1/3!, and
   q_3 = (M + 5)/2 of degree 1 with leading coefficient C(3,2)/3!. *)
Definition DDIAG_THREE_CLOSED : Prop :=
  forall M, (6 * Ddiag 3 M
             = (M * M + 11 * M + 21) * binomN (2 * M) M
               + (3 * M + 15) * 4 ^ M)%nat.

Definition diagonal_three (H : DDIAG_THREE_CLOSED) : Diagonal 3.
Proof.
  refine (mkDiagonal 3
            (Qmake 21 6 :: Qmake 11 6 :: Qmake 1 6 :: nil)
            (Qmake 15 6 :: Qmake 3 6 :: nil)
            eq_refl eq_refl _).
  intro M.
  assert (K := H M).
  assert (E : Qn (6 * Ddiag 3 M)%nat == Qmult 6 (Qn (Ddiag 3 M))).
  { rewrite Qn_mul. assert (E6 : Qn 6 == 6) by (unfold Qn, Qeq; simpl; lia).
    rewrite E6. reflexivity. }
  assert (E3 : Qn 3 == 3) by (unfold Qn, Qeq; simpl; lia).
  assert (E11 : Qn 11 == 11) by (unfold Qn, Qeq; simpl; lia).
  assert (E15 : Qn 15 == 15) by (unfold Qn, Qeq; simpl; lia).
  assert (E21 : Qn 21 == 21) by (unfold Qn, Qeq; simpl; lia).
  assert (KQ : Qmult 6 (Qn (Ddiag 3 M))
               == Qplus (Qmult (Qplus (Qplus (Qmult (Qn M) (Qn M))
                                             (Qmult 11 (Qn M))) 21)
                               (Qn (binomN (2 * M) M)))
                        (Qmult (Qplus (Qmult 3 (Qn M)) 15) (Qn (4 ^ M)))).
  { rewrite <- E, K, Qn_add, !Qn_mul, !Qn_add, !Qn_mul, E3, E11, E15, E21.
    reflexivity. }
  cbn [polyQ dp dq].
  setoid_replace (Qn (Ddiag 3 M))
    with (Qdiv (Qmult 6 (Qn (Ddiag 3 M))) 6) by field.
  rewrite KQ. field.
Defined.

(* ------------------------------------------------------------------ *)
(* The d = 3 state sum, reduced to two tree statistics.  Summing the two-letter
   count over the alphabet leaves, beyond the level sum already closed, only
   the total of H over each node's subtree and the total of the clipped H over
   the nodes to its left. *)

Definition Cin (u : list nat) (M y : nat) : nat :=
  fold_right (fun z acc => (Nat.min y (Hu u M z) + acc)%nat) 0%nat (seq 1 y).

Definition Bin (u : list nat) (M y : nat) : nat :=
  fold_right (fun z acc => (Hu u M z + acc)%nat) 0%nat
             (seq y (S (Hu u M y - y))).

Definition Cw (u : list nat) (M : nat) : nat :=
  fold_right (fun y acc => (Cin u M y + acc)%nat) 0%nat (seq 0 (S M)).

Definition Bw (u : list nat) (M : nat) : nat :=
  fold_right (fun y acc => (Bin u M y + acc)%nat) 0%nat (seq 0 (S M)).

Definition Ctot (M : nat) : nat :=
  fold_right (fun u acc => (Cw u M + acc)%nat) 0%nat (gen132 M).

Definition Btot (M : nat) : nat :=
  fold_right (fun u acc => (Bw u M + acc)%nat) 0%nat (gen132 M).

Lemma nfold_five : forall (A : Type) (g1 g2 g3 g4 g5 : A -> nat) (l : list A),
  fold_right (fun x acc => (g1 x + g2 x + g3 x + g4 x + g5 x + acc)%nat) 0%nat l
  = (fold_right (fun x acc => (g1 x + acc)%nat) 0%nat l
     + fold_right (fun x acc => (g2 x + acc)%nat) 0%nat l
     + fold_right (fun x acc => (g3 x + acc)%nat) 0%nat l
     + fold_right (fun x acc => (g4 x + acc)%nat) 0%nat l
     + fold_right (fun x acc => (g5 x + acc)%nat) 0%nat l)%nat.
Proof.
  intros A g1 g2 g3 g4 g5. induction l as [|a l IH]; cbn [fold_right];
    [reflexivity|]. rewrite IH. lia.
Qed.

Lemma inner_C_split : forall u M y,
  fold_right (fun z acc => (2 + Nat.min y (Hu u M z) + acc)%nat) 0%nat (seq 1 y)
  = (2 * y + Cin u M y)%nat.
Proof.
  intros u M y. unfold Cin.
  rewrite (fold_add_split nat (fun _ : nat => 2)
             (fun z => Nat.min y (Hu u M z)) (seq 1 y)).
  cbn beta. rewrite (nfold_const nat 2 (seq 1 y)), length_seq. reflexivity.
Qed.

Lemma inner_B_split : forall u M y,
  fold_right (fun z acc => (3 + Hu u M z + acc)%nat) 0%nat
             (seq y (S (Hu u M y - y)))
  = (3 * S (Hu u M y - y) + Bin u M y)%nat.
Proof.
  intros u M y. unfold Bin.
  rewrite (fold_add_split nat (fun _ : nat => 3)
             (fun z => Hu u M z) (seq y (S (Hu u M y - y)))).
  cbn beta.
  rewrite (nfold_const nat 3 (seq y (S (Hu u M y - y)))), length_seq.
  reflexivity.
Qed.

Lemma tri_fold : forall M,
  fold_right (fun y acc => (3 * y + acc)%nat) 0%nat (seq 0 (S M))
  = (3 * tri M)%nat.
Proof.
  intro M. rewrite (nfold_scal nat 3 (fun y => y) (seq 0 (S M))).
  unfold tri. reflexivity.
Qed.

Lemma Ddiag_three_word : forall u M,
  fold_right (fun y acc =>
    (3 + Hu u M y
     + fold_right (fun z acc' => (2 + Nat.min y (Hu u M z) + acc')%nat) 0%nat
                  (seq 1 y)
     + fold_right (fun z acc' => (3 + Hu u M z + acc')%nat) 0%nat
                  (seq y (S (Hu u M y - y)))
     + acc)%nat) 0%nat (seq 0 (S M))
  = (6 * S M + 3 * tri M + 4 * Lsum u M + Cw u M + Bw u M)%nat.
Proof.
  intros u M.
  transitivity (fold_right (fun y acc =>
      (6 + 3 * y + 4 * hgap u M y + Cin u M y + Bin u M y + acc)%nat)
      0%nat (seq 0 (S M))).
  - apply nfold_ext_in. intros y Hy. apply in_seq in Hy.
    rewrite (inner_C_split u M y), (inner_B_split u M y).
    assert (Hg : y <= Hu u M y) by (apply Hu_ge; lia).
    unfold hgap. lia.
  - rewrite (nfold_five nat (fun _ : nat => 6) (fun y => 3 * y)
               (fun y => 4 * hgap u M y) (Cin u M) (Bin u M) (seq 0 (S M))).
    cbn beta.
    rewrite (nfold_const nat 6 (seq 0 (S M))), length_seq.
    rewrite (tri_fold M).
    rewrite (nfold_scal nat 4 (hgap u M) (seq 0 (S M))).
    unfold Lsum, Cw, Bw. lia.
Qed.

Theorem Ddiag_three_stats : forall M,
  Ddiag 3 M = (card132 M * (6 * S M + 3 * tri M) + 4 * Ltot M
               + Ctot M + Btot M)%nat.
Proof.
  intro M. rewrite (Ddiag_three_H M).
  transitivity (fold_right (fun u acc =>
      ((6 * S M + 3 * tri M) + 4 * Lsum u M + Cw u M + Bw u M + acc)%nat)
      0%nat (gen132 M)).
  - apply nfold_ext_in. intros u _. apply Ddiag_three_word.
  - rewrite (nfold_four (list nat)
               (fun _ : list nat => (6 * S M + 3 * tri M)%nat)
               (fun u => (4 * Lsum u M)%nat) (fun u => Cw u M) (fun u => Bw u M)
               (gen132 M)).
    cbn beta.
    rewrite (nfold_const (list nat) (6 * S M + 3 * tri M) (gen132 M)).
    rewrite (nfold_scal (list nat) 4 (fun u => Lsum u M) (gen132 M)).
    unfold Ltot, Ctot, Btot, card132. nia.
Qed.

(* The two remaining totals, fitted and checked against the enumerator at
   every size it reaches. *)

Definition BTOT_CLOSED : Prop :=
  forall M, (4 * Btot M = 4 * M * binomN (2 * M) M + M * 4 ^ M)%nat.

Definition CTOT_CLOSED : Prop :=
  forall M, (12 * Ctot M + 8 * M * binomN (2 * M) M + 6 * binomN (2 * M) M
             = 2 * M * M * binomN (2 * M) M + (3 * M + 6) * 4 ^ M)%nat.

Theorem three_of_stats : BTOT_CLOSED -> CTOT_CLOSED -> DDIAG_THREE_CLOSED.
Proof.
  intros HB HC M.
  assert (Hred := Ddiag_three_stats M).
  assert (Htri := tri_val M).
  assert (Hcat := card132_binom M).
  assert (Hlt := Ltot_closed M).
  assert (Hb := HB M).
  assert (Hc := HC M).
  nia.
Qed.

Definition diagonal_three_of_stats (HB : BTOT_CLOSED) (HC : CTOT_CLOSED)
  : Diagonal 3 := diagonal_three (three_of_stats HB HC).

(* ------------------------------------------------------------------ *)
(* The second moment of the split count.  A 132-avoider with s split points
   has children carrying 2, 3, ..., s+1 split points, one each, so summing the
   child count over the class squares the parent's, and the level totals of
   sccount^2 and of sccount(sccount - 1) close in Catalan numbers.  Those are
   the two totals the subtree statistic's max-split recursion runs into. *)

Definition scsq (m : nat) : nat :=
  fold_right (fun u acc => (sccount u m * sccount u m + acc)%nat) 0%nat
             (gen132 m).

Definition scpair (m : nat) : nat :=
  fold_right (fun u acc => ((sccount u m - 1) * sccount u m + acc)%nat) 0%nat
             (gen132 m).

Lemma seq2_sum : forall s,
  (2 * fold_right (fun j acc => (j + acc)%nat) 0%nat (seq 2 s)
   = s * s + 3 * s)%nat.
Proof.
  induction s as [|s IH]; [reflexivity|].
  rewrite (seq_snoc s 2).
  rewrite (nfold_app nat (fun j => j) (seq 2 s) ((2 + s)%nat :: nil)).
  rewrite (nfold_single nat (fun j => j) (2 + s)).
  cbn beta. nia.
Qed.

Theorem scsq_closed : forall m,
  (scsq m + 3 * card132 (S m) = 2 * card132 (S (S m)))%nat.
Proof.
  intro m.
  assert (H1 : card132 (S (S m))
               = fold_right (fun u acc =>
                   (fold_right (fun j acc' => (j + acc')%nat) 0%nat
                               (seq 2 (sccount u m)) + acc)%nat)
                   0%nat (gen132 m)).
  { rewrite (card132_sccount (S m)), (children_gen132 m).
    rewrite (nfold_flat_map (list nat) (list nat)
               (fun w => sccount w (S m)) (fun u => children u m) (gen132 m)).
    apply nfold_ext_in. intros u Hu.
    assert (Hp : is_perm u m) by (apply gen132_perm; exact Hu).
    rewrite <- (nfold_map_gen (list nat) nat (fun j => j)
                 (fun w => sccount w (S m)) (children u m)).
    apply (nfold_perm nat (fun j => j)
             (map (fun w => sccount w (S m)) (children u m))
             (seq 2 (sccount u m)) (children_sccounts u m Hp)). }
  assert (H2 : (2 * card132 (S (S m))
                = fold_right (fun u acc =>
                    (sccount u m * sccount u m + 3 * sccount u m + acc)%nat)
                    0%nat (gen132 m))%nat).
  { rewrite H1.
    rewrite <- (nfold_scal (list nat) 2
                 (fun u => fold_right (fun j acc => (j + acc)%nat) 0%nat
                                      (seq 2 (sccount u m))) (gen132 m)).
    apply nfold_ext_in. intros u _. apply seq2_sum. }
  rewrite H2.
  rewrite (fold_add_split (list nat)
             (fun u => (sccount u m * sccount u m)%nat)
             (fun u => (3 * sccount u m)%nat) (gen132 m)).
  cbn beta.
  rewrite (nfold_scal (list nat) 3 (fun u => sccount u m) (gen132 m)).
  rewrite <- (card132_sccount m).
  unfold scsq. lia.
Qed.

(* Ordered pairs of safe values, which is what the subtree statistic's
   max-split recursion counts at the split point. *)

Definition cntge (L : list nat) (y : nat) : nat :=
  length (filter (fun z => Nat.leb y z) L).

Definition pairge (L : list nat) : nat :=
  fold_right (fun y acc => (cntge L y + acc)%nat) 0%nat L.

Lemma split_at_point : forall x L, ~ In x L ->
  (length (filter (fun z => Nat.leb x z) L)
   + length (filter (fun z => Nat.leb z x) L) = length L)%nat.
Proof.
  intros x. induction L as [|a L IH]; intro H; [reflexivity|].
  cbn [filter length].
  assert (Hne : a <> x) by (intro E; apply H; left; exact E).
  assert (HL : ~ In x L) by (intro C; apply H; right; exact C).
  assert (K := IH HL).
  destruct (Nat.leb_spec x a); destruct (Nat.leb_spec a x);
    cbn [length]; lia.
Qed.

Lemma cntge_cons : forall x L y,
  cntge (x :: L) y = ((if Nat.leb y x then 1 else 0) + cntge L y)%nat.
Proof.
  intros x L y. unfold cntge. cbn [filter].
  destruct (Nat.leb y x); cbn [length]; lia.
Qed.

Lemma pairge_cons : forall x L, ~ In x L ->
  pairge (x :: L) = (S (length L) + pairge L)%nat.
Proof.
  intros x L Hnx.
  assert (Hsp := split_at_point x L Hnx).
  unfold pairge at 1. cbn [fold_right].
  rewrite (cntge_cons x L x), Nat.leb_refl.
  transitivity (1 + cntge L x
                + fold_right (fun y acc =>
                    ((if Nat.leb y x then 1 else 0) + cntge L y + acc)%nat)
                    0%nat L)%nat.
  { f_equal. apply nfold_ext_in. intros y _. apply cntge_cons. }
  rewrite (fold_add_split nat (fun y => if Nat.leb y x then 1 else 0)
             (fun y => cntge L y) L).
  cbn beta.
  rewrite <- (length_filter_fold nat (fun y => Nat.leb y x) L).
  unfold pairge. unfold cntge in Hsp |- *. lia.
Qed.

Lemma pairge_val : forall L, NoDup L ->
  (2 * pairge L = length L * S (length L))%nat.
Proof.
  induction L as [|x L IH]; intro Hnd; [reflexivity|].
  inversion Hnd as [|z r Hnx Hnd' Heq]; subst.
  rewrite (pairge_cons x L Hnx).
  assert (IHL := IH Hnd').
  cbn [length]. nia.
Qed.

Definition safelist (b : list nat) (n : nat) : list nat :=
  filter (safeb b) (seq 1 n).

Lemma safelist_nodup : forall b n, NoDup (safelist b n).
Proof. intros b n. unfold safelist. apply NoDup_filter. apply seq_NoDup. Qed.

Lemma safelist_len : forall b n,
  S (length (safelist b n)) = safecount b n.
Proof. intros b n. unfold safelist. symmetry. apply safecount_head. Qed.

Corollary safelist_pairs : forall b n,
  (2 * pairge (safelist b n) = (safecount b n - 1) * safecount b n)%nat.
Proof.
  intros b n. rewrite (pairge_val _ (safelist_nodup b n)).
  rewrite <- (safelist_len b n).
  replace (S (length (safelist b n)) - 1) with (length (safelist b n)) by lia.
  reflexivity.
Qed.

Corollary scpair_closed : forall m,
  (scpair m + 4 * card132 (S m) = 2 * card132 (S (S m)))%nat.
Proof.
  intro m.
  assert (H := scsq_closed m).
  assert (E : (scpair m + card132 (S m) = scsq m)%nat).
  { unfold scpair, scsq.
    rewrite (card132_sccount m).
    rewrite <- (fold_add_split (list nat)
                 (fun u => ((sccount u m - 1) * sccount u m)%nat)
                 (fun u => sccount u m) (gen132 m)).
    apply nfold_ext_in. intros u Hu.
    assert (Hp : is_perm u m) by (apply gen132_perm; exact Hu).
    assert (Hpos : (1 <= sccount u m)%nat).
    { unfold sccount.
      apply (in_length_pos nat m).
      apply filter_In. split; [apply in_seq; lia | apply topsplit_full]. }
    nia. }
  lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The subtree statistic under the max-split.  Below the split an unsafe node
   keeps the right factor's subtree sum and a safe one gains the whole tail;
   above the split every node carries the left factor's, lifted.  The safe
   nodes contribute their ordered pairs, which is where pairge enters. *)
Definition Aw (u : list nat) (M : nat) : nat :=
  fold_right (fun z acc => (Hu u M z + acc)%nat) 0%nat (seq 0 (S M)).

Definition Awp (u : list nat) (M : nat) : nat :=
  fold_right (fun z acc => (Hu u M z + acc)%nat) 0%nat (seq 1 M).

Definition Bwp (u : list nat) (M : nat) : nat :=
  fold_right (fun y acc => (Bin u M y + acc)%nat) 0%nat (seq 1 M).

Lemma Aw_split : forall u M, Aw u M = (tri M + Lsum u M)%nat.
Proof.
  intros u M. unfold Aw.
  transitivity (fold_right (fun z acc => (z + hgap u M z + acc)%nat) 0%nat
                           (seq 0 (S M))).
  - apply nfold_ext_in. intros z Hz. apply in_seq in Hz.
    assert (Hg : z <= Hu u M z) by (apply Hu_ge; lia).
    unfold hgap. lia.
  - rewrite (fold_add_split nat (fun z => z) (hgap u M) (seq 0 (S M))).
    cbn beta. unfold tri, Lsum. reflexivity.
Qed.

Definition Atot (M : nat) : nat :=
  fold_right (fun u acc => (Aw u M + acc)%nat) 0%nat (gen132 M).

Theorem Atot_closed : forall M,
  (2 * Atot M + binomN (2 * M) M = M * binomN (2 * M) M + 4 ^ M)%nat.
Proof.
  intro M.
  assert (HA : Atot M = (card132 M * tri M + Ltot M)%nat).
  { unfold Atot.
    transitivity (fold_right (fun u acc => (tri M + Lsum u M + acc)%nat) 0%nat
                             (gen132 M)).
    - apply nfold_ext_in. intros u _. apply Aw_split.
    - rewrite (fold_add_split (list nat) (fun _ : list nat => tri M)
                 (fun u => Lsum u M) (gen132 M)).
      cbn beta.
      rewrite (nfold_const (list nat) (tri M) (gen132 M)).
      unfold Ltot, card132. nia. }
  assert (Htri := tri_val M).
  assert (Hcat := card132_binom M).
  assert (Hlt := Ltot_closed M).
  nia.
Qed.
Lemma Bin_zero : forall u M, Bin u M 0 = Aw u M.
Proof.
  intros u M. unfold Bin, Aw. rewrite Hu_zero.
  replace (M - 0) with M by lia. reflexivity.
Qed.

Lemma safe_iff_Hu : forall b y,
  is_perm b (length b) ->
  (safe_at b y <-> Hu b (length b) y = length b).
Proof.
  intros b y Hp. split.
  - intro Hs. apply Hu_safe. exact Hs.
  - intro E. apply hvals_empty_safe. intros v Hv.
    assert (K := Hu_le_in b (length b) y v Hv).
    apply in_hvals in Hv.
    destruct Hv as [_ [j [_ [Hj [_ [_ Hn]]]]]].
    assert (Hlt : v < length b).
    { rewrite <- Hn. destruct Hp as [_ [_ Hb]]. apply Hb. apply nth_In. lia. }
    lia.
Qed.

Lemma filter_ge_seq : forall n y, 1 <= y -> y <= n ->
  filter (fun z => Nat.leb y z) (seq 1 n) = seq y (S (n - y)).
Proof.
  induction n as [|n IH]; intros y H1 H2; [lia|].
  rewrite (seq_snoc n 1), filter_app.
  destruct (Nat.eq_dec y (S n)) as [E|E].
  - subst y.
    rewrite (filter_all_false (fun z => Nat.leb (S n) z) (seq 1 n)).
    + cbn [filter]. replace (1 + n) with (S n) by lia.
      rewrite Nat.leb_refl. replace (S n - S n) with 0 by lia. reflexivity.
    + intros z Hz. apply in_seq in Hz. apply Nat.leb_gt. lia.
  - rewrite (IH y H1 ltac:(lia)). cbn [filter].
    replace (1 + n) with (S n) by lia.
    assert (Hy : Nat.leb y (S n) = true) by (apply Nat.leb_le; lia).
    rewrite Hy.
    replace (S n - y) with (S (n - y)) by lia.
    rewrite (seq_snoc (S (n - y)) y).
    replace (y + S (n - y)) with (S n) by lia. reflexivity.
Qed.

Lemma cntge_safelist : forall b n y, 1 <= y -> y <= n ->
  cntge (safelist b n) y
  = length (filter (safeb b) (seq y (S (n - y)))).
Proof.
  intros b n y H1 H2. unfold cntge, safelist.
  rewrite (filter_filter nat (safeb b) (fun z => Nat.leb y z) (seq 1 n)).
  rewrite <- (filter_ge_seq n y H1 H2).
  rewrite (filter_filter nat (fun z => Nat.leb y z) (safeb b) (seq 1 n)).
  f_equal. apply filter_ext_gen. intro z. apply Bool.andb_comm.
Qed.

Lemma nfold_succ_gap : forall u N,
  fold_right (fun y acc => (S (hgap u N y) + acc)%nat) 0%nat (seq 1 N)
  = Lsum u N.
Proof.
  intros u N.
  change (fun y acc => (S (hgap u N y) + acc)%nat)
    with (fun y acc => (1 + hgap u N y + acc)%nat).
  rewrite (fold_add_split nat (fun _ : nat => 1) (hgap u N) (seq 1 N)).
  cbn beta.
  rewrite (nfold_const nat 1 (seq 1 N)), length_seq.
  assert (HL := Lsum_tail u N). lia.
Qed.

(* the block above the split contributes the left factor, lifted *)

Lemma Hsum_hi_block : forall a b,
  is_perm a (length a) -> is_perm b (length b) ->
  fold_right (fun z acc =>
    (Hu (midmax a b) (length a + S (length b)) z + acc)%nat) 0%nat
    (seq (S (length b)) (length a))
  = (length a * length b + Awp a (length a))%nat.
Proof.
  intros a b Hpa Hpb.
  replace (seq (S (length b)) (length a))
    with (map (fun t => t + length b) (seq 1 (length a)))
    by (rewrite seq_add_map; reflexivity).
  rewrite (nfold_map_gen nat nat
             (Hu (midmax a b) (length a + S (length b)))
             (fun t => t + length b) (seq 1 (length a))).
  cbn beta.
  transitivity (fold_right (fun z acc =>
      (length b + Hu a (length a) z + acc)%nat) 0%nat (seq 1 (length a))).
  - apply nfold_ext_in. intros z Hz. apply in_seq in Hz.
    rewrite (Hu_midmax_hi a b (z + length b) Hpa Hpb ltac:(lia) ltac:(lia)).
    replace (z + length b - length b) with z by lia. reflexivity.
  - rewrite (fold_add_split nat (fun _ : nat => length b)
               (fun z => Hu a (length a) z) (seq 1 (length a))).
    cbn beta.
    rewrite (nfold_const nat (length b) (seq 1 (length a))), length_seq.
    unfold Awp. lia.
Qed.

(* and each of its nodes carries the left factor's subtree sum, lifted *)

Lemma Bin_hi : forall a b y,
  is_perm a (length a) -> is_perm b (length b) -> 1 <= y -> y <= length a ->
  Bin (midmax a b) (length a + S (length b)) (y + length b)
  = (length b * S (Hu a (length a) y - y) + Bin a (length a) y)%nat.
Proof.
  intros a b y Hpa Hpb Hy1 Hya.
  assert (Hc := Hu_le_cap a (length a) y).
  assert (Hg : y <= Hu a (length a) y) by (apply Hu_ge; lia).
  unfold Bin at 1.
  rewrite (Hu_midmax_hi a b (y + length b) Hpa Hpb ltac:(lia) ltac:(lia)).
  replace (y + length b - length b) with y by lia.
  replace (length b + Hu a (length a) y - (y + length b))
    with (Hu a (length a) y - y) by lia.
  replace (seq (y + length b) (S (Hu a (length a) y - y)))
    with (map (fun t => t + length b) (seq y (S (Hu a (length a) y - y))))
    by (rewrite seq_add_map; reflexivity).
  rewrite (nfold_map_gen nat nat
             (Hu (midmax a b) (length a + S (length b)))
             (fun t => t + length b) (seq y (S (Hu a (length a) y - y)))).
  cbn beta.
  transitivity (fold_right (fun z acc =>
      (length b + Hu a (length a) z + acc)%nat) 0%nat
      (seq y (S (Hu a (length a) y - y)))).
  - apply nfold_ext_in. intros z Hz. apply in_seq in Hz.
    assert (Hzc := Hu_le_cap a (length a) z).
    rewrite (Hu_midmax_hi a b (z + length b) Hpa Hpb ltac:(lia) ltac:(lia)).
    replace (z + length b - length b) with z by lia. reflexivity.
  - rewrite (fold_add_split nat (fun _ : nat => length b)
               (fun z => Hu a (length a) z)
               (seq y (S (Hu a (length a) y - y)))).
    cbn beta.
    rewrite (nfold_const nat (length b)
               (seq y (S (Hu a (length a) y - y)))), length_seq.
    unfold Bin. lia.
Qed.

Theorem Bsum_hi_block : forall a b,
  is_perm a (length a) -> is_perm b (length b) ->
  fold_right (fun y acc =>
    (Bin (midmax a b) (length a + S (length b)) y + acc)%nat) 0%nat
    (seq (S (length b)) (length a))
  = (length b * Lsum a (length a) + Bwp a (length a))%nat.
Proof.
  intros a b Hpa Hpb.
  replace (seq (S (length b)) (length a))
    with (map (fun t => t + length b) (seq 1 (length a)))
    by (rewrite seq_add_map; reflexivity).
  rewrite (nfold_map_gen nat nat
             (Bin (midmax a b) (length a + S (length b)))
             (fun t => t + length b) (seq 1 (length a))).
  cbn beta.
  transitivity (fold_right (fun y acc =>
      (length b * S (hgap a (length a) y) + Bin a (length a) y + acc)%nat)
      0%nat (seq 1 (length a))).
  - apply nfold_ext_in. intros y Hy. apply in_seq in Hy.
    rewrite (Bin_hi a b y Hpa Hpb ltac:(lia) ltac:(lia)).
    unfold hgap. reflexivity.
  - rewrite (fold_add_split nat
               (fun y => (length b * S (hgap a (length a) y))%nat)
               (fun y => Bin a (length a) y) (seq 1 (length a))).
    cbn beta.
    rewrite (nfold_scal nat (length b)
               (fun y => S (hgap a (length a) y)) (seq 1 (length a))).
    rewrite (nfold_succ_gap a (length a)).
    unfold Bwp. reflexivity.
Qed.

(* below the split an unsafe node keeps the right factor's subtree sum *)

Lemma Bin_lo_unsafe : forall a b y,
  is_perm a (length a) -> is_perm b (length b) ->
  1 <= y -> y <= length b -> ~ safe_at b y ->
  Bin (midmax a b) (length a + S (length b)) y = Bin b (length b) y.
Proof.
  intros a b y Hpa Hpb Hy1 Hyb Hns.
  assert (Hc := Hu_le_cap b (length b) y).
  assert (Hlt : Hu b (length b) y < length b).
  { destruct (Nat.eq_dec (Hu b (length b) y) (length b)) as [E|E]; [|lia].
    exfalso. apply Hns. apply (safe_iff_Hu b y Hpb). exact E. }
  assert (Hg : y <= Hu b (length b) y) by (apply Hu_ge; lia).
  unfold Bin.
  rewrite (Hu_midmax_lo_unsafe a b y Hy1 Hyb Hpb Hns).
  apply nfold_ext_in. intros z Hz. apply in_seq in Hz.
  assert (Hlam : Hu b (length b) z <= Hu b (length b) y)
    by (apply (Hu_laminar b (length b) y z); lia).
  assert (Hnsz : ~ safe_at b z).
  { intro C. assert (E := proj1 (safe_iff_Hu b z Hpb) C). lia. }
  apply (Hu_midmax_lo_unsafe a b z ltac:(lia) ltac:(lia) Hpb Hnsz).
Qed.

Lemma seq_split_tail : forall al bl y, y <= bl ->
  seq y (S (al + S bl - y))
  = seq y (S (bl - y)) ++ seq (S bl) al ++ seq (al + S bl) 1.
Proof.
  intros al bl y H.
  replace (S (al + S bl - y)) with (S (bl - y) + (al + 1)) by lia.
  rewrite (seq_break (S (bl - y)) (al + 1) y).
  replace (y + S (bl - y)) with (S bl) by lia.
  rewrite (seq_break al 1 (S bl)).
  replace (S bl + al) with (al + S bl) by lia.
  reflexivity.
Qed.

Lemma Hsum_lo_tail : forall a b y,
  is_perm a (length a) -> is_perm b (length b) ->
  1 <= y -> y <= length b -> safe_at b y ->
  fold_right (fun z acc =>
    (Hu (midmax a b) (length a + S (length b)) z + acc)%nat) 0%nat
    (seq y (S (length b - y)))
  = (Bin b (length b) y
     + (length a + 1) * cntge (safelist b (length b)) y)%nat.
Proof.
  intros a b y Hpa Hpb Hy1 Hyb Hs.
  assert (Eb : Hu b (length b) y = length b)
    by (apply (safe_iff_Hu b y Hpb); exact Hs).
  transitivity (fold_right (fun z acc =>
      (Hu b (length b) z
       + (if safeb b z then (length a + 1) else 0) + acc)%nat) 0%nat
      (seq y (S (length b - y)))).
  - apply nfold_ext_in. intros z Hz. apply in_seq in Hz.
    destruct (safeb b z) eqn:Es.
    + assert (Hsz : safe_at b z) by (apply safeb_spec; exact Es).
      rewrite (Hu_midmax_lo_safe a b z ltac:(lia) ltac:(lia) Hsz).
      assert (E := proj1 (safe_iff_Hu b z Hpb) Hsz). lia.
    + assert (Hnsz : ~ safe_at b z).
      { intro C. assert (K : safeb b z = true) by (apply safeb_spec; exact C).
        rewrite Es in K. discriminate. }
      rewrite (Hu_midmax_lo_unsafe a b z ltac:(lia) ltac:(lia) Hpb Hnsz). lia.
  - rewrite (fold_add_split nat (fun z => Hu b (length b) z)
               (fun z => if safeb b z then (length a + 1) else 0)
               (seq y (S (length b - y)))).
    cbn beta.
    rewrite (nfold_filter nat (safeb b) (fun _ : nat => (length a + 1)%nat)
               (seq y (S (length b - y)))).
    rewrite (nfold_const nat (length a + 1)
               (filter (safeb b) (seq y (S (length b - y))))).
    rewrite <- (cntge_safelist b (length b) y Hy1 Hyb).
    unfold Bin. rewrite Eb. lia.
Qed.

Lemma Bin_lo_safe : forall a b y,
  is_perm a (length a) -> is_perm b (length b) ->
  1 <= y -> y <= length b -> safe_at b y ->
  Bin (midmax a b) (length a + S (length b)) y
  = (Bin b (length b) y
     + (length a + 1) * cntge (safelist b (length b)) y
     + (length a * length b + Awp a (length a)
        + (length a + S (length b))))%nat.
Proof.
  intros a b y Hpa Hpb Hy1 Hyb Hs.
  unfold Bin at 1.
  rewrite (Hu_midmax_lo_safe a b y Hy1 Hyb Hs).
  rewrite (seq_split_tail (length a) (length b) y Hyb).
  rewrite !(nfold_app nat (Hu (midmax a b) (length a + S (length b)))).
  rewrite (Hsum_lo_tail a b y Hpa Hpb Hy1 Hyb Hs).
  rewrite (Hsum_hi_block a b Hpa Hpb).
  replace (seq (length a + S (length b)) 1)
    with ((length a + S (length b)) :: nil) by reflexivity.
  rewrite (nfold_single nat (Hu (midmax a b) (length a + S (length b)))
             (length a + S (length b))).
  cbn beta. rewrite Hu_top. lia.
Qed.

Theorem Bsum_lo_block : forall a b,
  is_perm a (length a) -> is_perm b (length b) ->
  fold_right (fun y acc =>
    (Bin (midmax a b) (length a + S (length b)) y + acc)%nat) 0%nat
    (seq 1 (length b))
  = (Bwp b (length b)
     + (length a + 1) * pairge (safelist b (length b))
     + length (safelist b (length b))
       * (length a * length b + Awp a (length a)
          + (length a + S (length b))))%nat.
Proof.
  intros a b Hpa Hpb.
  transitivity (fold_right (fun y acc =>
      (Bin b (length b) y
       + (if safeb b y
          then ((length a + 1) * cntge (safelist b (length b)) y
                + (length a * length b + Awp a (length a)
                   + (length a + S (length b))))%nat
          else 0)
       + acc)%nat) 0%nat (seq 1 (length b))).
  - apply nfold_ext_in. intros y Hy. apply in_seq in Hy.
    destruct (safeb b y) eqn:Es.
    + assert (Hs : safe_at b y) by (apply safeb_spec; exact Es).
      rewrite (Bin_lo_safe a b y Hpa Hpb ltac:(lia) ltac:(lia) Hs). lia.
    + assert (Hns : ~ safe_at b y).
      { intro C. assert (K : safeb b y = true) by (apply safeb_spec; exact C).
        rewrite Es in K. discriminate. }
      rewrite (Bin_lo_unsafe a b y Hpa Hpb ltac:(lia) ltac:(lia) Hns). lia.
  - rewrite (fold_add_split nat (fun y => Bin b (length b) y)
               (fun y => if safeb b y
                         then ((length a + 1) * cntge (safelist b (length b)) y
                               + (length a * length b + Awp a (length a)
                                  + (length a + S (length b))))%nat
                         else 0) (seq 1 (length b))).
    cbn beta.
    rewrite (nfold_filter nat (safeb b)
               (fun y => ((length a + 1) * cntge (safelist b (length b)) y
                          + (length a * length b + Awp a (length a)
                             + (length a + S (length b))))%nat)
               (seq 1 (length b))).
    change (filter (safeb b) (seq 1 (length b)))
      with (safelist b (length b)).
    rewrite (fold_add_split nat
               (fun y => ((length a + 1)
                          * cntge (safelist b (length b)) y)%nat)
               (fun _ : nat => (length a * length b + Awp a (length a)
                                + (length a + S (length b)))%nat)
               (safelist b (length b))).
    cbn beta.
    rewrite (nfold_scal nat (length a + 1)
               (cntge (safelist b (length b))) (safelist b (length b))).
    rewrite (nfold_const nat (length a * length b + Awp a (length a)
                              + (length a + S (length b)))
               (safelist b (length b))).
    unfold Bwp, pairge. lia.
Qed.

Theorem Bw_midmax : forall a b,
  is_perm a (length a) -> is_perm b (length b) ->
  Bw (midmax a b) (length a + S (length b))
  = (Aw (midmax a b) (length a + S (length b))
     + Bwp b (length b)
     + (length a + 1) * pairge (safelist b (length b))
     + length (safelist b (length b))
       * (length a * length b + Awp a (length a)
          + (length a + S (length b)))
     + length b * Lsum a (length a) + Bwp a (length a)
     + (length a + S (length b)))%nat.
Proof.
  intros a b Hpa Hpb.
  assert (Etop : Bin (midmax a b) (length a + S (length b))
                     (length a + S (length b)) = (length a + S (length b))%nat).
  { unfold Bin. rewrite Hu_top.
    replace (length a + S (length b) - (length a + S (length b))) with 0 by lia.
    replace (seq (length a + S (length b)) 1)
      with ((length a + S (length b)) :: nil) by reflexivity.
    cbn [fold_right]. rewrite Hu_top. lia. }
  unfold Bw. rewrite (seq_split_three (length a) (length b)).
  rewrite !(nfold_app nat (Bin (midmax a b) (length a + S (length b)))).
  replace (seq 0 1) with (0 :: nil) by reflexivity.
  replace (seq (length a + S (length b)) 1)
    with ((length a + S (length b)) :: nil) by reflexivity.
  rewrite !(nfold_single nat (Bin (midmax a b) (length a + S (length b)))).
  rewrite (Bin_zero (midmax a b) (length a + S (length b))).
  rewrite (Bsum_lo_block a b Hpa Hpb), (Bsum_hi_block a b Hpa Hpb), Etop.
  lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The convolutions the max-split recursions run into.  The central binomials
   convolve to the powers of four, which fixes the quadratic weight against the
   Catalan convolution and, with it, every polynomial weight up to degree two. *)

Definition cb (n : nat) : nat := binomN (2 * n) n.

Lemma cbi_ratio : forall n, (S n * cb (S n) = 2 * (2 * n + 1) * cb n)%nat.
Proof. intro n. unfold cb. assert (K := cb_ratio n). nia. Qed.

Lemma cb_card : forall n, (S n * card132 n)%nat = cb n.
Proof. intro n. unfold cb. apply card132_binom. Qed.

Definition bsum (w : nat -> nat) (m : nat) : nat :=
  fold_right (fun k acc => (w k * (cb k * cb (m - k)) + acc)%nat) 0%nat
             (seq 0 (S m)).

Lemma bsum_ext : forall w1 w2 m,
  (forall k, (k <= m)%nat -> w1 k = w2 k) -> bsum w1 m = bsum w2 m.
Proof.
  intros w1 w2 m H. unfold bsum. apply nfold_ext_in.
  intros k Hk. apply in_seq in Hk. rewrite (H k ltac:(lia)). reflexivity.
Qed.

Lemma bsum_add : forall w1 w2 m,
  (bsum w1 m + bsum w2 m)%nat = bsum (fun k => (w1 k + w2 k)%nat) m.
Proof.
  intros w1 w2 m. unfold bsum. cbn beta.
  generalize (seq 0 (S m)) as l. intro l.
  induction l as [|a l IH]; cbn [fold_right]; [lia | rewrite <- IH; ring].
Qed.

Lemma bsum_scal : forall c w m,
  bsum (fun k => (c * w k)%nat) m = (c * bsum w m)%nat.
Proof.
  intros c w m. unfold bsum. cbn beta.
  generalize (seq 0 (S m)) as l. intro l.
  induction l as [|a l IH]; cbn [fold_right]; [lia | rewrite IH; ring].
Qed.

Lemma bsum_rev : forall w m, bsum w m = bsum (fun k => w (m - k)%nat) m.
Proof.
  intros w m. symmetry. unfold bsum. cbn beta.
  transitivity (fold_right (fun k acc =>
      ((fun t => (w t * (cb t * cb (m - t)))%nat) (m - k)%nat + acc)%nat)
      0%nat (seq 0 (S m))).
  - apply nfold_ext_in. intros k Hk. apply in_seq in Hk. cbn beta.
    replace (m - (m - k))%nat with k by lia. ring.
  - apply (nfold_rev_seq (fun t => (w t * (cb t * cb (m - t)))%nat) m).
Qed.

Definition pconv (m : nat) : nat := bsum (fun _ => 1%nat) m.
Definition pconv1 (m : nat) : nat := bsum (fun k => k) m.

Lemma bsum_const : forall c m, bsum (fun _ => c) m = (c * pconv m)%nat.
Proof.
  intros c m. unfold pconv. rewrite <- (bsum_scal c (fun _ => 1%nat) m).
  apply bsum_ext. intros k _. lia.
Qed.

Lemma pconv1_sym : forall m, (2 * pconv1 m = m * pconv m)%nat.
Proof.
  intro m. unfold pconv1.
  assert (A1 : bsum (fun k => k) m = bsum (fun k => (m - k)%nat) m)
    by apply bsum_rev.
  assert (A2 : (bsum (fun k => k) m + bsum (fun k => (m - k)%nat) m)%nat
             = bsum (fun k => (k + (m - k))%nat) m) by apply bsum_add.
  assert (A3 : bsum (fun k => (k + (m - k))%nat) m = bsum (fun _ => m) m)
    by (apply bsum_ext; intros k Hk; lia).
  rewrite (bsum_const m m) in A3. lia.
Qed.

Lemma pconv1_succ : forall n, pconv1 (S n) = bsum (fun k => (4 * k + 2)%nat) n.
Proof.
  intro n. unfold pconv1, bsum. cbn beta.
  change (seq 0 (S (S n))) with (0%nat :: seq 1 (S n)).
  rewrite (nfold_cons nat (fun k => (k * (cb k * cb (S n - k)))%nat) 0%nat
             (seq 1 (S n))).
  cbn beta.
  replace (0 * (cb 0 * cb (S n - 0)))%nat with 0%nat by lia.
  rewrite Nat.add_0_l.
  rewrite <- (seq_shift (S n) 0).
  rewrite (nfold_map_gen nat nat (fun k => (k * (cb k * cb (S n - k)))%nat) S
             (seq 0 (S n))).
  apply nfold_ext_in. intros k Hk. apply in_seq in Hk. cbn beta.
  replace (S n - S k)%nat with (n - k)%nat by lia.
  assert (E := cbi_ratio k).
  transitivity ((S k * cb (S k)) * cb (n - k))%nat; [ring|].
  rewrite E. ring.
Qed.

Lemma bsum_lin : forall n,
  bsum (fun k => (4 * k + 2)%nat) n = (4 * pconv1 n + 2 * pconv n)%nat.
Proof.
  intro n.
  rewrite <- (bsum_add (fun k => (4 * k)%nat) (fun _ => 2%nat) n).
  rewrite (bsum_scal 4 (fun k => k) n).
  rewrite (bsum_const 2 n).
  unfold pconv1. reflexivity.
Qed.

Theorem pconv_pow : forall m, pconv m = (4 ^ m)%nat.
Proof.
  induction m as [|m IH]; [vm_compute; reflexivity|].
  assert (H1 := pconv1_sym m).
  assert (H2 := pconv1_sym (S m)).
  rewrite (pconv1_succ m), (bsum_lin m) in H2.
  assert (E : pconv (S m) = (4 * pconv m)%nat).
  { apply (Nat.mul_cancel_l _ _ (S m)); [lia|]. nia. }
  rewrite E, IH. cbn [Nat.pow]. lia.
Qed.

(* Polynomial weights against the Catalan convolution. *)

Lemma wsum_prodS : forall m,
  wsum (fun k => ((k + 1) * (m - k + 1))%nat) m = (4 ^ m)%nat.
Proof.
  intro m. rewrite <- (pconv_pow m). unfold pconv, wsum, bsum.
  apply nfold_ext_in. intros k Hk. apply in_seq in Hk. cbn beta.
  rewrite <- (cb_card k), <- (cb_card (m - k)). ring.
Qed.

Lemma wsum_id_val : forall n,
  (2 * wsum (fun k => k) n = n * card132 (S n))%nat.
Proof.
  intro n.
  assert (A1 : wsum (fun k => k) n = wsum (fun k => (n - k)%nat) n)
    by apply wsum_rev.
  assert (A2 : (wsum (fun k => k) n + wsum (fun k => (n - k)%nat) n)%nat
             = wsum (fun k => (k + (n - k))%nat) n) by apply wsum_add.
  assert (A3 : wsum (fun k => (k + (n - k))%nat) n = wsum (fun _ => n) n)
    by (apply wsum_ext; intros k Hk; lia).
  rewrite wsum_const in A3. lia.
Qed.

Lemma wsum_kmk_val : forall n,
  (wsum (fun k => (k * (n - k))%nat) n + (n + 1) * card132 (S n) = 4 ^ n)%nat.
Proof.
  intro n. rewrite <- (wsum_prodS n).
  assert (A : (wsum (fun k => (k * (n - k))%nat) n
               + wsum (fun _ => (n + 1)%nat) n)%nat
            = wsum (fun k => (k * (n - k) + (n + 1))%nat) n) by apply wsum_add.
  rewrite wsum_const in A.
  rewrite A. apply wsum_ext. intros k Hk.
  assert (Hj : (n - k + k)%nat = n) by lia. nia.
Qed.

Lemma wsum_sq_val : forall n,
  (2 * wsum (fun k => (k * k)%nat) n + 2 * 4 ^ n
   = (n * n + 2 * n + 2) * card132 (S n))%nat.
Proof.
  intro n.
  assert (A : (wsum (fun k => (k * (n - k))%nat) n
               + wsum (fun k => (k * k)%nat) n)%nat
            = wsum (fun k => (k * (n - k) + k * k)%nat) n) by apply wsum_add.
  assert (B : wsum (fun k => (k * (n - k) + k * k)%nat) n
            = wsum (fun k => (n * k)%nat) n)
    by (apply wsum_ext; intros k Hk; nia).
  rewrite (wsum_scal n (fun k => k) n) in B.
  assert (C := wsum_id_val n).
  assert (D := wsum_kmk_val n).
  nia.
Qed.

(* Shifting the right factor. *)

Lemma wsum_shift1 : forall w m,
  (fold_right (fun k acc =>
     (w k * (card132 k * card132 (S (m - k))) + acc)%nat) 0%nat (seq 0 (S m))
   + w (S m) * card132 (S m))%nat
  = wsum w (S m).
Proof.
  intros w m. unfold wsum. rewrite (seq_snoc (S m) 0).
  rewrite (nfold_app nat (fun k => (w k * (card132 k * card132 (S m - k)))%nat)).
  rewrite (nfold_single nat
             (fun k => (w k * (card132 k * card132 (S m - k)))%nat) (0 + S m)).
  cbn beta. f_equal.
  - apply nfold_ext_in. intros k Hk. apply in_seq in Hk.
    replace (S m - k)%nat with (S (m - k)) by lia. reflexivity.
  - replace (0 + S m)%nat with (S m) by lia.
    rewrite Nat.sub_diag. change (card132 0) with 1%nat. ring.
Qed.

Lemma wsum_shift2 : forall w m,
  (fold_right (fun k acc =>
     (w k * (card132 k * card132 (S (S (m - k)))) + acc)%nat) 0%nat
     (seq 0 (S m))
   + w (S m) * card132 (S m) + w (S (S m)) * card132 (S (S m)))%nat
  = wsum w (S (S m)).
Proof.
  intros w m.
  rewrite <- (wsum_shift1 w (S m)).
  rewrite (seq_snoc (S m) 0).
  rewrite (nfold_app nat
             (fun k => (w k * (card132 k * card132 (S (S m - k))))%nat)).
  rewrite (nfold_single nat
             (fun k => (w k * (card132 k * card132 (S (S m - k))))%nat)
             (0 + S m)).
  cbn beta.
  replace (0 + S m)%nat with (S m) by lia.
  rewrite Nat.sub_diag. change (card132 1) with 1%nat.
  assert (E : fold_right (fun k acc =>
                (w k * (card132 k * card132 (S (S m - k))) + acc)%nat) 0%nat
                (seq 0 (S m))
            = fold_right (fun k acc =>
                (w k * (card132 k * card132 (S (S (m - k)))) + acc)%nat) 0%nat
                (seq 0 (S m))).
  { apply nfold_ext_in. intros k Hk. apply in_seq in Hk.
    replace (S m - k)%nat with (S (m - k)) by lia. reflexivity. }
  rewrite E. ring.
Qed.

(* The weighted four-against-Catalan convolution. *)

Definition Bconv (m : nat) : nat :=
  fold_right (fun k acc => (k * (4 ^ k * card132 (m - k)) + acc)%nat) 0%nat
             (seq 0 (S m)).

Lemma Bconv_rec : forall m, Bconv (S m) = (4 * (Bconv m + Aconv m))%nat.
Proof.
  intro m. unfold Bconv at 1.
  change (seq 0 (S (S m))) with (0%nat :: seq 1 (S m)).
  rewrite (nfold_cons nat (fun k => (k * (4 ^ k * card132 (S m - k)))%nat) 0%nat
             (seq 1 (S m))).
  cbn beta.
  replace (0 * (4 ^ 0 * card132 (S m - 0)))%nat with 0%nat by lia.
  rewrite Nat.add_0_l.
  rewrite <- (seq_shift (S m) 0).
  rewrite (nfold_map_gen nat nat
             (fun k => (k * (4 ^ k * card132 (S m - k)))%nat) S (seq 0 (S m))).
  cbn beta.
  unfold Bconv, Aconv.
  rewrite Nat.mul_add_distr_l.
  rewrite <- (nfold_scal nat 4 (fun j => (j * (4 ^ j * card132 (m - j)))%nat)
                (seq 0 (S m))).
  rewrite <- (nfold_scal nat 4 (fun j => (4 ^ j * card132 (m - j))%nat)
                (seq 0 (S m))).
  rewrite <- (fold_add_split nat
                (fun j => (4 * (j * (4 ^ j * card132 (m - j))))%nat)
                (fun j => (4 * (4 ^ j * card132 (m - j)))%nat) (seq 0 (S m))).
  apply nfold_ext_in. intros j Hj. apply in_seq in Hj.
  replace (S m - S j)%nat with (m - j)%nat by lia.
  cbn [Nat.pow]. ring.
Qed.

Lemma Bconv_val : forall m,
  (2 * Bconv m + 4 * (2 * m + 1) * cb m = (m + 1) * 4 ^ (S m))%nat.
Proof.
  induction m as [|m IH]; [vm_compute; reflexivity|].
  rewrite (Bconv_rec m).
  assert (HA := Aconv_closed m).
  assert (HR := cbi_ratio m).
  change (binomN (2 * S m) (S m)) with (cb (S m)) in HA.
  replace (4 ^ S (S m))%nat with (4 * 4 ^ S m)%nat by (cbn [Nat.pow]; ring).
  nia.
Qed.

Lemma Aconv_shift1 : forall m,
  (fold_right (fun k acc => (4 ^ k * card132 (S (m - k)) + acc)%nat) 0%nat
     (seq 0 (S m)) + 4 ^ (S m))%nat
  = Aconv (S m).
Proof.
  intro m. unfold Aconv. rewrite (seq_snoc (S m) 0).
  rewrite (nfold_app nat (fun k => (4 ^ k * card132 (S m - k))%nat)).
  rewrite (nfold_single nat (fun k => (4 ^ k * card132 (S m - k))%nat) (0 + S m)).
  cbn beta. f_equal.
  - apply nfold_ext_in. intros k Hk. apply in_seq in Hk.
    replace (S m - k)%nat with (S (m - k)) by lia. reflexivity.
  - replace (0 + S m)%nat with (S m) by lia.
    rewrite Nat.sub_diag. change (card132 0) with 1%nat. ring.
Qed.

Lemma Aconv_rev_w : forall m,
  (fold_right (fun k acc => ((m - k) * (4 ^ k * card132 (m - k)) + acc)%nat)
     0%nat (seq 0 (S m)) + Bconv m)%nat
  = (m * Aconv m)%nat.
Proof.
  intro m. unfold Bconv, Aconv.
  rewrite <- (nfold_scal nat m (fun k => (4 ^ k * card132 (m - k))%nat)
                (seq 0 (S m))).
  rewrite <- (fold_add_split nat
                (fun k => ((m - k) * (4 ^ k * card132 (m - k)))%nat)
                (fun k => (k * (4 ^ k * card132 (m - k)))%nat) (seq 0 (S m))).
  apply nfold_ext_in. intros k Hk. apply in_seq in Hk.
  assert (Hk' : (m - k + k)%nat = m) by lia.
  transitivity ((m - k + k) * (4 ^ k * card132 (m - k)))%nat; [ring|].
  rewrite Hk'. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* One former for every convolution the recursions produce. *)

Definition conv (f g : nat -> nat) (m : nat) : nat :=
  fold_right (fun k acc => (f k * g (m - k) + acc)%nat) 0%nat (seq 0 (S m)).

Lemma conv_ext : forall f1 f2 g1 g2 m,
  (forall k, (k <= m)%nat -> f1 k = f2 k) ->
  (forall k, (k <= m)%nat -> g1 k = g2 k) ->
  conv f1 g1 m = conv f2 g2 m.
Proof.
  intros f1 f2 g1 g2 m Hf Hg. unfold conv. apply nfold_ext_in.
  intros k Hk. apply in_seq in Hk.
  rewrite (Hf k ltac:(lia)), (Hg (m - k)%nat ltac:(lia)). reflexivity.
Qed.

Lemma conv_rev : forall f g m, conv f g m = conv g f m.
Proof.
  intros f g m. unfold conv.
  transitivity (fold_right (fun k acc =>
      ((fun t => (g t * f (m - t))%nat) (m - k)%nat + acc)%nat) 0%nat
      (seq 0 (S m))).
  - apply nfold_ext_in. intros k Hk. apply in_seq in Hk. cbn beta.
    replace (m - (m - k))%nat with k by lia. ring.
  - apply (nfold_rev_seq (fun t => (g t * f (m - t))%nat) m).
Qed.

Lemma conv_add_l : forall f1 f2 g m,
  conv (fun k => (f1 k + f2 k)%nat) g m = (conv f1 g m + conv f2 g m)%nat.
Proof.
  intros f1 f2 g m. unfold conv. cbn beta.
  generalize (seq 0 (S m)) as l. intro l.
  induction l as [|a l IH]; cbn [fold_right]; [lia | rewrite IH; ring].
Qed.

Lemma conv_scal_l : forall c f g m,
  conv (fun k => (c * f k)%nat) g m = (c * conv f g m)%nat.
Proof.
  intros c f g m. unfold conv. cbn beta.
  generalize (seq 0 (S m)) as l. intro l.
  induction l as [|a l IH]; cbn [fold_right]; [lia | rewrite IH; ring].
Qed.

Lemma conv_cat : forall m, conv card132 card132 m = card132 (S m).
Proof. intro m. symmetry. apply card132_convolution. Qed.

Lemma conv_wsum : forall w m,
  conv (fun k => (w k * card132 k)%nat) card132 m = wsum w m.
Proof.
  intros w m. unfold conv, wsum. apply nfold_ext_in. intros k _. cbn beta. ring.
Qed.

Lemma conv_aconv : forall m, conv (fun k => 4 ^ k) card132 m = Aconv m.
Proof. intro m. unfold conv, Aconv. reflexivity. Qed.

Lemma conv_bconv : forall m,
  conv (fun k => (k * 4 ^ k)%nat) card132 m = Bconv m.
Proof.
  intro m. unfold conv, Bconv. apply nfold_ext_in. intros k _. cbn beta. ring.
Qed.

Lemma conv_rbconv : forall m,
  (conv (fun k => 4 ^ k) (fun n => (n * card132 n)%nat) m + Bconv m)%nat
  = (m * Aconv m)%nat.
Proof.
  intro m. rewrite <- (Aconv_rev_w m). f_equal.
  unfold conv. apply nfold_ext_in. intros k _. cbn beta. ring.
Qed.

Lemma conv_a1 : forall m,
  (conv (fun k => 4 ^ k) (fun n => card132 (S n)) m + 4 ^ (S m))%nat
  = Aconv (S m).
Proof. intro m. apply Aconv_shift1. Qed.

Lemma conv_shift1 : forall w m,
  (conv (fun k => (w k * card132 k)%nat) (fun n => card132 (S n)) m
   + w (S m) * card132 (S m))%nat
  = wsum w (S m).
Proof.
  intros w m. rewrite <- (wsum_shift1 w m). f_equal.
  unfold conv. apply nfold_ext_in. intros k _. cbn beta. ring.
Qed.

Lemma conv_shift2 : forall w m,
  (conv (fun k => (w k * card132 k)%nat) (fun n => card132 (S (S n))) m
   + w (S m) * card132 (S m) + w (S (S m)) * card132 (S (S m)))%nat
  = wsum w (S (S m)).
Proof.
  intros w m. rewrite <- (wsum_shift2 w m).
  f_equal. f_equal.
  unfold conv. apply nfold_ext_in. intros k _. cbn beta. ring.
Qed.


(* ------------------------------------------------------------------ *)
(* The subtree statistic in closed form. *)


Definition Bwptot (M : nat) : nat :=
  fold_right (fun u acc => (Bwp u M + acc)%nat) 0%nat (gen132 M).

Definition Awptot (M : nat) : nat :=
  fold_right (fun u acc => (Awp u M + acc)%nat) 0%nat (gen132 M).

Definition Ptot (M : nat) : nat :=
  fold_right (fun u acc => (pairge (safelist u M) + acc)%nat) 0%nat (gen132 M).

Lemma Bw_split : forall u M, Bw u M = (Aw u M + Bwp u M)%nat.
Proof.
  intros u M. unfold Bw, Bwp.
  change (seq 0 (S M)) with (0%nat :: seq 1 M).
  rewrite (nfold_cons nat (Bin u M) 0%nat (seq 1 M)).
  rewrite (Bin_zero u M). reflexivity.
Qed.

Lemma Aw_zero_split : forall u M, Aw u M = (M + Awp u M)%nat.
Proof.
  intros u M. unfold Aw, Awp.
  change (seq 0 (S M)) with (0%nat :: seq 1 M).
  rewrite (nfold_cons nat (Hu u M) 0%nat (seq 1 M)).
  rewrite (Hu_zero u M). reflexivity.
Qed.

Lemma Btot_split : forall M, Btot M = (Atot M + Bwptot M)%nat.
Proof.
  intro M. unfold Btot, Atot, Bwptot.
  rewrite <- (fold_add_split (list nat) (fun u => Aw u M) (fun u => Bwp u M)
                (gen132 M)).
  apply nfold_ext_in. intros u _. apply Bw_split.
Qed.

Lemma Atot_split : forall M, Atot M = (M * card132 M + Awptot M)%nat.
Proof.
  intro M. unfold Atot, Awptot.
  transitivity (fold_right (fun u acc => (M + Awp u M + acc)%nat) 0%nat
                           (gen132 M)).
  - apply nfold_ext_in. intros u _. apply Aw_zero_split.
  - rewrite (fold_add_split (list nat) (fun _ : list nat => M)
               (fun u => Awp u M) (gen132 M)).
    cbn beta. rewrite (nfold_const (list nat) M (gen132 M)).
    unfold card132. lia.
Qed.

Lemma Ptot_scpair : forall M, (2 * Ptot M = scpair M)%nat.
Proof.
  intro M. unfold Ptot, scpair.
  rewrite <- (nfold_scal (list nat) 2 (fun u => pairge (safelist u M))
                (gen132 M)).
  apply nfold_ext_in. intros u Hu.
  assert (Hp : is_perm u M) by (apply gen132_perm; exact Hu).
  rewrite (safelist_pairs u M), (safecount_sccount u M Hp). reflexivity.
Qed.

Corollary Ptot_closed : forall M,
  (Ptot M + 2 * card132 (S M) = card132 (S (S M)))%nat.
Proof.
  intro M. assert (H := Ptot_scpair M). assert (K := scpair_closed M). lia.
Qed.

Corollary Awptot_closed : forall M,
  (2 * Awptot M + 2 * M * card132 M + binomN (2 * M) M
   = M * binomN (2 * M) M + 4 ^ M)%nat.
Proof.
  intro M. assert (H := Atot_closed M). rewrite (Atot_split M) in H. lia.
Qed.

Corollary Bwp_midmax : forall a b,
  is_perm a (length a) -> is_perm b (length b) ->
  Bwp (midmax a b) (length a + S (length b))
  = (Bwp b (length b)
     + (length a + 1) * pairge (safelist b (length b))
     + length (safelist b (length b))
       * (length a * length b + Awp a (length a)
          + (length a + S (length b)))
     + length b * Lsum a (length a) + Bwp a (length a)
     + (length a + S (length b)))%nat.
Proof.
  intros a b Hpa Hpb.
  assert (K := Bw_midmax a b Hpa Hpb).
  rewrite (Bw_split (midmax a b) (length a + S (length b))) in K.
  lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The level sum of the subtree statistic, split at the maximum. *)

Theorem Bwptot_expand : forall m,
  Bwptot (S m)
  = fold_right (fun k acc =>
      (card132 k * Bwptot (m - k)
       + card132 k * (k + 1) * Ptot (m - k)
       + sctot (m - k) * (card132 k * (k * (m - k) + S m) + Awptot k)
       + card132 (m - k) * ((m - k) * Ltot k + Bwptot k + card132 k * S m)
       + acc)%nat) 0%nat (seq 0 (S m)).
Proof.
  intro m. unfold Bwptot at 1.
  rewrite (nfold_pairs132 m (fun w => Bwp w (S m))).
  apply nfold_ext_in. intros k Hk. apply in_seq in Hk. destruct Hk as [_ Hk].
  assert (HkM : k <= m) by lia.
  transitivity (fold_right (fun a acc =>
      ((Bwptot (m - k) + card132 k * 0 + (k + 1) * Ptot (m - k)
        + sctot (m - k) * (k * (m - k) + S m)
        + card132 (m - k) * S m)
       + sctot (m - k) * Awp a k
       + card132 (m - k) * (m - k) * Lsum a k
       + card132 (m - k) * Bwp a k
       + acc)%nat) 0%nat (gen132 k)).
  - apply nfold_ext_in. intros a Ha.
    assert (Hpa0 : is_perm a k) by (apply gen132_perm; exact Ha).
    assert (Hla : length a = k) by (apply (perm_len a k); exact Hpa0).
    assert (Hpa : is_perm a (length a)) by (rewrite Hla; exact Hpa0).
    transitivity (fold_right (fun v acc =>
        (((m - k) * Lsum a k + Bwp a k + S m)
         + Bwp v (m - k)
         + (k + 1) * pairge (safelist v (m - k))
         + (k * (m - k) + Awp a k + S m) * length (safelist v (m - k))
         + acc)%nat) 0%nat (gen132 (m - k))).
    + apply nfold_ext_in. intros v Hv.
      assert (Hpv0 : is_perm v (m - k)) by (apply gen132_perm; exact Hv).
      assert (Hlv : length v = (m - k)%nat)
        by (apply (perm_len v (m - k)); exact Hpv0).
      assert (Hpv : is_perm v (length v)) by (rewrite Hlv; exact Hpv0).
      assert (K := Bwp_midmax a v Hpa Hpv).
      rewrite Hla, Hlv in K.
      replace (k + S (m - k))%nat with (S m) in K by lia.
      rewrite K. nia.
    + rewrite (nfold_four (list nat)
                 (fun _ : list nat => ((m - k) * Lsum a k + Bwp a k + S m)%nat)
                 (fun v => Bwp v (m - k))
                 (fun v => ((k + 1) * pairge (safelist v (m - k)))%nat)
                 (fun v => ((k * (m - k) + Awp a k + S m)
                            * length (safelist v (m - k)))%nat)
                 (gen132 (m - k))).
      cbn beta.
      rewrite (nfold_const (list nat)
                 ((m - k) * Lsum a k + Bwp a k + S m) (gen132 (m - k))).
      rewrite (nfold_scal (list nat) (k + 1)
                 (fun v => pairge (safelist v (m - k))) (gen132 (m - k))).
      rewrite (nfold_scal (list nat) (k * (m - k) + Awp a k + S m)
                 (fun v => length (safelist v (m - k))) (gen132 (m - k))).
      unfold Bwptot, Ptot, sctot, card132, safelist. nia.
  - rewrite (nfold_four (list nat)
               (fun _ : list nat =>
                  (Bwptot (m - k) + card132 k * 0 + (k + 1) * Ptot (m - k)
                   + sctot (m - k) * (k * (m - k) + S m)
                   + card132 (m - k) * S m)%nat)
               (fun a => (sctot (m - k) * Awp a k)%nat)
               (fun a => (card132 (m - k) * (m - k) * Lsum a k)%nat)
               (fun a => (card132 (m - k) * Bwp a k)%nat)
               (gen132 k)).
    cbn beta.
    rewrite (nfold_const (list nat)
               (Bwptot (m - k) + card132 k * 0 + (k + 1) * Ptot (m - k)
                + sctot (m - k) * (k * (m - k) + S m)
                + card132 (m - k) * S m) (gen132 k)).
    rewrite (nfold_scal (list nat) (sctot (m - k)) (fun a => Awp a k)
               (gen132 k)).
    rewrite (nfold_scal (list nat) (card132 (m - k) * (m - k))
               (fun a => Lsum a k) (gen132 k)).
    rewrite (nfold_scal (list nat) (card132 (m - k)) (fun a => Bwp a k)
               (gen132 k)).
    unfold Awptot, Ltot, Bwptot, card132. nia.
Qed.

(* ------------------------------------------------------------------ *)

Lemma nfold_eight : forall (A : Type) (g1 g2 g3 g4 g5 g6 g7 g8 : A -> nat)
                           (l : list A),
  fold_right (fun x acc =>
    (g1 x + g2 x + g3 x + g4 x + g5 x + g6 x + g7 x + g8 x + acc)%nat) 0%nat l
  = (fold_right (fun x acc => (g1 x + acc)%nat) 0%nat l
     + fold_right (fun x acc => (g2 x + acc)%nat) 0%nat l
     + fold_right (fun x acc => (g3 x + acc)%nat) 0%nat l
     + fold_right (fun x acc => (g4 x + acc)%nat) 0%nat l
     + fold_right (fun x acc => (g5 x + acc)%nat) 0%nat l
     + fold_right (fun x acc => (g6 x + acc)%nat) 0%nat l
     + fold_right (fun x acc => (g7 x + acc)%nat) 0%nat l
     + fold_right (fun x acc => (g8 x + acc)%nat) 0%nat l)%nat.
Proof.
  intros A g1 g2 g3 g4 g5 g6 g7 g8. induction l as [|a l IH];
    cbn [fold_right]; [reflexivity|]. rewrite IH. lia.
Qed.

Lemma conv_add_r : forall f g1 g2 m,
  conv f (fun n => (g1 n + g2 n)%nat) m = (conv f g1 m + conv f g2 m)%nat.
Proof.
  intros f g1 g2 m.
  rewrite (conv_rev f (fun n => (g1 n + g2 n)%nat) m),
          (conv_rev f g1 m), (conv_rev f g2 m).
  apply conv_add_l.
Qed.

Lemma conv_scal_r : forall c f g m,
  conv f (fun n => (c * g n)%nat) m = (c * conv f g m)%nat.
Proof.
  intros c f g m.
  rewrite (conv_rev f (fun n => (c * g n)%nat) m), (conv_rev f g m).
  apply conv_scal_l.
Qed.

Lemma conv_catw : forall w m,
  conv card132 (fun n => (w n * card132 n)%nat) m = wsum w m.
Proof.
  intros w m. rewrite (conv_rev card132 (fun n => (w n * card132 n)%nat) m).
  apply conv_wsum.
Qed.

Lemma conv_wsum2 : forall f h m,
  conv (fun k => (f k * card132 k)%nat) (fun n => (h n * card132 n)%nat) m
  = wsum (fun k => (f k * h (m - k))%nat) m.
Proof.
  intros f h m. unfold conv, wsum. apply nfold_ext_in. intros k _.
  cbn beta. ring.
Qed.

Lemma conv_sctot : forall f m,
  (conv f sctot m + conv f card132 m
   = conv f (fun n => card132 (S n)) m)%nat.
Proof.
  intros f m. rewrite <- (conv_add_r f sctot card132 m).
  apply conv_ext; [intros k _; reflexivity|].
  intros n _. assert (K := sctot_card n). lia.
Qed.

Lemma conv_sctot_w : forall f m,
  (conv f (fun n => (n * sctot n)%nat) m
   + conv f (fun n => (n * card132 n)%nat) m
   = conv f (fun n => (n * card132 (S n))%nat) m)%nat.
Proof.
  intros f m.
  rewrite <- (conv_add_r f (fun n => (n * sctot n)%nat)
                (fun n => (n * card132 n)%nat) m).
  apply conv_ext; [intros k _; reflexivity|].
  intros n _. rewrite (sctot_card n). ring.
Qed.

Lemma conv_Ptot : forall f m,
  (conv f Ptot m + 2 * conv f (fun n => card132 (S n)) m
   = conv f (fun n => card132 (S (S n))) m)%nat.
Proof.
  intros f m.
  rewrite <- (conv_scal_r 2 f (fun n => card132 (S n)) m).
  rewrite <- (conv_add_r f Ptot (fun n => (2 * card132 (S n))%nat) m).
  apply conv_ext; [intros k _; reflexivity|].
  intros n _. assert (K := Ptot_closed n). lia.
Qed.

Lemma wsum_split3 : forall a b c n,
  wsum (fun k => (a * (k * k) + b * k + c)%nat) n
  = (a * wsum (fun k => (k * k)%nat) n + b * wsum (fun k => k) n
     + c * wsum (fun _ => 1%nat) n)%nat.
Proof.
  intros a b c n.
  rewrite <- (wsum_scal a (fun k => (k * k)%nat) n).
  rewrite <- (wsum_scal b (fun k => k) n).
  rewrite <- (wsum_scal c (fun _ => 1%nat) n).
  rewrite (wsum_add (fun k => (a * (k * k))%nat) (fun k => (b * k)%nat) n).
  rewrite (wsum_add (fun k => (a * (k * k) + b * k)%nat)
             (fun k => (c * 1)%nat) n).
  apply wsum_ext. intros k _. lia.
Qed.

Theorem Bwptot_conv : forall m,
  (4 * Bwptot (S m)
   = conv card132 (fun n => (4 * Bwptot n)%nat) m
     + 4 * conv (fun k => (S k * card132 k)%nat) Ptot m
     + 4 * conv (fun k => (k * card132 k)%nat) (fun n => (n * sctot n)%nat) m
     + 4 * S m * conv card132 sctot m
     + 2 * conv (fun k => (2 * Awptot k)%nat) sctot m
     + 2 * conv (fun k => (2 * Ltot k)%nat) (fun n => (n * card132 n)%nat) m
     + conv (fun k => (4 * Bwptot k)%nat) card132 m
     + 4 * S m * conv card132 card132 m)%nat.
Proof.
  intro m. rewrite (Bwptot_expand m).
  rewrite <- (conv_scal_l 4 (fun k => (S k * card132 k)%nat) Ptot m).
  rewrite <- (conv_scal_l (4 * S m) card132 sctot m).
  rewrite <- (conv_scal_l 2 (fun k => (2 * Awptot k)%nat) sctot m).
  rewrite <- (conv_scal_l 4 (fun k => (k * card132 k)%nat)
                (fun n => (n * sctot n)%nat) m).
  rewrite <- (conv_scal_l 2 (fun k => (2 * Ltot k)%nat)
                (fun n => (n * card132 n)%nat) m).
  rewrite <- (conv_scal_l (4 * S m) card132 card132 m).
  unfold conv.
  rewrite <- (nfold_eight nat
    (fun k => (card132 k * (4 * Bwptot (m - k)))%nat)
    (fun k => (4 * (S k * card132 k) * Ptot (m - k))%nat)
    (fun k => (4 * (k * card132 k) * ((m - k) * sctot (m - k)))%nat)
    (fun k => (4 * S m * card132 k * sctot (m - k))%nat)
    (fun k => (2 * (2 * Awptot k) * sctot (m - k))%nat)
    (fun k => (2 * (2 * Ltot k) * ((m - k) * card132 (m - k)))%nat)
    (fun k => (4 * Bwptot k * card132 (m - k))%nat)
    (fun k => (4 * S m * card132 k * card132 (m - k))%nat)
    (seq 0 (S m))).
  rewrite <- (nfold_scal nat 4 (fun k =>
    (card132 k * Bwptot (m - k)
     + card132 k * (k + 1) * Ptot (m - k)
     + sctot (m - k) * (card132 k * (k * (m - k) + S m) + Awptot k)
     + card132 (m - k) * ((m - k) * Ltot k + Bwptot k + card132 k * S m))%nat)
    (seq 0 (S m))).
  apply nfold_ext_in. intros k _. cbn beta. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* The value of each block. *)

Lemma conv_SA : forall m,
  (forall j, (j <= m)%nat ->
     (4 * Bwptot j + 2 * 4 ^ j
      = (2 * j + 2) * binomN (2 * j) j + j * 4 ^ j)%nat) ->
  (conv card132 (fun n => (4 * Bwptot n)%nat) m + 2 * Aconv m
   = 2 * wsum (fun k => (S k * S k)%nat) m + Bconv m)%nat.
Proof.
  intros m IH.
  assert (E : (conv card132 (fun n => (4 * Bwptot n)%nat) m
               + conv card132 (fun n => (2 * 4 ^ n)%nat) m
               = conv card132 (fun n => (2 * (S n * S n * card132 n)
                                         + n * 4 ^ n)%nat) m)%nat).
  { rewrite <- (conv_add_r card132 (fun n => (4 * Bwptot n)%nat)
                  (fun n => (2 * 4 ^ n)%nat) m).
    apply conv_ext; [intros k _; reflexivity|].
    intros n Hn. assert (K := IH n Hn).
    rewrite <- (card132_binom n) in K. nia. }
  rewrite (conv_scal_r 2 card132 (fun n => 4 ^ n) m) in E.
  rewrite (conv_rev card132 (fun n => 4 ^ n) m), (conv_aconv m) in E.
  rewrite (conv_add_r card132 (fun n => (2 * (S n * S n * card132 n))%nat)
             (fun n => (n * 4 ^ n)%nat) m) in E.
  rewrite (conv_scal_r 2 card132 (fun n => (S n * S n * card132 n)%nat) m) in E.
  rewrite (conv_catw (fun n => (S n * S n)%nat) m) in E.
  rewrite (conv_rev card132 (fun n => (n * 4 ^ n)%nat) m), (conv_bconv m) in E.
  exact E.
Qed.

Lemma conv_SF : forall m,
  (forall j, (j <= m)%nat ->
     (4 * Bwptot j + 2 * 4 ^ j
      = (2 * j + 2) * binomN (2 * j) j + j * 4 ^ j)%nat) ->
  (conv (fun k => (4 * Bwptot k)%nat) card132 m + 2 * Aconv m
   = 2 * wsum (fun k => (S k * S k)%nat) m + Bconv m)%nat.
Proof.
  intros m IH.
  assert (E : (conv (fun k => (4 * Bwptot k)%nat) card132 m
               + conv (fun k => (2 * 4 ^ k)%nat) card132 m
               = conv (fun k => (2 * (S k * S k * card132 k)
                                 + k * 4 ^ k)%nat) card132 m)%nat).
  { rewrite <- (conv_add_l (fun k => (4 * Bwptot k)%nat)
                  (fun k => (2 * 4 ^ k)%nat) card132 m).
    apply conv_ext; [|intros k _; reflexivity].
    intros n Hn. assert (K := IH n Hn).
    rewrite <- (card132_binom n) in K. nia. }
  rewrite (conv_scal_l 2 (fun k => 4 ^ k) card132 m), (conv_aconv m) in E.
  rewrite (conv_add_l (fun k => (2 * (S k * S k * card132 k))%nat)
             (fun k => (k * 4 ^ k)%nat) card132 m) in E.
  rewrite (conv_scal_l 2 (fun k => (S k * S k * card132 k)%nat) card132 m) in E.
  rewrite (conv_wsum (fun k => (S k * S k)%nat) m) in E.
  rewrite (conv_bconv m) in E.
  exact E.
Qed.

Lemma conv_SB : forall m,
  (conv (fun k => (S k * card132 k)%nat) Ptot m
   + S (S (S m)) * card132 (S (S m)) + 2 * wsum S (S m)
   = wsum S (S (S m)) + S (S m) * card132 (S m))%nat.
Proof.
  intro m.
  assert (E := conv_Ptot (fun k => (S k * card132 k)%nat) m).
  assert (H1 := conv_shift1 S m).
  assert (H2 := conv_shift2 S m).
  cbn beta in H1, H2. lia.
Qed.

Lemma conv_SC2 : forall m,
  (conv card132 sctot m + 2 * card132 (S m) = card132 (S (S m)))%nat.
Proof.
  intro m.
  assert (E := conv_sctot card132 m).
  rewrite (conv_cat m) in E.
  assert (H1 := conv_shift1 (fun _ => 1%nat) m).
  cbn beta in H1.
  rewrite (wsum_const 1 (S m)) in H1.
  assert (Hb : conv (fun k => (1 * card132 k)%nat) (fun n => card132 (S n)) m
             = conv card132 (fun n => card132 (S n)) m).
  { apply conv_ext; [intros k _; lia | intros n _; reflexivity]. }
  rewrite Hb in H1. lia.
Qed.

Lemma conv_SC1 : forall m,
  (conv (fun k => (k * card132 k)%nat) (fun n => (n * sctot n)%nat) m
   + wsum (fun k => (k * (m - k))%nat) m
   + wsum (fun k => (k * k)%nat) (S m)
   = m * wsum (fun k => k) (S m) + S m * card132 (S m))%nat.
Proof.
  intro m.
  assert (E := conv_sctot_w (fun k => (k * card132 k)%nat) m).
  rewrite (conv_wsum2 (fun k => k) (fun n => n) m) in E.
  assert (K : (conv (fun k => (k * card132 k)%nat)
                 (fun n => (n * card132 (S n))%nat) m
               + conv (fun k => (k * k * card132 k)%nat)
                   (fun n => card132 (S n)) m
               = m * conv (fun k => (k * card132 k)%nat)
                     (fun n => card132 (S n)) m)%nat).
  { unfold conv.
    rewrite <- (fold_add_split nat
                  (fun k => ((k * card132 k)
                             * ((m - k) * card132 (S (m - k))))%nat)
                  (fun k => ((k * k * card132 k) * card132 (S (m - k)))%nat)
                  (seq 0 (S m))).
    rewrite <- (nfold_scal nat m
                  (fun k => ((k * card132 k) * card132 (S (m - k)))%nat)
                  (seq 0 (S m))).
    apply nfold_ext_in. intros k Hk. apply in_seq in Hk.
    assert (Hk' : (k + (m - k))%nat = m) by lia.
    transitivity ((k + (m - k))
                  * (k * card132 k * card132 (S (m - k))))%nat; [ring|].
    rewrite Hk'. ring. }
  assert (H1 := conv_shift1 (fun k => (k * k)%nat) m).
  assert (H2 := conv_shift1 (fun k => k) m).
  cbn beta in H1, H2. nia.
Qed.

Lemma conv_SD : forall m,
  (conv (fun k => (2 * Awptot k)%nat) sctot m
   + S m * (S m + 1) * card132 (S m)
   + wsum (fun k => (k * (k + 1))%nat) m
   + 4 ^ (S m) + Aconv m + wsum (fun k => (3 * k + 1)%nat) (S m)
   = wsum (fun k => (k * (k + 1))%nat) (S m) + Aconv (S m)
     + (3 * S m + 1) * card132 (S m)
     + wsum (fun k => (3 * k + 1)%nat) m)%nat.
Proof.
  intro m.
  assert (E : (conv (fun k => (2 * Awptot k)%nat) sctot m
               + conv (fun k => ((3 * k + 1) * card132 k)%nat) sctot m
               = conv (fun k => (k * (k + 1) * card132 k)%nat) sctot m
                 + conv (fun k => 4 ^ k) sctot m)%nat).
  { rewrite <- (conv_add_l (fun k => (2 * Awptot k)%nat)
                  (fun k => ((3 * k + 1) * card132 k)%nat) sctot m).
    rewrite <- (conv_add_l (fun k => (k * (k + 1) * card132 k)%nat)
                  (fun k => 4 ^ k) sctot m).
    apply conv_ext; [|intros n _; reflexivity].
    intros n _. assert (K := Awptot_closed n).
    rewrite <- (card132_binom n) in K. nia. }
  assert (F1 := conv_sctot (fun k => ((3 * k + 1) * card132 k)%nat) m).
  assert (F2 := conv_sctot (fun k => (k * (k + 1) * card132 k)%nat) m).
  assert (F3 := conv_sctot (fun k => 4 ^ k) m).
  rewrite (conv_wsum (fun k => (3 * k + 1)%nat) m) in F1.
  rewrite (conv_wsum (fun k => (k * (k + 1))%nat) m) in F2.
  rewrite (conv_aconv m) in F3.
  assert (G1 := conv_shift1 (fun k => (3 * k + 1)%nat) m).
  assert (G2 := conv_shift1 (fun k => (k * (k + 1))%nat) m).
  assert (G3 := conv_a1 m).
  cbn beta in G1, G2. lia.
Qed.

Lemma conv_SE : forall m,
  (conv (fun k => (2 * Ltot k)%nat) (fun n => (n * card132 n)%nat) m
   + wsum (fun k => (S k * (m - k))%nat) m + Bconv m
   = m * Aconv m)%nat.
Proof.
  intro m.
  assert (E : (conv (fun k => (2 * Ltot k)%nat)
                 (fun n => (n * card132 n)%nat) m
               + conv (fun k => (S k * card132 k)%nat)
                   (fun n => (n * card132 n)%nat) m
               = conv (fun k => 4 ^ k) (fun n => (n * card132 n)%nat) m)%nat).
  { rewrite <- (conv_add_l (fun k => (2 * Ltot k)%nat)
                  (fun k => (S k * card132 k)%nat)
                  (fun n => (n * card132 n)%nat) m).
    apply conv_ext; [|intros n _; reflexivity].
    intros n _. assert (K := Ltot_closed n).
    rewrite <- (card132_binom n) in K. lia. }
  rewrite (conv_wsum2 (fun k => S k) (fun n => n) m) in E.
  assert (R := conv_rbconv m). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Polynomial weights, reduced to the three basic ones. *)

Lemma wsum_sqw : forall m,
  wsum (fun k => (S k * S k)%nat) m
  = (wsum (fun k => (k * k)%nat) m + 2 * wsum (fun k => k) m
     + wsum (fun _ => 1%nat) m)%nat.
Proof.
  intro m.
  assert (K := wsum_split3 1 2 1 m).
  assert (E : wsum (fun k => (1 * (k * k) + 2 * k + 1)%nat) m
            = wsum (fun k => (S k * S k)%nat) m)
    by (apply wsum_ext; intros k _; lia).
  lia.
Qed.

Lemma wsum_3k1 : forall n,
  wsum (fun k => (3 * k + 1)%nat) n
  = (3 * wsum (fun k => k) n + wsum (fun _ => 1%nat) n)%nat.
Proof.
  intro n.
  assert (K := wsum_split3 0 3 1 n).
  assert (E : wsum (fun k => (0 * (k * k) + 3 * k + 1)%nat) n
            = wsum (fun k => (3 * k + 1)%nat) n)
    by (apply wsum_ext; intros k _; lia).
  lia.
Qed.

Lemma wsum_kk1 : forall n,
  wsum (fun k => (k * (k + 1))%nat) n
  = (wsum (fun k => (k * k)%nat) n + wsum (fun k => k) n)%nat.
Proof.
  intro n.
  assert (K := wsum_split3 1 1 0 n).
  assert (E : wsum (fun k => (1 * (k * k) + 1 * k + 0)%nat) n
            = wsum (fun k => (k * (k + 1))%nat) n)
    by (apply wsum_ext; intros k _; lia).
  lia.
Qed.

Lemma wsum_Skmk : forall m,
  wsum (fun k => (S k * (m - k))%nat) m
  = (wsum (fun k => (k * (m - k))%nat) m + wsum (fun k => k) m)%nat.
Proof.
  intro m.
  assert (R : wsum (fun k => k) m = wsum (fun k => (m - k)%nat) m)
    by apply wsum_rev.
  rewrite R.
  rewrite (wsum_add (fun k => (k * (m - k))%nat) (fun k => (m - k)%nat) m).
  apply wsum_ext. intros k _. ring.
Qed.

(* ------------------------------------------------------------------ *)

Lemma Bwptot_step : forall m,
  (forall j, (j <= m)%nat ->
     (4 * Bwptot j + 2 * 4 ^ j
      = (2 * j + 2) * binomN (2 * j) j + j * 4 ^ j)%nat) ->
  (4 * Bwptot (S m) + 2 * 4 ^ (S m)
   = (2 * S m + 2) * binomN (2 * S m) (S m) + S m * 4 ^ (S m))%nat.
Proof.
  intros m IH.
  assert (HC := Bwptot_conv m).
  assert (HA := conv_SA m IH).
  assert (HF := conv_SF m IH).
  assert (HB := conv_SB m).
  assert (HC1 := conv_SC1 m).
  assert (HC2 := conv_SC2 m).
  assert (HD := conv_SD m).
  assert (HE := conv_SE m).
  assert (HG := conv_cat m).
  assert (HC2m := f_equal (Nat.mul m) HC2).
  assert (HGm := f_equal (Nat.mul m) HG).
  (* polynomial weights *)
  rewrite (wsum_sqw m) in HA, HF.
  rewrite (wsum_3k1 m), (wsum_3k1 (S m)), (wsum_kk1 m), (wsum_kk1 (S m)) in HD.
  rewrite (wsum_Skmk m) in HE.
  assert (W1 := wsum_S_sym (S m)).
  assert (W2 := wsum_S_sym (S (S m))).
  (* basic weights *)
  assert (V1 := wsum_const 1 m).
  assert (V2 := wsum_const 1 (S m)).
  assert (V3 := wsum_id_val m).
  assert (V4 := wsum_id_val (S m)).
  assert (V4m := f_equal (Nat.mul m) V4).
  assert (V5 := wsum_sq_val m).
  assert (V6 := wsum_sq_val (S m)).
  assert (V7 := wsum_kmk_val m).
  (* catalan ratios *)
  assert (R2 := card132_ratio (S m)).
  assert (R2m := f_equal (Nat.mul m) R2).
  assert (R3 := card132_ratio (S (S m))).
  (* closed forms of the power convolutions *)
  assert (P1 := Aconv_closed m).
  assert (P2 := Aconv_closed (S m)).
  assert (P1m := f_equal (Nat.mul m) P1).
  assert (P3 := Bconv_val m).
  assert (P4 := cbi_ratio m).
  (* binomials against the class *)
  assert (B1 := card132_binom (S m)).
  assert (B1m := f_equal (Nat.mul m) B1).
  assert (B2 := card132_binom (S (S m))).
  unfold cb in P3, P4.
  replace (4 ^ S (S m))%nat with (4 * 4 ^ S m)%nat in P2
    by (cbn [Nat.pow]; ring).
  replace (4 ^ S m)%nat with (4 * 4 ^ m)%nat in *
    by (cbn [Nat.pow]; ring).
  lia.
Qed.

Theorem Bwptot_closed_upto : forall N m, (m <= N)%nat ->
  (4 * Bwptot m + 2 * 4 ^ m
   = (2 * m + 2) * binomN (2 * m) m + m * 4 ^ m)%nat.
Proof.
  induction N as [|N IHN]; intros m Hm.
  - assert (E : m = 0%nat) by lia. subst m. vm_compute. reflexivity.
  - destruct (le_lt_dec m N) as [H|H]; [apply IHN; exact H|].
    assert (EM : m = S N) by lia. subst m.
    apply Bwptot_step. intros j Hj. apply IHN. lia.
Qed.

Theorem Bwptot_closed : forall m,
  (4 * Bwptot m + 2 * 4 ^ m
   = (2 * m + 2) * binomN (2 * m) m + m * 4 ^ m)%nat.
Proof. intro m. apply (Bwptot_closed_upto m m). lia. Qed.

Theorem Btot_closed : BTOT_CLOSED.
Proof.
  intro M.
  assert (H1 := Btot_split M).
  assert (H2 := Atot_closed M).
  assert (H3 := Bwptot_closed M).
  lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The clipped statistic in closed form, and the d = 3 diagonal. *)


(* The clipped statistic, transposed.  Summing over the node to the left first
   leaves a sum over each node of a quantity depending only on H at that node,
   so the clipped total reduces to the level sum and the second moment of H. *)

Lemma swap_tri : forall (f : nat -> nat -> nat) M,
  fold_right (fun y acc =>
    (fold_right (fun z acc' => (f y z + acc')%nat) 0%nat (seq 1 y) + acc)%nat)
    0%nat (seq 0 (S M))
  = fold_right (fun z acc =>
      (fold_right (fun y acc' => (f y z + acc')%nat) 0%nat (seq z (S M - z))
       + acc)%nat) 0%nat (seq 1 M).
Proof.
  intros f M. induction M as [|M IH]; [reflexivity|].
  assert (EL : fold_right (fun y acc =>
      (fold_right (fun z acc' => (f y z + acc')%nat) 0%nat (seq 1 y) + acc)%nat)
      0%nat (seq 0 (S (S M)))
    = (fold_right (fun y acc =>
        (fold_right (fun z acc' => (f y z + acc')%nat) 0%nat (seq 1 y)
         + acc)%nat) 0%nat (seq 0 (S M))
       + fold_right (fun z acc' => (f (S M) z + acc')%nat) 0%nat
                    (seq 1 (S M)))%nat).
  { rewrite (seq_snoc (S M) 0).
    rewrite (nfold_app nat (fun y =>
      fold_right (fun z acc' => (f y z + acc')%nat) 0%nat (seq 1 y))).
    rewrite (nfold_single nat (fun y =>
      fold_right (fun z acc' => (f y z + acc')%nat) 0%nat (seq 1 y)) (0 + S M)).
    cbn beta. replace (0 + S M)%nat with (S M) by lia. reflexivity. }
  assert (EI : forall z, (1 <= z)%nat -> (z <= M)%nat ->
      fold_right (fun y acc' => (f y z + acc')%nat) 0%nat
                 (seq z (S (S M) - z))
      = (fold_right (fun y acc' => (f y z + acc')%nat) 0%nat (seq z (S M - z))
         + f (S M) z)%nat).
  { intros z Hz1 HzM.
    replace (S (S M) - z)%nat with (S (S M - z)) by lia.
    rewrite (seq_snoc (S M - z) z).
    rewrite (nfold_app nat (fun y => f y z)).
    rewrite (nfold_single nat (fun y => f y z) (z + (S M - z))).
    cbn beta. replace (z + (S M - z))%nat with (S M) by lia. reflexivity. }
  assert (ER : fold_right (fun z acc =>
      (fold_right (fun y acc' => (f y z + acc')%nat) 0%nat
                  (seq z (S (S M) - z)) + acc)%nat) 0%nat (seq 1 (S M))
    = (fold_right (fun z acc =>
        (fold_right (fun y acc' => (f y z + acc')%nat) 0%nat (seq z (S M - z))
         + acc)%nat) 0%nat (seq 1 M)
       + fold_right (fun z acc' => (f (S M) z + acc')%nat) 0%nat
                    (seq 1 (S M)))%nat).
  { rewrite (seq_snoc M 1) at 1.
    rewrite (nfold_app nat (fun z =>
      fold_right (fun y acc' => (f y z + acc')%nat) 0%nat
                 (seq z (S (S M) - z)))).
    rewrite (nfold_single nat (fun z =>
      fold_right (fun y acc' => (f y z + acc')%nat) 0%nat
                 (seq z (S (S M) - z))) (1 + M)).
    cbn beta.
    replace (1 + M)%nat with (S M) by lia.
    replace (S (S M) - S M)%nat with 1%nat by lia.
    replace (seq (S M) 1) with ((S M) :: nil) by reflexivity.
    rewrite (nfold_single nat (fun y => f y (S M)) (S M)).
    assert (EB : fold_right (fun z acc =>
        (fold_right (fun y acc' => (f y z + acc')%nat) 0%nat
                    (seq z (S (S M) - z)) + acc)%nat) 0%nat (seq 1 M)
      = (fold_right (fun z acc =>
          (fold_right (fun y acc' => (f y z + acc')%nat) 0%nat (seq z (S M - z))
           + acc)%nat) 0%nat (seq 1 M)
         + fold_right (fun z acc => (f (S M) z + acc)%nat) 0%nat (seq 1 M))%nat).
    { rewrite <- (fold_add_split nat
        (fun z => fold_right (fun y acc' => (f y z + acc')%nat) 0%nat
                             (seq z (S M - z)))
        (fun z => f (S M) z) (seq 1 M)).
      apply nfold_ext_in. intros z Hz. apply in_seq in Hz. apply EI; lia. }
    rewrite EB.
    assert (EC : fold_right (fun z acc' => (f (S M) z + acc')%nat) 0%nat
                            (seq 1 (S M))
      = (fold_right (fun z acc => (f (S M) z + acc)%nat) 0%nat (seq 1 M)
         + f (S M) (S M))%nat).
    { rewrite (seq_snoc M 1).
      rewrite (nfold_app nat (fun z => f (S M) z)).
      rewrite (nfold_single nat (fun z => f (S M) z) (1 + M)).
      cbn beta. replace (1 + M)%nat with (S M) by lia. reflexivity. }
    rewrite EC. lia. }
  rewrite EL, ER, IH. reflexivity.
Qed.

Definition tri2 (M : nat) : nat :=
  fold_right (fun z acc => (tri (z - 1) + acc)%nat) 0%nat (seq 1 M).

Lemma tri2_val : forall M, (6 * tri2 M + M = M * M * M)%nat.
Proof.
  induction M as [|M IH]; [reflexivity|].
  assert (E : tri2 (S M) = (tri2 M + tri M)%nat).
  { unfold tri2 at 1. rewrite (seq_snoc M 1).
    rewrite (nfold_app nat (fun z => tri (z - 1))).
    rewrite (nfold_single nat (fun z => tri (z - 1)) (1 + M)).
    cbn beta. replace (1 + M - 1)%nat with M by lia. reflexivity. }
  rewrite E. assert (Ht := tri_val M). nia.
Qed.

Lemma minsum_val : forall z h M, (1 <= z)%nat -> (z <= h)%nat -> (h <= M)%nat ->
  (fold_right (fun y acc => (Nat.min y h + acc)%nat) 0%nat (seq z (S M - z))
   + tri (z - 1)
   = tri h + (M - h) * h)%nat.
Proof.
  intros z h M H1 H2 H3.
  replace (S M - z)%nat with ((S h - z) + (M - h))%nat by lia.
  rewrite (seq_break (S h - z) (M - h) z).
  rewrite (nfold_app nat (fun y => Nat.min y h)).
  replace (z + (S h - z))%nat with (S h) by lia.
  assert (A : fold_right (fun y acc => (Nat.min y h + acc)%nat) 0%nat
                         (seq z (S h - z))
            = fold_right (fun y acc => (y + acc)%nat) 0%nat (seq z (S h - z))).
  { apply nfold_ext_in. intros y Hy. apply in_seq in Hy. lia. }
  assert (B : fold_right (fun y acc => (Nat.min y h + acc)%nat) 0%nat
                         (seq (S h) (M - h))
            = ((M - h) * h)%nat).
  { transitivity (fold_right (fun y acc => (h + acc)%nat) 0%nat
                             (seq (S h) (M - h))).
    - apply nfold_ext_in. intros y Hy. apply in_seq in Hy. lia.
    - rewrite (nfold_const nat h (seq (S h) (M - h))), length_seq. lia. }
  assert (LS : seq 0 (S h) = seq 0 z ++ seq z (S h - z)).
  { replace (S h) with (z + (S h - z))%nat at 1 by lia.
    rewrite (seq_break z (S h - z) 0). reflexivity. }
  assert (C : (fold_right (fun y acc => (y + acc)%nat) 0%nat (seq z (S h - z))
               + tri (z - 1) = tri h)%nat).
  { unfold tri. replace (S (z - 1)) with z by lia.
    rewrite LS. rewrite (nfold_app nat (fun y => y)). lia. }
  rewrite A, B. lia.
Qed.

Definition Hsq (u : list nat) (M : nat) : nat :=
  fold_right (fun z acc => (Hu u M z * Hu u M z + acc)%nat) 0%nat (seq 1 M).

Definition Hsqtot (M : nat) : nat :=
  fold_right (fun u acc => (Hsq u M + acc)%nat) 0%nat (gen132 M).

Lemma Cw_Hsq : forall u M,
  (2 * Cw u M + Hsq u M + 2 * tri2 M = (2 * M + 1) * Awp u M)%nat.
Proof.
  intros u M.
  assert (Sw := swap_tri (fun y z => Nat.min y (Hu u M z)) M).
  cbn beta in Sw.
  assert (E1 : Cw u M
    = fold_right (fun z acc =>
        (fold_right (fun y acc' => (Nat.min y (Hu u M z) + acc')%nat) 0%nat
                    (seq z (S M - z)) + acc)%nat) 0%nat (seq 1 M)).
  { unfold Cw, Cin. rewrite <- Sw. reflexivity. }
  assert (E3 : (Cw u M + tri2 M
    = fold_right (fun z acc =>
        (tri (Hu u M z) + (M - Hu u M z) * Hu u M z + acc)%nat) 0%nat
        (seq 1 M))%nat).
  { rewrite E1. unfold tri2.
    rewrite <- (fold_add_split nat
      (fun z => fold_right (fun y acc' => (Nat.min y (Hu u M z) + acc')%nat)
                           0%nat (seq z (S M - z)))
      (fun z => tri (z - 1)) (seq 1 M)).
    apply nfold_ext_in. intros z Hz. apply in_seq in Hz.
    apply minsum_val; [lia | apply Hu_ge; lia | apply Hu_le_cap]. }
  assert (E4 : (2 * fold_right (fun z acc =>
      (tri (Hu u M z) + (M - Hu u M z) * Hu u M z + acc)%nat) 0%nat (seq 1 M)
    + Hsq u M = (2 * M + 1) * Awp u M)%nat).
  { unfold Hsq, Awp.
    rewrite <- (nfold_scal nat 2
      (fun z => (tri (Hu u M z) + (M - Hu u M z) * Hu u M z)%nat) (seq 1 M)).
    rewrite <- (nfold_scal nat (2 * M + 1) (fun z => Hu u M z) (seq 1 M)).
    rewrite <- (fold_add_split nat
      (fun z => (2 * (tri (Hu u M z) + (M - Hu u M z) * Hu u M z))%nat)
      (fun z => (Hu u M z * Hu u M z)%nat) (seq 1 M)).
    apply nfold_ext_in. intros z Hz. apply in_seq in Hz.
    assert (Hc := Hu_le_cap u M z).
    assert (Ht := tri_val (Hu u M z)).
    remember (Hu u M z) as h eqn:Eh.
    remember (M - h) as d eqn:Ed.
    assert (EM : M = (h + d)%nat) by lia.
    rewrite EM. nia. }
  lia.
Qed.

Lemma Ctot_Hsq : forall M,
  (2 * Ctot M + Hsqtot M + 2 * card132 M * tri2 M
   = (2 * M + 1) * Awptot M)%nat.
Proof.
  intro M.
  assert (E : (2 * Ctot M + Hsqtot M + 2 * card132 M * tri2 M)%nat
    = fold_right (fun u acc =>
        (2 * Cw u M + Hsq u M + 2 * tri2 M + acc)%nat) 0%nat (gen132 M)).
  { rewrite (nfold_three (list nat) (fun u => (2 * Cw u M)%nat)
               (fun u => Hsq u M) (fun _ : list nat => (2 * tri2 M)%nat)
               (gen132 M)).
    cbn beta.
    rewrite (nfold_scal (list nat) 2 (fun u => Cw u M) (gen132 M)).
    rewrite (nfold_const (list nat) (2 * tri2 M) (gen132 M)).
    unfold Ctot, Hsqtot, card132. nia. }
  rewrite E. unfold Awptot.
  rewrite <- (nfold_scal (list nat) (2 * M + 1) (fun u => Awp u M) (gen132 M)).
  apply nfold_ext_in. intros u _. apply Cw_Hsq.
Qed.

(* ------------------------------------------------------------------ *)
(* The second moment of H under the max-split. *)

Lemma seq_split_hi : forall al bl,
  seq 1 (al + S bl) = seq 1 bl ++ seq (S bl) al ++ seq (al + S bl) 1.
Proof.
  intros al bl.
  replace (al + S bl)%nat with (bl + (al + 1))%nat by lia.
  rewrite (seq_break bl (al + 1) 1).
  replace (1 + bl)%nat with (S bl) by lia.
  rewrite (seq_break al 1 (S bl)).
  replace (S bl + al)%nat with (bl + (al + 1))%nat by lia.
  reflexivity.
Qed.

Lemma Hsqsum_hi_block : forall a b,
  is_perm a (length a) -> is_perm b (length b) ->
  fold_right (fun z acc =>
    (Hu (midmax a b) (length a + S (length b)) z
     * Hu (midmax a b) (length a + S (length b)) z + acc)%nat) 0%nat
    (seq (S (length b)) (length a))
  = (length a * (length b * length b)
     + 2 * length b * Awp a (length a) + Hsq a (length a))%nat.
Proof.
  intros a b Hpa Hpb.
  replace (seq (S (length b)) (length a))
    with (map (fun t => t + length b) (seq 1 (length a)))
    by (rewrite seq_add_map; reflexivity).
  rewrite (nfold_map_gen nat nat
             (fun z => (Hu (midmax a b) (length a + S (length b)) z
                        * Hu (midmax a b) (length a + S (length b)) z)%nat)
             (fun t => t + length b) (seq 1 (length a))).
  cbn beta.
  transitivity (fold_right (fun t acc =>
      (length b * length b + 2 * length b * Hu a (length a) t
       + Hu a (length a) t * Hu a (length a) t + acc)%nat) 0%nat
      (seq 1 (length a))).
  - apply nfold_ext_in. intros t Ht. apply in_seq in Ht.
    rewrite (Hu_midmax_hi a b (t + length b) Hpa Hpb ltac:(lia) ltac:(lia)).
    replace (t + length b - length b)%nat with t by lia. ring.
  - rewrite (nfold_three nat (fun _ : nat => (length b * length b)%nat)
               (fun t => (2 * length b * Hu a (length a) t)%nat)
               (fun t => (Hu a (length a) t * Hu a (length a) t)%nat)
               (seq 1 (length a))).
    cbn beta.
    rewrite (nfold_const nat (length b * length b) (seq 1 (length a))),
            length_seq.
    rewrite (nfold_scal nat (2 * length b) (fun t => Hu a (length a) t)
               (seq 1 (length a))).
    unfold Awp, Hsq. lia.
Qed.

Lemma Hsqsum_lo_block : forall a b,
  is_perm a (length a) -> is_perm b (length b) ->
  (fold_right (fun z acc =>
    (Hu (midmax a b) (length a + S (length b)) z
     * Hu (midmax a b) (length a + S (length b)) z + acc)%nat) 0%nat
    (seq 1 (length b))
   + length (safelist b (length b)) * (length b * length b)
   = Hsq b (length b)
     + length (safelist b (length b))
       * ((length a + S (length b)) * (length a + S (length b))))%nat.
Proof.
  intros a b Hpa Hpb.
  assert (E : (fold_right (fun z acc =>
        (Hu (midmax a b) (length a + S (length b)) z
         * Hu (midmax a b) (length a + S (length b)) z + acc)%nat) 0%nat
        (seq 1 (length b))
      + fold_right (fun z acc =>
          ((if safeb b z then (length b * length b)%nat else 0) + acc)%nat)
          0%nat (seq 1 (length b))
      = fold_right (fun z acc =>
          (Hu b (length b) z * Hu b (length b) z + acc)%nat) 0%nat
          (seq 1 (length b))
        + fold_right (fun z acc =>
            ((if safeb b z
              then ((length a + S (length b))
                    * (length a + S (length b)))%nat
              else 0) + acc)%nat) 0%nat (seq 1 (length b)))%nat).
  { rewrite <- (fold_add_split nat
      (fun z => (Hu (midmax a b) (length a + S (length b)) z
                 * Hu (midmax a b) (length a + S (length b)) z)%nat)
      (fun z => if safeb b z then (length b * length b)%nat else 0)
      (seq 1 (length b))).
    rewrite <- (fold_add_split nat
      (fun z => (Hu b (length b) z * Hu b (length b) z)%nat)
      (fun z => if safeb b z
                then ((length a + S (length b))
                      * (length a + S (length b)))%nat
                else 0) (seq 1 (length b))).
    apply nfold_ext_in. intros z Hz. apply in_seq in Hz.
    destruct (safeb b z) eqn:Es.
    - assert (Hs : safe_at b z) by (apply safeb_spec; exact Es).
      rewrite (Hu_midmax_lo_safe a b z ltac:(lia) ltac:(lia) Hs).
      assert (Eb := proj1 (safe_iff_Hu b z Hpb) Hs). rewrite Eb. ring.
    - assert (Hns : ~ safe_at b z).
      { intro C. assert (K : safeb b z = true) by (apply safeb_spec; exact C).
        rewrite Es in K. discriminate. }
      rewrite (Hu_midmax_lo_unsafe a b z ltac:(lia) ltac:(lia) Hpb Hns). ring. }
  rewrite (nfold_filter nat (safeb b)
             (fun _ : nat => (length b * length b)%nat)
             (seq 1 (length b))) in E.
  rewrite (nfold_filter nat (safeb b)
             (fun _ : nat => ((length a + S (length b))
                              * (length a + S (length b)))%nat)
             (seq 1 (length b))) in E.
  rewrite (nfold_const nat (length b * length b)
             (filter (safeb b) (seq 1 (length b)))) in E.
  rewrite (nfold_const nat ((length a + S (length b))
                            * (length a + S (length b)))
             (filter (safeb b) (seq 1 (length b)))) in E.
  change (filter (safeb b) (seq 1 (length b)))
    with (safelist b (length b)) in E.
  unfold Hsq. nia.
Qed.

Theorem Hsq_midmax : forall a b,
  is_perm a (length a) -> is_perm b (length b) ->
  (Hsq (midmax a b) (length a + S (length b))
   + length (safelist b (length b)) * (length b * length b)
   = Hsq b (length b)
     + length (safelist b (length b))
       * ((length a + S (length b)) * (length a + S (length b)))
     + (length a * (length b * length b)
        + 2 * length b * Awp a (length a) + Hsq a (length a))
     + (length a + S (length b)) * (length a + S (length b)))%nat.
Proof.
  intros a b Hpa Hpb.
  assert (HL := Hsqsum_lo_block a b Hpa Hpb).
  assert (HH := Hsqsum_hi_block a b Hpa Hpb).
  unfold Hsq at 1. rewrite (seq_split_hi (length a) (length b)).
  rewrite !(nfold_app nat
    (fun z => (Hu (midmax a b) (length a + S (length b)) z
               * Hu (midmax a b) (length a + S (length b)) z)%nat)).
  replace (seq (length a + S (length b)) 1)
    with ((length a + S (length b)) :: nil) by reflexivity.
  rewrite (nfold_single nat
    (fun z => (Hu (midmax a b) (length a + S (length b)) z
               * Hu (midmax a b) (length a + S (length b)) z)%nat)
    (length a + S (length b))).
  cbn beta. rewrite Hu_top. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The level sum of the second moment. *)

Lemma nfold_six : forall (A : Type) (g1 g2 g3 g4 g5 g6 : A -> nat) (l : list A),
  fold_right (fun x acc =>
    (g1 x + g2 x + g3 x + g4 x + g5 x + g6 x + acc)%nat) 0%nat l
  = (fold_right (fun x acc => (g1 x + acc)%nat) 0%nat l
     + fold_right (fun x acc => (g2 x + acc)%nat) 0%nat l
     + fold_right (fun x acc => (g3 x + acc)%nat) 0%nat l
     + fold_right (fun x acc => (g4 x + acc)%nat) 0%nat l
     + fold_right (fun x acc => (g5 x + acc)%nat) 0%nat l
     + fold_right (fun x acc => (g6 x + acc)%nat) 0%nat l)%nat.
Proof.
  intros A g1 g2 g3 g4 g5 g6. induction l as [|a l IH];
    cbn [fold_right]; [reflexivity|]. rewrite IH. lia.
Qed.

Theorem Hsqtot_expand : forall m,
  (Hsqtot (S m)
   + fold_right (fun k acc =>
       (card132 k * ((m - k) * (m - k) * sctot (m - k)) + acc)%nat) 0%nat
       (seq 0 (S m))
   = fold_right (fun k acc =>
       (card132 k * Hsqtot (m - k)
        + S m * S m * (card132 k * sctot (m - k))
        + k * card132 k * ((m - k) * (m - k) * card132 (m - k))
        + 2 * (Awptot k * ((m - k) * card132 (m - k)))
        + Hsqtot k * card132 (m - k)
        + S m * S m * (card132 k * card132 (m - k))
        + acc)%nat) 0%nat (seq 0 (S m)))%nat.
Proof.
  intro m. unfold Hsqtot at 1.
  rewrite (nfold_pairs132 m (fun w => Hsq w (S m))).
  rewrite <- (fold_add_split nat
    (fun k => fold_right (fun a acc' =>
       (fold_right (fun v acc'' => (Hsq (midmax a v) (S m) + acc'')%nat) 0%nat
                   (gen132 (m - k)) + acc')%nat) 0%nat (gen132 k))
    (fun k => (card132 k * ((m - k) * (m - k) * sctot (m - k)))%nat)
    (seq 0 (S m))).
  apply nfold_ext_in. intros k Hk. apply in_seq in Hk. destruct Hk as [_ Hk].
  assert (HkM : (k <= m)%nat) by lia.
  assert (Ecorr : ((m - k) * (m - k) * sctot (m - k))%nat
    = fold_right (fun v acc =>
        (length (safelist v (m - k)) * ((m - k) * (m - k)) + acc)%nat) 0%nat
        (gen132 (m - k))).
  { transitivity (fold_right (fun v acc =>
        ((m - k) * (m - k) * length (safelist v (m - k)) + acc)%nat) 0%nat
        (gen132 (m - k))).
    - rewrite (nfold_scal (list nat) ((m - k) * (m - k))
                 (fun v => length (safelist v (m - k))) (gen132 (m - k))).
      unfold sctot, safelist. reflexivity.
    - apply nfold_ext_in. intros v _. ring. }
  assert (INNER : forall a, In a (gen132 k) ->
    (fold_right (fun v acc => (Hsq (midmax a v) (S m) + acc)%nat) 0%nat
                (gen132 (m - k))
     + ((m - k) * (m - k) * sctot (m - k))
     = Hsqtot (m - k) + S m * S m * sctot (m - k)
       + card132 (m - k) * (k * ((m - k) * (m - k))
                            + 2 * (m - k) * Awp a k + Hsq a k)
       + card132 (m - k) * (S m * S m))%nat).
  { intros a Ha.
    assert (Hpa0 : is_perm a k) by (apply gen132_perm; exact Ha).
    assert (Hla : length a = k) by (apply (perm_len a k); exact Hpa0).
    assert (Hpa : is_perm a (length a)) by (rewrite Hla; exact Hpa0).
    rewrite Ecorr.
    rewrite <- (fold_add_split (list nat) (fun v => Hsq (midmax a v) (S m))
      (fun v => (length (safelist v (m - k)) * ((m - k) * (m - k)))%nat)
      (gen132 (m - k))).
    transitivity (fold_right (fun v acc =>
        (Hsq v (m - k) + length (safelist v (m - k)) * (S m * S m)
         + (k * ((m - k) * (m - k)) + 2 * (m - k) * Awp a k + Hsq a k)
         + (S m * S m) + acc)%nat) 0%nat (gen132 (m - k))).
    - apply nfold_ext_in. intros v Hv.
      assert (Hpv0 : is_perm v (m - k)) by (apply gen132_perm; exact Hv).
      assert (Hlv : length v = (m - k)%nat)
        by (apply (perm_len v (m - k)); exact Hpv0).
      assert (Hpv : is_perm v (length v)) by (rewrite Hlv; exact Hpv0).
      assert (K := Hsq_midmax a v Hpa Hpv).
      rewrite Hla, Hlv in K.
      replace (k + S (m - k))%nat with (S m) in K by lia.
      lia.
    - rewrite (nfold_four (list nat) (fun v => Hsq v (m - k))
                 (fun v => (length (safelist v (m - k)) * (S m * S m))%nat)
                 (fun _ : list nat => (k * ((m - k) * (m - k))
                                       + 2 * (m - k) * Awp a k + Hsq a k)%nat)
                 (fun _ : list nat => (S m * S m)%nat) (gen132 (m - k))).
      cbn beta.
      transitivity (Hsqtot (m - k)
        + (S m * S m) * fold_right (fun v acc =>
             (length (safelist v (m - k)) + acc)%nat) 0%nat (gen132 (m - k))
        + card132 (m - k) * (k * ((m - k) * (m - k))
                             + 2 * (m - k) * Awp a k + Hsq a k)
        + card132 (m - k) * (S m * S m))%nat.
      + rewrite <- (nfold_scal (list nat) (S m * S m)
                      (fun v => length (safelist v (m - k))) (gen132 (m - k))).
        rewrite (nfold_const (list nat) (k * ((m - k) * (m - k))
                                         + 2 * (m - k) * Awp a k + Hsq a k)
                   (gen132 (m - k))).
        rewrite (nfold_const (list nat) (S m * S m) (gen132 (m - k))).
        unfold Hsqtot, card132.
        assert (Eq : fold_right (fun v acc =>
            (length (safelist v (m - k)) * (S m * S m) + acc)%nat) 0%nat
            (gen132 (m - k))
          = fold_right (fun v acc =>
              (S m * S m * length (safelist v (m - k)) + acc)%nat) 0%nat
              (gen132 (m - k)))
          by (apply nfold_ext_in; intros v _; ring).
        rewrite Eq. nia.
      + unfold sctot, safelist. reflexivity. }
  transitivity (fold_right (fun a acc =>
      ((Hsqtot (m - k) + S m * S m * sctot (m - k)
        + card132 (m - k) * (k * ((m - k) * (m - k)))
        + card132 (m - k) * (S m * S m))
       + card132 (m - k) * (2 * (m - k)) * Awp a k
       + card132 (m - k) * Hsq a k + acc)%nat) 0%nat (gen132 k)).
  - assert (Ecorr2 : (card132 k * ((m - k) * (m - k) * sctot (m - k)))%nat
      = fold_right (fun (_ : list nat) (acc : nat) =>
          ((m - k) * (m - k) * sctot (m - k) + acc)%nat) 0%nat (gen132 k)).
    { rewrite (nfold_const (list nat)
                 ((m - k) * (m - k) * sctot (m - k)) (gen132 k)).
      unfold card132. ring. }
    rewrite Ecorr2.
    rewrite <- (fold_add_split (list nat)
      (fun a : list nat => fold_right (fun v acc =>
         (Hsq (midmax a v) (S m) + acc)%nat) 0%nat (gen132 (m - k)))
      (fun _ : list nat => ((m - k) * (m - k) * sctot (m - k))%nat)
      (gen132 k)).
    apply nfold_ext_in. intros a Ha.
    assert (K := INNER a Ha). nia.
  - rewrite (nfold_three (list nat)
               (fun _ : list nat =>
                  (Hsqtot (m - k) + S m * S m * sctot (m - k)
                   + card132 (m - k) * (k * ((m - k) * (m - k)))
                   + card132 (m - k) * (S m * S m))%nat)
               (fun a => (card132 (m - k) * (2 * (m - k)) * Awp a k)%nat)
               (fun a => (card132 (m - k) * Hsq a k)%nat) (gen132 k)).
    cbn beta.
    rewrite (nfold_const (list nat)
               (Hsqtot (m - k) + S m * S m * sctot (m - k)
                + card132 (m - k) * (k * ((m - k) * (m - k)))
                + card132 (m - k) * (S m * S m)) (gen132 k)).
    rewrite (nfold_scal (list nat) (card132 (m - k) * (2 * (m - k)))
               (fun a => Awp a k) (gen132 k)).
    rewrite (nfold_scal (list nat) (card132 (m - k))
               (fun a => Hsq a k) (gen132 k)).
    unfold Awptot, Hsqtot, card132. nia.
Qed.

(* ------------------------------------------------------------------ *)
(* Cubic weights against the Catalan convolution. *)

Lemma wsum_split4 : forall a b c d n,
  wsum (fun k => (a * (k * k * k) + b * (k * k) + c * k + d)%nat) n
  = (a * wsum (fun k => (k * k * k)%nat) n + b * wsum (fun k => (k * k)%nat) n
     + c * wsum (fun k => k) n + d * wsum (fun _ => 1%nat) n)%nat.
Proof.
  intros a b c d n.
  rewrite <- (wsum_scal a (fun k => (k * k * k)%nat) n).
  rewrite <- (wsum_scal b (fun k => (k * k)%nat) n).
  rewrite <- (wsum_scal c (fun k => k) n).
  rewrite <- (wsum_scal d (fun _ => 1%nat) n).
  rewrite (wsum_add (fun k => (a * (k * k * k))%nat)
             (fun k => (b * (k * k))%nat) n).
  rewrite (wsum_add (fun k => (a * (k * k * k) + b * (k * k))%nat)
             (fun k => (c * k)%nat) n).
  rewrite (wsum_add (fun k => (a * (k * k * k) + b * (k * k) + c * k)%nat)
             (fun k => (d * 1)%nat) n).
  apply wsum_ext. intros k _. lia.
Qed.

Lemma wsum_kkmk_val : forall m,
  (2 * wsum (fun k => (k * k * (m - k))%nat) m
   = m * wsum (fun k => (k * (m - k))%nat) m)%nat.
Proof.
  intro m.
  assert (R : wsum (fun k => (k * k * (m - k))%nat) m
            = wsum (fun k => ((m - k) * (m - k) * k)%nat) m).
  { rewrite (wsum_rev (fun k => (k * k * (m - k))%nat) m).
    apply wsum_ext. intros k Hk.
    replace (m - (m - k))%nat with k by lia. reflexivity. }
  assert (A : (wsum (fun k => (k * k * (m - k))%nat) m
               + wsum (fun k => ((m - k) * (m - k) * k)%nat) m)%nat
            = wsum (fun k => (k * k * (m - k) + (m - k) * (m - k) * k)%nat) m)
    by apply wsum_add.
  assert (B : wsum (fun k => (k * k * (m - k) + (m - k) * (m - k) * k)%nat) m
            = wsum (fun k => (m * (k * (m - k)))%nat) m).
  { apply wsum_ext. intros k Hk.
    remember (m - k)%nat as d eqn:Ed.
    assert (EM : m = (k + d)%nat) by lia. rewrite EM. ring. }
  rewrite (wsum_scal m (fun k => (k * (m - k))%nat) m) in B. lia.
Qed.

Lemma wsum_kmk2_val : forall m,
  (2 * wsum (fun k => (k * ((m - k) * (m - k)))%nat) m
   = m * wsum (fun k => (k * (m - k))%nat) m)%nat.
Proof.
  intro m.
  assert (E : wsum (fun k => (k * ((m - k) * (m - k)))%nat) m
            = wsum (fun k => ((m - k) * (m - k) * k)%nat) m)
    by (apply wsum_ext; intros k _; ring).
  assert (R : wsum (fun k => (k * k * (m - k))%nat) m
            = wsum (fun k => ((m - k) * (m - k) * k)%nat) m).
  { rewrite (wsum_rev (fun k => (k * k * (m - k))%nat) m).
    apply wsum_ext. intros k Hk.
    replace (m - (m - k))%nat with k by lia. reflexivity. }
  assert (K := wsum_kkmk_val m). lia.
Qed.

Lemma wsum_cube_val : forall m,
  (2 * wsum (fun k => (k * k * k)%nat) m
   + 3 * m * wsum (fun k => (k * (m - k))%nat) m
   = m * m * m * card132 (S m))%nat.
Proof.
  intro m.
  assert (R := wsum_rev (fun k => (k * k * k)%nat) m).
  assert (A : (wsum (fun k => (k * k * k)%nat) m
               + wsum (fun k => ((m - k) * (m - k) * (m - k))%nat) m)%nat
            = wsum (fun k => (k * k * k
                              + (m - k) * (m - k) * (m - k))%nat) m)
    by apply wsum_add.
  assert (B : (wsum (fun k => (k * k * k
                               + (m - k) * (m - k) * (m - k))%nat) m
               + wsum (fun k => (3 * m * (k * (m - k)))%nat) m)%nat
            = wsum (fun k => (k * k * k + (m - k) * (m - k) * (m - k)
                              + 3 * m * (k * (m - k)))%nat) m)
    by apply wsum_add.
  assert (Cc : wsum (fun k => (k * k * k + (m - k) * (m - k) * (m - k)
                               + 3 * m * (k * (m - k)))%nat) m
             = wsum (fun _ => (m * m * m)%nat) m).
  { apply wsum_ext. intros k Hk.
    remember (m - k)%nat as d eqn:Ed.
    assert (EM : m = (k + d)%nat) by lia. rewrite EM. ring. }
  rewrite (wsum_const (m * m * m) m) in Cc.
  rewrite (wsum_scal (3 * m) (fun k => (k * (m - k))%nat) m) in B.
  lia.
Qed.

Lemma wsum_3k1mk : forall m,
  wsum (fun k => ((3 * k + 1) * (m - k))%nat) m
  = (3 * wsum (fun k => (k * (m - k))%nat) m + wsum (fun k => k) m)%nat.
Proof.
  intro m.
  assert (R : wsum (fun k => k) m = wsum (fun k => (m - k)%nat) m)
    by apply wsum_rev.
  rewrite R.
  rewrite <- (wsum_scal 3 (fun k => (k * (m - k))%nat) m).
  rewrite (wsum_add (fun k => (3 * (k * (m - k)))%nat)
             (fun k => (m - k)%nat) m).
  apply wsum_ext. intros k _. ring.
Qed.

Lemma wsum_kk1mk : forall m,
  wsum (fun k => (k * (k + 1) * (m - k))%nat) m
  = (wsum (fun k => (k * k * (m - k))%nat) m
     + wsum (fun k => (k * (m - k))%nat) m)%nat.
Proof.
  intro m.
  rewrite (wsum_add (fun k => (k * k * (m - k))%nat)
             (fun k => (k * (m - k))%nat) m).
  apply wsum_ext. intros k _. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* The blocks the level sum runs into. *)

Lemma conv_sctot_ww : forall f m,
  (conv f (fun n => (n * n * sctot n)%nat) m
   + conv f (fun n => (n * n * card132 n)%nat) m
   = conv f (fun n => (n * n * card132 (S n))%nat) m)%nat.
Proof.
  intros f m.
  rewrite <- (conv_add_r f (fun n => (n * n * sctot n)%nat)
                (fun n => (n * n * card132 n)%nat) m).
  apply conv_ext; [intros k _; reflexivity|].
  intros n _. rewrite (sctot_card n). ring.
Qed.

Lemma conv_shift_sq : forall m,
  (conv card132 (fun n => (n * n * card132 (S n))%nat) m
   + 2 * m * conv (fun k => (k * card132 k)%nat) (fun n => card132 (S n)) m
   = m * m * conv card132 (fun n => card132 (S n)) m
     + conv (fun k => (k * k * card132 k)%nat) (fun n => card132 (S n)) m)%nat.
Proof.
  intro m. unfold conv.
  rewrite <- (nfold_scal nat (2 * m)
    (fun k => (k * card132 k * card132 (S (m - k)))%nat) (seq 0 (S m))).
  rewrite <- (nfold_scal nat (m * m)
    (fun k => (card132 k * card132 (S (m - k)))%nat) (seq 0 (S m))).
  rewrite <- (fold_add_split nat
    (fun k => (card132 k * ((m - k) * (m - k) * card132 (S (m - k))))%nat)
    (fun k => (2 * m * (k * card132 k * card132 (S (m - k))))%nat)
    (seq 0 (S m))).
  rewrite <- (fold_add_split nat
    (fun k => (m * m * (card132 k * card132 (S (m - k))))%nat)
    (fun k => (k * k * card132 k * card132 (S (m - k)))%nat) (seq 0 (S m))).
  apply nfold_ext_in. intros k Hk. apply in_seq in Hk.
  remember (m - k)%nat as d eqn:Ed.
  assert (EM : m = (k + d)%nat) by lia. rewrite EM. ring.
Qed.

Lemma conv_V0 : forall m,
  (conv card132 (fun n => card132 (S n)) m + card132 (S m)
   = card132 (S (S m)))%nat.
Proof.
  intro m.
  assert (H1 := conv_shift1 (fun _ => 1%nat) m). cbn beta in H1.
  rewrite (wsum_const 1 (S m)) in H1.
  assert (Hb : conv (fun k => (1 * card132 k)%nat) (fun n => card132 (S n)) m
             = conv card132 (fun n => card132 (S n)) m)
    by (apply conv_ext; [intros k _; lia | intros n _; reflexivity]).
  rewrite Hb in H1. lia.
Qed.

Definition HSQCL (n : nat) : Prop :=
  (6 * Hsqtot n + 3 * 4 ^ n + 3 * n * n * card132 n
   = (2 * n * n * n + 4 * n + 3) * card132 n + 3 * n * 4 ^ n)%nat.

Lemma conv_HA : forall m,
  (forall j, (j <= m)%nat -> HSQCL j) ->
  (6 * conv card132 Hsqtot m + 3 * Aconv m + 3 * wsum (fun k => (k * k)%nat) m
   = wsum (fun k => (2 * k * k * k + 4 * k + 3)%nat) m + 3 * Bconv m)%nat.
Proof.
  intros m IH.
  assert (E : (conv card132 (fun n => (6 * Hsqtot n)%nat) m
               + conv card132 (fun n => (3 * 4 ^ n
                                         + 3 * (n * n * card132 n))%nat) m
               = conv card132 (fun n => ((2 * n * n * n + 4 * n + 3)
                                         * card132 n + 3 * (n * 4 ^ n))%nat) m)%nat).
  { rewrite <- (conv_add_r card132 (fun n => (6 * Hsqtot n)%nat)
                  (fun n => (3 * 4 ^ n + 3 * (n * n * card132 n))%nat) m).
    apply conv_ext; [intros k _; reflexivity|].
    intros n Hn. assert (K := IH n Hn). unfold HSQCL in K. nia. }
  rewrite (conv_scal_r 6 card132 Hsqtot m) in E.
  rewrite (conv_add_r card132 (fun n => (3 * 4 ^ n)%nat)
             (fun n => (3 * (n * n * card132 n))%nat) m) in E.
  rewrite (conv_scal_r 3 card132 (fun n => 4 ^ n) m) in E.
  rewrite (conv_scal_r 3 card132 (fun n => (n * n * card132 n)%nat) m) in E.
  rewrite (conv_rev card132 (fun n => 4 ^ n) m), (conv_aconv m) in E.
  rewrite (conv_catw (fun n => (n * n)%nat) m) in E.
  rewrite (conv_add_r card132
             (fun n => ((2 * n * n * n + 4 * n + 3) * card132 n)%nat)
             (fun n => (3 * (n * 4 ^ n))%nat) m) in E.
  rewrite (conv_catw (fun n => (2 * n * n * n + 4 * n + 3)%nat) m) in E.
  rewrite (conv_scal_r 3 card132 (fun n => (n * 4 ^ n)%nat) m) in E.
  rewrite (conv_rev card132 (fun n => (n * 4 ^ n)%nat) m), (conv_bconv m) in E.
  lia.
Qed.

Lemma conv_HF : forall m,
  (forall j, (j <= m)%nat -> HSQCL j) ->
  (6 * conv Hsqtot card132 m + 3 * Aconv m + 3 * wsum (fun k => (k * k)%nat) m
   = wsum (fun k => (2 * k * k * k + 4 * k + 3)%nat) m + 3 * Bconv m)%nat.
Proof.
  intros m IH.
  assert (E : (conv (fun k => (6 * Hsqtot k)%nat) card132 m
               + conv (fun k => (3 * 4 ^ k
                                 + 3 * (k * k * card132 k))%nat) card132 m
               = conv (fun k => ((2 * k * k * k + 4 * k + 3) * card132 k
                                 + 3 * (k * 4 ^ k))%nat) card132 m)%nat).
  { rewrite <- (conv_add_l (fun k => (6 * Hsqtot k)%nat)
                  (fun k => (3 * 4 ^ k + 3 * (k * k * card132 k))%nat)
                  card132 m).
    apply conv_ext; [|intros n _; reflexivity].
    intros n Hn. assert (K := IH n Hn). unfold HSQCL in K. nia. }
  rewrite (conv_scal_l 6 Hsqtot card132 m) in E.
  rewrite (conv_add_l (fun k => (3 * 4 ^ k)%nat)
             (fun k => (3 * (k * k * card132 k))%nat) card132 m) in E.
  rewrite (conv_scal_l 3 (fun k => 4 ^ k) card132 m), (conv_aconv m) in E.
  rewrite (conv_scal_l 3 (fun k => (k * k * card132 k)%nat) card132 m) in E.
  rewrite (conv_wsum (fun k => (k * k)%nat) m) in E.
  rewrite (conv_add_l (fun k => ((2 * k * k * k + 4 * k + 3) * card132 k)%nat)
             (fun k => (3 * (k * 4 ^ k))%nat) card132 m) in E.
  rewrite (conv_wsum (fun k => (2 * k * k * k + 4 * k + 3)%nat) m) in E.
  rewrite (conv_scal_l 3 (fun k => (k * 4 ^ k)%nat) card132 m),
          (conv_bconv m) in E.
  lia.
Qed.

Lemma conv_HD : forall m,
  (2 * conv Awptot (fun n => (n * card132 n)%nat) m
   + wsum (fun k => ((3 * k + 1) * (m - k))%nat) m + Bconv m
   = wsum (fun k => (k * (k + 1) * (m - k))%nat) m + m * Aconv m)%nat.
Proof.
  intro m.
  assert (E : (conv (fun k => (2 * Awptot k)%nat)
                 (fun n => (n * card132 n)%nat) m
               + conv (fun k => ((3 * k + 1) * card132 k)%nat)
                   (fun n => (n * card132 n)%nat) m
               = conv (fun k => (k * (k + 1) * card132 k)%nat)
                   (fun n => (n * card132 n)%nat) m
                 + conv (fun k => 4 ^ k)
                     (fun n => (n * card132 n)%nat) m)%nat).
  { rewrite <- (conv_add_l (fun k => (2 * Awptot k)%nat)
                  (fun k => ((3 * k + 1) * card132 k)%nat)
                  (fun n => (n * card132 n)%nat) m).
    rewrite <- (conv_add_l (fun k => (k * (k + 1) * card132 k)%nat)
                  (fun k => 4 ^ k) (fun n => (n * card132 n)%nat) m).
    apply conv_ext; [|intros n _; reflexivity].
    intros n _. assert (K := Awptot_closed n).
    rewrite <- (card132_binom n) in K. nia. }
  rewrite (conv_scal_l 2 Awptot (fun n => (n * card132 n)%nat) m) in E.
  rewrite (conv_wsum2 (fun k => (3 * k + 1)%nat) (fun n => n) m) in E.
  rewrite (conv_wsum2 (fun k => (k * (k + 1))%nat) (fun n => n) m) in E.
  assert (R := conv_rbconv m). lia.
Qed.

Lemma conv_HE : forall m,
  (conv card132 (fun n => (n * n * sctot n)%nat) m
   + wsum (fun k => (k * k)%nat) m
   + 2 * m * conv (fun k => (k * card132 k)%nat) (fun n => card132 (S n)) m
   = m * m * conv card132 (fun n => card132 (S n)) m
     + conv (fun k => (k * k * card132 k)%nat) (fun n => card132 (S n)) m)%nat.
Proof.
  intro m.
  assert (E := conv_sctot_ww card132 m).
  rewrite (conv_catw (fun n => (n * n)%nat) m) in E.
  assert (K := conv_shift_sq m). lia.
Qed.

Theorem Hsqtot_conv : forall m,
  (Hsqtot (S m) + conv card132 (fun n => (n * n * sctot n)%nat) m
   = conv card132 Hsqtot m
     + S m * S m * conv card132 sctot m
     + conv (fun k => (k * card132 k)%nat) (fun n => (n * n * card132 n)%nat) m
     + 2 * conv Awptot (fun n => (n * card132 n)%nat) m
     + conv Hsqtot card132 m
     + S m * S m * conv card132 card132 m)%nat.
Proof.
  intro m.
  assert (E := Hsqtot_expand m).
  assert (R : (conv card132 Hsqtot m
               + S m * S m * conv card132 sctot m
               + conv (fun k => (k * card132 k)%nat)
                   (fun n => (n * n * card132 n)%nat) m
               + 2 * conv Awptot (fun n => (n * card132 n)%nat) m
               + conv Hsqtot card132 m
               + S m * S m * conv card132 card132 m)%nat
    = fold_right (fun k acc =>
       (card132 k * Hsqtot (m - k)
        + S m * S m * (card132 k * sctot (m - k))
        + k * card132 k * ((m - k) * (m - k) * card132 (m - k))
        + 2 * (Awptot k * ((m - k) * card132 (m - k)))
        + Hsqtot k * card132 (m - k)
        + S m * S m * (card132 k * card132 (m - k))
        + acc)%nat) 0%nat (seq 0 (S m))).
  { rewrite <- (conv_scal_l (S m * S m) card132 sctot m).
    rewrite <- (conv_scal_l 2 Awptot (fun n => (n * card132 n)%nat) m).
    rewrite <- (conv_scal_l (S m * S m) card132 card132 m).
    unfold conv. cbn beta.
    rewrite <- (nfold_six nat
      (fun k => (card132 k * Hsqtot (m - k))%nat)
      (fun k => (S m * S m * card132 k * sctot (m - k))%nat)
      (fun k => (k * card132 k * ((m - k) * (m - k) * card132 (m - k)))%nat)
      (fun k => (2 * Awptot k * ((m - k) * card132 (m - k)))%nat)
      (fun k => (Hsqtot k * card132 (m - k))%nat)
      (fun k => (S m * S m * card132 k * card132 (m - k))%nat)
      (seq 0 (S m))).
    apply nfold_ext_in. intros k _. cbn beta. ring. }
  assert (L : conv card132 (fun n => (n * n * sctot n)%nat) m
    = fold_right (fun k acc =>
        (card132 k * ((m - k) * (m - k) * sctot (m - k)) + acc)%nat) 0%nat
        (seq 0 (S m))) by reflexivity.
  lia.
Qed.

Lemma Hsqtot_step : forall m,
  (forall j, (j <= m)%nat -> HSQCL j) -> HSQCL (S m).
Proof.
  intros m IH. unfold HSQCL.
  assert (HC := Hsqtot_conv m).
  assert (HA := conv_HA m IH).
  assert (HF := conv_HF m IH).
  assert (HB := conv_SC2 m).
  assert (HBm := f_equal (Nat.mul m) HB).
  assert (HBm2 := f_equal (Nat.mul (m * m)) HB).
  assert (HCc := conv_wsum2 (fun k => k) (fun n => (n * n)%nat) m).
  assert (HD := conv_HD m).
  assert (HE := conv_HE m).
  assert (HG := conv_cat m).
  assert (HGm := f_equal (Nat.mul m) HG).
  assert (HGm2 := f_equal (Nat.mul (m * m)) HG).
  assert (V0 := conv_V0 m).
  assert (V0m2 := f_equal (Nat.mul (m * m)) V0).
  assert (V1 := conv_shift1 (fun k => k) m).
  assert (V2 := conv_shift1 (fun k => (k * k)%nat) m).
  cbn beta in V1, V2.
  assert (V1m := f_equal (Nat.mul m) V1).
  rewrite (wsum_3k1mk m), (wsum_kk1mk m) in HD.
  assert (Q1 := wsum_split4 2 0 4 3 m).
  assert (Qe : wsum (fun k => (2 * (k * k * k) + 0 * (k * k) + 4 * k + 3)%nat) m
             = wsum (fun k => (2 * k * k * k + 4 * k + 3)%nat) m)
    by (apply wsum_ext; intros k _; lia).
  assert (W1 := wsum_const 1 m).
  assert (W2 := wsum_const 1 (S m)).
  assert (W3 := wsum_id_val m).
  assert (W4 := wsum_id_val (S m)).
  assert (W4m := f_equal (Nat.mul m) W4).
  assert (W5 := wsum_sq_val m).
  assert (W6 := wsum_sq_val (S m)).
  assert (W7 := wsum_kmk_val m).
  assert (W8 := wsum_cube_val m).
  assert (W9 := wsum_kkmk_val m).
  assert (W10 := wsum_kmk2_val m).
  assert (R2 := card132_ratio (S m)).
  assert (R2m := f_equal (Nat.mul m) R2).
  assert (R2m2 := f_equal (Nat.mul (m * m)) R2).
  assert (P1 := Aconv_closed m).
  assert (P1m := f_equal (Nat.mul m) P1).
  assert (P3 := Bconv_val m).
  assert (P4 := cbi_ratio m).
  assert (B1 := card132_binom (S m)).
  assert (B1m := f_equal (Nat.mul m) B1).
  unfold cb in P3, P4.
  replace (4 ^ S m)%nat with (4 * 4 ^ m)%nat in * by (cbn [Nat.pow]; ring).
  lia.
Qed.

Theorem Hsqtot_closed_upto : forall N m, (m <= N)%nat -> HSQCL m.
Proof.
  induction N as [|N IHN]; intros m Hm.
  - assert (E : m = 0%nat) by lia. subst m. unfold HSQCL.
    vm_compute. reflexivity.
  - destruct (le_lt_dec m N) as [H|H]; [apply IHN; exact H|].
    assert (EM : m = S N) by lia. subst m.
    apply Hsqtot_step. intros j Hj. apply IHN. lia.
Qed.

Theorem Hsqtot_closed : forall m, HSQCL m.
Proof. intro m. apply (Hsqtot_closed_upto m m). lia. Qed.

Theorem Ctot_closed : CTOT_CLOSED.
Proof.
  intro M.
  assert (H1 := Ctot_Hsq M).
  assert (H2 := Hsqtot_closed M). unfold HSQCL in H2.
  assert (H3 := tri2_val M).
  assert (H3c := f_equal (Nat.mul (card132 M)) H3).
  assert (H4 := Awptot_closed M).
  assert (H4m := f_equal (Nat.mul M) H4).
  assert (H5 := card132_binom M).
  assert (H5m := f_equal (Nat.mul M) H5).
  assert (H5m2 := f_equal (Nat.mul (M * M)) H5).
  lia.
Qed.

Definition diagonal_three_closed : Diagonal 3 :=
  diagonal_three_of_stats Btot_closed Ctot_closed.


(* ------------------------------------------------------------------ *)
(* Polynomial weights against the central binomial convolutions. *)


(* The two convolutions of the central binomials: against themselves they give
   the powers of four, against the powers of four they give back the central
   binomials.  Both carry polynomial weights, by one shift recurrence each. *)

Lemma bsum_shift : forall w n,
  bsum (fun j => (j * w (j - 1))%nat) (S n)
  = (4 * bsum (fun k => (k * w k)%nat) n + 2 * bsum w n)%nat.
Proof.
  intros w n.
  assert (E : bsum (fun j => (j * w (j - 1))%nat) (S n)
            = bsum (fun k => ((4 * k + 2) * w k)%nat) n).
  { unfold bsum. cbn beta.
    change (seq 0 (S (S n))) with (0%nat :: seq 1 (S n)).
    rewrite (nfold_cons nat
      (fun j => (j * w (j - 1) * (cb j * cb (S n - j)))%nat) 0%nat
      (seq 1 (S n))).
    cbn beta.
    replace (0 * w (0 - 1) * (cb 0 * cb (S n - 0)))%nat with 0%nat by lia.
    rewrite Nat.add_0_l.
    rewrite <- (seq_shift (S n) 0).
    rewrite (nfold_map_gen nat nat
      (fun j => (j * w (j - 1) * (cb j * cb (S n - j)))%nat) S (seq 0 (S n))).
    apply nfold_ext_in. intros k Hk. apply in_seq in Hk. cbn beta.
    replace (S n - S k)%nat with (n - k)%nat by lia.
    replace (S k - 1)%nat with k by lia.
    assert (R := cbi_ratio k).
    transitivity (w k * (S k * cb (S k)) * cb (n - k))%nat; [ring|].
    rewrite R. ring. }
  rewrite E.
  rewrite <- (bsum_scal 4 (fun k => (k * w k)%nat) n).
  rewrite <- (bsum_scal 2 w n).
  rewrite (bsum_add (fun k => (4 * (k * w k))%nat) (fun k => (2 * w k)%nat) n).
  apply bsum_ext. intros k _. ring.
Qed.

Lemma bsum_id_val : forall m, (2 * bsum (fun k => k) m = m * 4 ^ m)%nat.
Proof.
  intro m. assert (H := pconv1_sym m). unfold pconv1 in H.
  rewrite (pconv_pow m) in H. exact H.
Qed.

Lemma bsum_sq_val : forall m,
  (8 * bsum (fun k => (k * k)%nat) m = m * (3 * m + 1) * 4 ^ m)%nat.
Proof.
  induction m as [|n IH]; [reflexivity|].
  assert (S1 := bsum_shift (fun k => k) n). cbn beta in S1.
  assert (E : (bsum (fun j => (j * (j - 1))%nat) (S n)
               + bsum (fun k => k) (S n))%nat
            = bsum (fun k => (k * k)%nat) (S n)).
  { rewrite (bsum_add (fun j => (j * (j - 1))%nat) (fun k => k) (S n)).
    apply bsum_ext. intros k _. destruct k as [|k]; [reflexivity|].
    replace (S k - 1)%nat with k by lia. ring. }
  assert (A := bsum_id_val n).
  assert (B := bsum_id_val (S n)).
  replace (4 ^ S n)%nat with (4 * 4 ^ n)%nat in B by (cbn [Nat.pow]; ring).
  replace (4 ^ S n)%nat with (4 * 4 ^ n)%nat by (cbn [Nat.pow]; ring).
  nia.
Qed.

Lemma bsum_kmk_val : forall m,
  (8 * bsum (fun k => (k * (m - k))%nat) m + m * (3 * m + 1) * 4 ^ m
   = 4 * m * (m * 4 ^ m))%nat.
Proof.
  intro m.
  assert (E : (bsum (fun k => (k * (m - k))%nat) m
               + bsum (fun k => (k * k)%nat) m)%nat
            = bsum (fun k => (m * k)%nat) m).
  { rewrite (bsum_add (fun k => (k * (m - k))%nat) (fun k => (k * k)%nat) m).
    apply bsum_ext. intros k Hk.
    remember (m - k)%nat as d eqn:Ed.
    assert (EM : m = (k + d)%nat) by lia. rewrite EM. ring. }
  rewrite (bsum_scal m (fun k => k) m) in E.
  assert (A := bsum_id_val m).
  assert (B := bsum_sq_val m).
  nia.
Qed.

(* ------------------------------------------------------------------ *)

Definition esum (w : nat -> nat) (m : nat) : nat :=
  fold_right (fun k acc => (w k * (cb k * 4 ^ (m - k)) + acc)%nat) 0%nat
             (seq 0 (S m)).

Lemma esum_rec : forall w n,
  esum w (S n) = (4 * esum w n + w (S n) * cb (S n))%nat.
Proof.
  intros w n. unfold esum at 1. rewrite (seq_snoc (S n) 0).
  rewrite (nfold_app nat (fun k => (w k * (cb k * 4 ^ (S n - k)))%nat)).
  rewrite (nfold_single nat (fun k => (w k * (cb k * 4 ^ (S n - k)))%nat)
             (0 + S n)).
  cbn beta.
  replace (0 + S n)%nat with (S n) by lia.
  rewrite Nat.sub_diag. change (4 ^ 0)%nat with 1%nat.
  unfold esum.
  rewrite <- (nfold_scal nat 4 (fun k => (w k * (cb k * 4 ^ (n - k)))%nat)
                (seq 0 (S n))).
  f_equal; [|ring].
  apply nfold_ext_in. intros k Hk. apply in_seq in Hk.
  replace (S n - k)%nat with (S (n - k)) by lia.
  cbn [Nat.pow]. ring.
Qed.

Lemma esum_ext : forall w1 w2 m,
  (forall k, (k <= m)%nat -> w1 k = w2 k) -> esum w1 m = esum w2 m.
Proof.
  intros w1 w2 m H. unfold esum. apply nfold_ext_in.
  intros k Hk. apply in_seq in Hk. rewrite (H k ltac:(lia)). reflexivity.
Qed.

Lemma esum_one : forall m,
  esum (fun _ => 1%nat) m = ((2 * m + 1) * cb m)%nat.
Proof.
  induction m as [|n IH]; [reflexivity|].
  rewrite (esum_rec (fun _ => 1%nat) n), IH.
  assert (R := cbi_ratio n). nia.
Qed.

Lemma esum_id_val : forall m,
  (3 * esum (fun k => k) m = m * (2 * m + 1) * cb m)%nat.
Proof.
  induction m as [|n IH]; [reflexivity|].
  rewrite (esum_rec (fun k => k) n).
  assert (R := cbi_ratio n). nia.
Qed.

(* the classical form: sum of 4^(m-k) C(2k,k) is (2m+1) C(2m,m) *)
Corollary central_pow_conv : forall m,
  fold_right (fun k acc => (4 ^ (m - k) * binomN (2 * k) k + acc)%nat) 0%nat
             (seq 0 (S m))
  = ((2 * m + 1) * binomN (2 * m) m)%nat.
Proof.
  intro m.
  assert (E := esum_one m). unfold esum, cb in E. cbn beta in E.
  rewrite <- E. apply nfold_ext_in. intros k _. cbn beta. ring.
Qed.

(* Cubic weights on both convolutions. *)


(* Cubic weights on both convolutions. *)

Lemma bsum_cube_val : forall m,
  (16 * bsum (fun k => (k * k * k)%nat) m
   = m * m * (5 * m + 3) * 4 ^ m)%nat.
Proof.
  induction m as [|n IH]; [reflexivity|].
  assert (S1 := bsum_shift (fun k => (k * k)%nat) n). cbn beta in S1.
  assert (E1 : bsum (fun k => (k * (k * k))%nat) n
             = bsum (fun k => (k * k * k)%nat) n)
    by (apply bsum_ext; intros k _; ring).
  rewrite E1 in S1.
  assert (E2 : (bsum (fun j => (j * ((j - 1) * (j - 1)))%nat) (S n)
                + 2 * bsum (fun k => (k * k)%nat) (S n))%nat
             = (bsum (fun k => (k * k * k)%nat) (S n)
                + bsum (fun k => k) (S n))%nat).
  { rewrite <- (bsum_scal 2 (fun k => (k * k)%nat) (S n)).
    rewrite (bsum_add (fun j => (j * ((j - 1) * (j - 1)))%nat)
               (fun k => (2 * (k * k))%nat) (S n)).
    rewrite (bsum_add (fun k => (k * k * k)%nat) (fun k => k) (S n)).
    apply bsum_ext. intros j _.
    destruct j as [|j]; [reflexivity|].
    replace (S j - 1)%nat with j by lia. ring. }
  assert (A := bsum_id_val (S n)).
  assert (B := bsum_sq_val n).
  assert (C := bsum_sq_val (S n)).
  replace (4 ^ S n)%nat with (4 * 4 ^ n)%nat in A, C by (cbn [Nat.pow]; ring).
  replace (4 ^ S n)%nat with (4 * 4 ^ n)%nat by (cbn [Nat.pow]; ring).
  nia.
Qed.

Lemma bsum_kkmk_val : forall m,
  (16 * bsum (fun k => (k * k * (m - k))%nat) m + m * m * (5 * m + 3) * 4 ^ m
   = 2 * m * m * (3 * m + 1) * 4 ^ m)%nat.
Proof.
  intro m.
  assert (E : (bsum (fun k => (k * k * (m - k))%nat) m
               + bsum (fun k => (k * k * k)%nat) m)%nat
            = bsum (fun k => (m * (k * k))%nat) m).
  { rewrite (bsum_add (fun k => (k * k * (m - k))%nat)
               (fun k => (k * k * k)%nat) m).
    apply bsum_ext. intros k Hk.
    remember (m - k)%nat as d eqn:Ed.
    assert (EM : m = (k + d)%nat) by lia. rewrite EM. ring. }
  rewrite (bsum_scal m (fun k => (k * k)%nat) m) in E.
  assert (A := bsum_sq_val m).
  assert (B := bsum_cube_val m).
  nia.
Qed.

Lemma bsum_kmkmk_val : forall m,
  (2 * bsum (fun k => (k * ((m - k) * (m - k)))%nat) m
   = 2 * bsum (fun k => (k * k * (m - k))%nat) m)%nat.
Proof.
  intro m.
  assert (R : bsum (fun k => (k * k * (m - k))%nat) m
            = bsum (fun k => ((m - k) * (m - k) * k)%nat) m).
  { rewrite (bsum_rev (fun k => (k * k * (m - k))%nat) m).
    apply bsum_ext. intros k Hk.
    replace (m - (m - k))%nat with k by lia. reflexivity. }
  assert (E : bsum (fun k => (k * ((m - k) * (m - k)))%nat) m
            = bsum (fun k => ((m - k) * (m - k) * k)%nat) m)
    by (apply bsum_ext; intros k _; ring).
  lia.
Qed.

Lemma esum_sq_val : forall m,
  (15 * esum (fun k => (k * k)%nat) m
   = m * (6 * m * m + 7 * m + 2) * cb m)%nat.
Proof.
  induction m as [|n IH]; [reflexivity|].
  rewrite (esum_rec (fun k => (k * k)%nat) n). cbn beta.
  assert (R := cbi_ratio n). nia.
Qed.

(* ------------------------------------------------------------------ *)
(* The two- and three-letter extension counts at a general state. *)


(* The two-letter extension count at a general state.  The cap enters every
   term through a minimum, and laminarity collapses the nested minima exactly
   as in the 132-free case. *)

Theorem extend_two_at_state : forall v n z,
  is_perm v n -> ~ contains_1324 v -> z <= Mu v n ->
  length (extend (ext v z) (S n) 2)
  = (3 + Nat.min (Mu v n) (Hu v n z)
     + fold_right (fun t acc => (2 + Nat.min z (Hu v n t) + acc)%nat) 0%nat
                  (seq 1 z)
     + fold_right (fun s acc => (3 + Nat.min (Mu v n) (Hu v n s) + acc)%nat)
                  0%nat
                  (seq z (S (Nat.min (Mu v n) (Hu v n z) - z))))%nat.
Proof.
  intros v n z Hp Hav Hzm.
  assert (HM := Mu_le_cap v n).
  assert (Hzn : z <= n) by lia.
  assert (Hlv : length v = n) by (apply (perm_len v n); exact Hp).
  assert (Hgz : z <= Hu v n z) by (apply Hu_ge; exact Hzn).
  assert (Hcz := Hu_le_cap v n z).
  assert (Hzh : z <= Nat.min (Mu v n) (Hu v n z)) by lia.
  assert (Hhn : Nat.min (Mu v n) (Hu v n z) <= n) by lia.
  assert (Hpe : is_perm (ext v z) (S n)) by (apply ext_perm; assumption).
  assert (Hae : ~ contains_1324 (ext v z))
    by (apply (ext_avoids v n z Hav Hzm Hzn)).
  rewrite (extend_two_state (ext v z) (S n) Hpe Hae).
  rewrite (Mu_ext v z n Hp Hzn).
  assert (Eb : bump z (Nat.min (Mu v n) (Hu v n z))
             = S (Nat.min (Mu v n) (Hu v n z)))
    by (unfold bump; destruct (Nat.leb_spec z (Nat.min (Mu v n) (Hu v n z)));
        lia).
  rewrite Eb.
  rewrite (seq_split_d3 z (Nat.min (Mu v n) (Hu v n z)) Hzh).
  rewrite !(nfold_app nat (fun t =>
    S (S (Nat.min (S (Nat.min (Mu v n) (Hu v n z)))
                  (Hu (ext v z) (S n) t))))).
  assert (P1 : fold_right (fun t acc =>
      (S (S (Nat.min (S (Nat.min (Mu v n) (Hu v n z)))
                     (Hu (ext v z) (S n) t))) + acc)%nat) 0%nat (seq 0 1)
    = (3 + Nat.min (Mu v n) (Hu v n z))%nat).
  { cbn [seq fold_right].
    rewrite (Hu_ext_zero_M v n z Hlv).
    rewrite (Nat.min_l (S (Nat.min (Mu v n) (Hu v n z))) (S n) ltac:(lia)).
    lia. }
  assert (P2 : fold_right (fun t acc =>
      (S (S (Nat.min (S (Nat.min (Mu v n) (Hu v n z)))
                     (Hu (ext v z) (S n) t))) + acc)%nat) 0%nat (seq 1 z)
    = fold_right (fun t acc => (2 + Nat.min z (Hu v n t) + acc)%nat) 0%nat
                 (seq 1 z)).
  { apply nfold_ext_in. intros t Ht. apply in_seq in Ht.
    assert (Ht1 : 1 <= t) by lia.
    assert (Htz : t <= z) by lia.
    rewrite (Hu_ext_lo_M v n z t Hlv Hp Hzn Ht1 Htz).
    assert (K : Nat.min z (Hu v n t) <= z) by lia.
    rewrite (Nat.min_r (S (Nat.min (Mu v n) (Hu v n z)))
               (Nat.min z (Hu v n t)) ltac:(lia)).
    lia. }
  assert (P3 : fold_right (fun t acc =>
      (S (S (Nat.min (S (Nat.min (Mu v n) (Hu v n z)))
                     (Hu (ext v z) (S n) t))) + acc)%nat) 0%nat
      (seq (S z) (S (Nat.min (Mu v n) (Hu v n z)) - z))
    = fold_right (fun s acc => (3 + Nat.min (Mu v n) (Hu v n s) + acc)%nat)
                 0%nat (seq z (S (Nat.min (Mu v n) (Hu v n z) - z)))).
  { replace (S (Nat.min (Mu v n) (Hu v n z)) - z)%nat
      with (S (Nat.min (Mu v n) (Hu v n z) - z)) by lia.
    rewrite <- (seq_shift (S (Nat.min (Mu v n) (Hu v n z) - z)) z).
    rewrite (nfold_map_gen nat nat
      (fun t => S (S (Nat.min (S (Nat.min (Mu v n) (Hu v n z)))
                              (Hu (ext v z) (S n) t)))) S
      (seq z (S (Nat.min (Mu v n) (Hu v n z) - z)))).
    cbn beta.
    apply nfold_ext_in. intros s Hs. apply in_seq in Hs.
    assert (Hzs : z <= s) by lia.
    assert (Hsh : s <= Nat.min (Mu v n) (Hu v n z)) by lia.
    assert (Hsn : S s <= S n) by lia.
    rewrite (Hu_ext_hi_M v n z (S s) Hlv Hzn ltac:(lia) Hsn).
    replace (S s - 1)%nat with s by lia.
    assert (Hgs : s <= Hu v n s) by (apply Hu_ge; lia).
    assert (Elam : Hu v n s <= Hu v n z)
      by (apply (Hu_laminar v n z s); lia).
    assert (Eb2 : bump z (Hu v n s) = S (Hu v n s))
      by (unfold bump; destruct (Nat.leb_spec z (Hu v n s)); lia).
    rewrite Eb2. lia. }
  rewrite P1, P2, P3. lia.
Qed.

Theorem extend_three_state : forall v n, is_perm v n -> ~ contains_1324 v ->
  length (extend v n 3)
  = fold_right (fun z acc =>
      (3 + Nat.min (Mu v n) (Hu v n z)
       + fold_right (fun t acc' => (2 + Nat.min z (Hu v n t) + acc')%nat)
                    0%nat (seq 1 z)
       + fold_right (fun s acc' =>
           (3 + Nat.min (Mu v n) (Hu v n s) + acc')%nat) 0%nat
           (seq z (S (Nat.min (Mu v n) (Hu v n z) - z)))
       + acc)%nat) 0%nat (seq 0 (S (Mu v n))).
Proof.
  intros v n Hp Hav.
  change 3 with (S 2).
  rewrite (extend_front v n 2), length_flat_map_gen,
          (extend_one_state v n Hav).
  rewrite (nfold_map_gen nat (list nat)
             (fun w => length (extend w (S n) 2)) (ext v) (seq 0 (S (Mu v n)))).
  apply nfold_ext_in. intros z Hz. apply in_seq in Hz.
  apply extend_two_at_state; [exact Hp | exact Hav | lia].
Qed.

(* the 132-free case is the specialisation with no cap *)
Corollary extend_three_free : forall M u, In u (gen132 M) ->
  length (extend u M 3)
  = fold_right (fun z acc =>
      (3 + Hu u M z
       + fold_right (fun t acc' => (2 + Nat.min z (Hu u M t) + acc')%nat)
                    0%nat (seq 1 z)
       + fold_right (fun s acc' => (3 + Hu u M s + acc')%nat) 0%nat
                    (seq z (S (Hu u M z - z)))
       + acc)%nat) 0%nat (seq 0 (S M)).
Proof.
  intros M u Hin.
  assert (Hp : is_perm u M) by (apply gen132_perm; exact Hin).
  assert (H132 : ~ contains_132 u) by (exact (gen132_av M u Hin)).
  assert (Hav : ~ contains_1324 u)
    by (intro C; apply H132; apply sub_1324_132; exact C).
  assert (HMu : Mu u M = M) by (apply Mu_free; exact H132).
  rewrite (extend_three_state u M Hp Hav), HMu.
  apply nfold_ext_in. intros z Hz. apply in_seq in Hz.
  assert (Hc := Hu_le_cap u M z).
  rewrite (Nat.min_r M (Hu u M z) Hc).
  assert (E : fold_right (fun s acc => (3 + Nat.min M (Hu u M s) + acc)%nat)
                0%nat (seq z (S (Hu u M z - z)))
            = fold_right (fun s acc => (3 + Hu u M s + acc)%nat) 0%nat
                (seq z (S (Hu u M z - z)))).
  { apply nfold_ext_in. intros s _.
    assert (Hcs := Hu_le_cap u M s). rewrite (Nat.min_r M (Hu u M s) Hcs).
    reflexivity. }
  rewrite E. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The d = 4 diagonal through the state function. *)


Definition d4form (u : list nat) (M y : nat) : nat :=
  ((8 + 2 * Hu u M y
    + fold_right (fun s acc => (3 + Nat.min y (Hu u M s) + acc)%nat) 0%nat
                 (seq 1 y)
    + fold_right (fun q acc => (4 + Hu u M q + acc)%nat) 0%nat
                 (seq y (S (Hu u M y - y))))
   + fold_right (fun z acc =>
       (3 + Nat.min y (Hu u M z)
        + fold_right (fun t acc' => (2 + Nat.min z (Hu u M t) + acc')%nat)
                     0%nat (seq 1 z)
        + fold_right (fun s acc' => (3 + Nat.min y (Hu u M s) + acc')%nat)
                     0%nat (seq z (S (Nat.min y (Hu u M z) - z)))
        + acc)%nat) 0%nat (seq 1 y)
   + fold_right (fun w acc =>
       (4 + Hu u M w
        + fold_right (fun t acc' => (2 + Nat.min y (Hu u M t) + acc')%nat)
                     0%nat (seq 1 y)
        + fold_right (fun r acc' => (3 + Nat.min w (Hu u M r) + acc')%nat)
                     0%nat (seq y (S (w - y)))
        + fold_right (fun q acc' => (4 + Hu u M q + acc')%nat) 0%nat
                     (seq w (S (Hu u M w - w)))
        + acc)%nat) 0%nat (seq y (S (Hu u M y - y))))%nat.

Definition Gz (u : list nat) (M y z : nat) : nat :=
  (3 + Nat.min (S (Hu u M y)) (Hu (ext u y) (S M) z)
   + fold_right (fun t acc => (2 + Nat.min z (Hu (ext u y) (S M) t) + acc)%nat)
                0%nat (seq 1 z)
   + fold_right (fun s acc =>
       (3 + Nat.min (S (Hu u M y)) (Hu (ext u y) (S M) s) + acc)%nat) 0%nat
       (seq z (S (Nat.min (S (Hu u M y)) (Hu (ext u y) (S M) z) - z))))%nat.

Lemma Hu_ext_hi_S : forall u M y r,
  length u = M -> y <= M -> y <= r -> r <= M ->
  Hu (ext u y) (S M) (S r) = S (Hu u M r).
Proof.
  intros u M y r HL HyM Hyr HrM.
  rewrite (Hu_ext_hi_M u M y (S r) HL HyM ltac:(lia) ltac:(lia)).
  replace (S r - 1)%nat with r by lia.
  assert (Hgr : r <= Hu u M r) by (apply Hu_ge; lia).
  unfold bump. destruct (Nat.leb_spec y (Hu u M r)); lia.
Qed.

Lemma seq_split_lo : forall y w, y <= w ->
  seq 1 (S w) = seq 1 y ++ seq (S y) (S w - y).
Proof.
  intros y w H.
  replace (S w) with (y + (S w - y))%nat at 1 by lia.
  rewrite (seq_break y (S w - y) 1).
  replace (1 + y)%nat with (S y) by lia. reflexivity.
Qed.

(* the sum of H over a block above the insertion point *)
Lemma d4_hiblock : forall M u y a b,
  length u = M -> is_perm u M -> y <= M -> y <= a -> b <= M ->
  b <= Hu u M y -> a <= S b ->
  fold_right (fun s acc =>
    (3 + Nat.min (S (Hu u M y)) (Hu (ext u y) (S M) s) + acc)%nat) 0%nat
    (seq (S a) (S b - a))
  = fold_right (fun q acc => (4 + Hu u M q + acc)%nat) 0%nat (seq a (S b - a)).
Proof.
  intros M u y a b HL Hp HyM Hya HbM Hbh Hab.
  rewrite <- (seq_shift (S b - a) a).
  rewrite (nfold_map_gen nat nat
    (fun s => (3 + Nat.min (S (Hu u M y)) (Hu (ext u y) (S M) s))%nat) S
    (seq a (S b - a))).
  cbn beta.
  apply nfold_ext_in. intros q Hq. apply in_seq in Hq.
  assert (HqM : q <= M) by lia.
  assert (Hyq : y <= q) by lia.
  rewrite (Hu_ext_hi_S u M y q HL HyM Hyq HqM).
  assert (Hlam : Hu u M q <= Hu u M y) by (apply (Hu_laminar u M y q); lia).
  lia.
Qed.

Theorem extend_three_at : forall M u y, In u (gen132 M) -> y <= M ->
  length (extend (ext u y) (S M) 3) = d4form u M y.
Proof.
  intros M u y Hin HyM.
  assert (Hp : is_perm u M) by (apply gen132_perm; exact Hin).
  assert (H132 : ~ contains_132 u) by (exact (gen132_av M u Hin)).
  assert (Hlu : length u = M) by (apply (perm_len u M); exact Hp).
  assert (Hc := Hu_le_cap u M y).
  assert (Hg : y <= Hu u M y) by (apply Hu_ge; exact HyM).
  assert (Hpe : is_perm (ext u y) (S M)) by (apply ext_perm; assumption).
  assert (Hae : ~ contains_1324 (ext u y))
    by (apply ext_all_legal_when_132_free; exact H132).
  rewrite (extend_three_state (ext u y) (S M) Hpe Hae).
  rewrite (Mu_ext_free u M y Hp H132 HyM).
  change (fold_right (fun z acc =>
    (3 + Nat.min (S (Hu u M y)) (Hu (ext u y) (S M) z)
     + fold_right (fun t acc' =>
         (2 + Nat.min z (Hu (ext u y) (S M) t) + acc')%nat) 0%nat (seq 1 z)
     + fold_right (fun s acc' =>
         (3 + Nat.min (S (Hu u M y)) (Hu (ext u y) (S M) s) + acc')%nat) 0%nat
         (seq z (S (Nat.min (S (Hu u M y)) (Hu (ext u y) (S M) z) - z)))
     + acc)%nat) 0%nat (seq 0 (S (S (Hu u M y)))))
  with (fold_right (fun z acc => (Gz u M y z + acc)%nat) 0%nat
          (seq 0 (S (S (Hu u M y))))).
  rewrite (seq_split_d3 y (Hu u M y) Hg).
  rewrite !(nfold_app nat (fun z => Gz u M y z)).
  replace (seq 0 1) with (0%nat :: @nil nat) by reflexivity.
  rewrite (nfold_single nat (fun z => Gz u M y z) 0).
  (* the block at the insertion point *)
  assert (P1 : Gz u M y 0
    = (8 + 2 * Hu u M y
       + fold_right (fun s acc => (3 + Nat.min y (Hu u M s) + acc)%nat) 0%nat
                    (seq 1 y)
       + fold_right (fun q acc => (4 + Hu u M q + acc)%nat) 0%nat
                    (seq y (S (Hu u M y - y))))%nat).
  { unfold Gz.
    rewrite (Hu_ext_zero_M u M y Hlu).
    rewrite (Nat.min_l (S (Hu u M y)) (S M) ltac:(lia)).
    replace (seq 1 0) with (@nil nat) by reflexivity.
    cbn [fold_right].
    replace (S (Hu u M y) - 0)%nat with (S (Hu u M y)) by lia.
    rewrite (seq_split_d3 y (Hu u M y) Hg).
    rewrite !(nfold_app nat (fun s =>
      (3 + Nat.min (S (Hu u M y)) (Hu (ext u y) (S M) s))%nat)).
    replace (seq 0 1) with (0%nat :: @nil nat) by reflexivity.
    rewrite (nfold_single nat (fun s =>
      (3 + Nat.min (S (Hu u M y)) (Hu (ext u y) (S M) s))%nat) 0).
    cbn beta.
    rewrite (Hu_ext_zero_M u M y Hlu).
    rewrite (Nat.min_l (S (Hu u M y)) (S M) ltac:(lia)).
    assert (Q2 : fold_right (fun s acc =>
        (3 + Nat.min (S (Hu u M y)) (Hu (ext u y) (S M) s) + acc)%nat) 0%nat
        (seq 1 y)
      = fold_right (fun s acc => (3 + Nat.min y (Hu u M s) + acc)%nat) 0%nat
                   (seq 1 y)).
    { apply nfold_ext_in. intros s Hs. apply in_seq in Hs.
      rewrite (Hu_ext_lo_M u M y s Hlu Hp HyM ltac:(lia) ltac:(lia)).
      assert (K : Nat.min y (Hu u M s) <= y) by lia. lia. }
    assert (Q3 := d4_hiblock M u y y (Hu u M y) Hlu Hp HyM
                    ltac:(lia) Hc ltac:(lia) ltac:(lia)).
    replace (S (Hu u M y) - y)%nat with (S (Hu u M y - y)) in Q3 by lia.
    replace (S (Hu u M y) - y)%nat with (S (Hu u M y - y)) by lia.
    rewrite Q2, Q3. lia. }
  (* the block below the insertion point *)
  assert (P2 : fold_right (fun z acc => (Gz u M y z + acc)%nat) 0%nat (seq 1 y)
    = fold_right (fun z acc =>
        (3 + Nat.min y (Hu u M z)
         + fold_right (fun t acc' => (2 + Nat.min z (Hu u M t) + acc')%nat)
                      0%nat (seq 1 z)
         + fold_right (fun s acc' => (3 + Nat.min y (Hu u M s) + acc')%nat)
                      0%nat (seq z (S (Nat.min y (Hu u M z) - z)))
         + acc)%nat) 0%nat (seq 1 y)).
  { apply nfold_ext_in. intros z Hz. apply in_seq in Hz.
    assert (Hz1 : 1 <= z) by lia.
    assert (Hzy : z <= y) by lia.
    unfold Gz.
    rewrite (Hu_ext_lo_M u M y z Hlu Hp HyM Hz1 Hzy).
    assert (K : Nat.min y (Hu u M z) <= y) by lia.
    rewrite (Nat.min_r (S (Hu u M y)) (Nat.min y (Hu u M z)) ltac:(lia)).
    assert (T : fold_right (fun t acc =>
        (2 + Nat.min z (Hu (ext u y) (S M) t) + acc)%nat) 0%nat (seq 1 z)
      = fold_right (fun t acc => (2 + Nat.min z (Hu u M t) + acc)%nat) 0%nat
                   (seq 1 z)).
    { apply nfold_ext_in. intros t Ht. apply in_seq in Ht.
      rewrite (Hu_ext_lo_M u M y t Hlu Hp HyM ltac:(lia) ltac:(lia)). lia. }
    assert (S2 : fold_right (fun s acc =>
        (3 + Nat.min (S (Hu u M y)) (Hu (ext u y) (S M) s) + acc)%nat) 0%nat
        (seq z (S (Nat.min y (Hu u M z) - z)))
      = fold_right (fun s acc => (3 + Nat.min y (Hu u M s) + acc)%nat) 0%nat
                   (seq z (S (Nat.min y (Hu u M z) - z)))).
    { apply nfold_ext_in. intros s Hs. apply in_seq in Hs.
      rewrite (Hu_ext_lo_M u M y s Hlu Hp HyM ltac:(lia) ltac:(lia)).
      assert (K2 : Nat.min y (Hu u M s) <= y) by lia. lia. }
    rewrite T, S2. reflexivity. }
  (* the block above the insertion point *)
  assert (P3 : fold_right (fun z acc => (Gz u M y z + acc)%nat) 0%nat
      (seq (S y) (S (Hu u M y) - y))
    = fold_right (fun w acc =>
        (4 + Hu u M w
         + fold_right (fun t acc' => (2 + Nat.min y (Hu u M t) + acc')%nat)
                      0%nat (seq 1 y)
         + fold_right (fun r acc' => (3 + Nat.min w (Hu u M r) + acc')%nat)
                      0%nat (seq y (S (w - y)))
         + fold_right (fun q acc' => (4 + Hu u M q + acc')%nat) 0%nat
                      (seq w (S (Hu u M w - w)))
         + acc)%nat) 0%nat (seq y (S (Hu u M y - y)))).
  { replace (S (Hu u M y) - y)%nat with (S (Hu u M y - y)) by lia.
    rewrite <- (seq_shift (S (Hu u M y - y)) y).
    rewrite (nfold_map_gen nat nat (fun z => Gz u M y z) S
               (seq y (S (Hu u M y - y)))).
    cbn beta.
    apply nfold_ext_in. intros w Hw. apply in_seq in Hw.
    assert (Hyw : y <= w) by lia.
    assert (HwH : w <= Hu u M y) by lia.
    assert (HwM : w <= M) by lia.
    unfold Gz.
    rewrite (Hu_ext_hi_S u M y w Hlu HyM Hyw HwM).
    assert (Hlamw : Hu u M w <= Hu u M y) by (apply (Hu_laminar u M y w); lia).
    rewrite (Nat.min_r (S (Hu u M y)) (S (Hu u M w)) ltac:(lia)).
    assert (T : fold_right (fun t acc =>
        (2 + Nat.min (S w) (Hu (ext u y) (S M) t) + acc)%nat) 0%nat
        (seq 1 (S w))
      = (fold_right (fun t acc => (2 + Nat.min y (Hu u M t) + acc)%nat) 0%nat
                    (seq 1 y)
         + fold_right (fun r acc => (3 + Nat.min w (Hu u M r) + acc)%nat) 0%nat
                      (seq y (S (w - y))))%nat).
    { rewrite (seq_split_lo y w Hyw).
      rewrite (nfold_app nat (fun t =>
        (2 + Nat.min (S w) (Hu (ext u y) (S M) t))%nat)).
      f_equal.
      - apply nfold_ext_in. intros t Ht. apply in_seq in Ht.
        rewrite (Hu_ext_lo_M u M y t Hlu Hp HyM ltac:(lia) ltac:(lia)).
        assert (K : Nat.min y (Hu u M t) <= y) by lia. lia.
      - replace (S w - y)%nat with (S (w - y)) by lia.
        rewrite <- (seq_shift (S (w - y)) y).
        rewrite (nfold_map_gen nat nat
          (fun t => (2 + Nat.min (S w) (Hu (ext u y) (S M) t))%nat) S
          (seq y (S (w - y)))).
        cbn beta.
        apply nfold_ext_in. intros r Hr. apply in_seq in Hr.
        rewrite (Hu_ext_hi_S u M y r Hlu HyM ltac:(lia) ltac:(lia)). lia. }
    rewrite T.
    assert (Hgw : w <= Hu u M w) by (apply Hu_ge; lia).
    assert (Q := d4_hiblock M u y w (Hu u M w) Hlu Hp HyM Hyw
                   (Hu_le_cap u M w) Hlamw ltac:(lia)).
    replace (S (Hu u M w) - w)%nat with (S (Hu u M w - w)) in Q by lia.
    replace (S (S (Hu u M w) - S w)) with (S (Hu u M w - w)) by lia.
    rewrite Q. lia. }
  rewrite P1, P2, P3. unfold d4form. lia.
Qed.

Theorem Ddiag_four_H : forall M,
  Ddiag 4 M
  = fold_right (fun u acc =>
      (fold_right (fun y acc' => (d4form u M y + acc')%nat) 0%nat
                  (seq 0 (S M)) + acc)%nat) 0%nat (gen132 M).
Proof.
  intro M. change 4 with (S 3). rewrite (Ddiag_front 3 M).
  apply nfold_ext_in. intros u Hin.
  apply nfold_ext_in. intros y Hy. apply in_seq in Hy.
  apply extend_three_at; [exact Hin | lia].
Qed.


(* The d = 4 two-term law, in the cleared form the state sum has to reach.
   Fitted and checked against the enumerator at every size it reaches:
   p_4 of degree 3 with leading coefficient 1/4! and q_4 of degree 2 with
   leading coefficient C(4,2)/4!. *)
Definition DDIAG_FOUR_CLOSED : Prop :=
  forall M, (24 * Ddiag 4 M
             = (M * M * M + 35 * M * M + 216 * M + 288) * binomN (2 * M) M
               + (6 * M * M + 78 * M + 264) * 4 ^ M)%nat.

Definition diagonal_four (H : DDIAG_FOUR_CLOSED) : Diagonal 4.
Proof.
  refine (mkDiagonal 4
            (Qmake 288 24 :: Qmake 216 24 :: Qmake 35 24 :: Qmake 1 24 :: nil)
            (Qmake 264 24 :: Qmake 78 24 :: Qmake 6 24 :: nil)
            eq_refl eq_refl _).
  intro M.
  assert (K := H M).
  assert (E : Qn (24 * Ddiag 4 M)%nat == Qmult 24 (Qn (Ddiag 4 M))).
  { rewrite Qn_mul.
    assert (E24 : Qn 24 == 24) by (unfold Qn, Qeq; simpl; lia).
    rewrite E24. reflexivity. }
  assert (E6 : Qn 6 == 6) by (unfold Qn, Qeq; simpl; lia).
  assert (E35 : Qn 35 == 35) by (unfold Qn, Qeq; simpl; lia).
  assert (E78 : Qn 78 == 78) by (unfold Qn, Qeq; simpl; lia).
  assert (E216 : Qn 216 == 216) by (unfold Qn, Qeq; simpl; lia).
  assert (E264 : Qn 264 == 264) by (unfold Qn, Qeq; simpl; lia).
  assert (E288 : Qn 288 == 288) by (unfold Qn, Qeq; simpl; lia).
  cbn [polyQ dp dq].
  setoid_replace (Qn (Ddiag 4 M))
    with (Qdiv (Qmult 24 (Qn (Ddiag 4 M))) 24) by field.
  rewrite <- E, K.
  rewrite ?Qn_add, ?Qn_mul, ?Qn_add, ?Qn_mul, ?Qn_add, ?Qn_mul.
  rewrite E6, E35, E78, E216, E264, E288.
  field.
Defined.

(* The d = 4 state sum, reduced to two further tree statistics. *)


(* The two statistics the d = 4 state sum adds: the clipped H over a node's
   subtree, and the clipped H over the nodes between two given ones. *)

Definition Din (u : list nat) (M y z : nat) : nat :=
  fold_right (fun s acc => (Nat.min y (Hu u M s) + acc)%nat) 0%nat
             (seq z (S (Nat.min y (Hu u M z) - z))).

Definition Ein (u : list nat) (M w y : nat) : nat :=
  fold_right (fun r acc => (Nat.min w (Hu u M r) + acc)%nat) 0%nat
             (seq y (S (w - y))).

Definition d4stat (u : list nat) (M y : nat) : nat :=
  (12 + 2 * Hu u M y + 3 * y + 4 * (Hu u M y - y) + Cin u M y + Bin u M y
   + fold_right (fun z acc =>
       (6 + 4 * Nat.min y (Hu u M z) + Cin u M z + Din u M y z + acc)%nat)
       0%nat (seq 1 y)
   + fold_right (fun w acc =>
       (11 + Hu u M w + 2 * y + Cin u M y + 3 * (w - y) + Ein u M w y
        + 4 * (Hu u M w - w) + Bin u M w + acc)%nat) 0%nat
       (seq y (S (Hu u M y - y))))%nat.

Lemma nfold_const_add : forall (c : nat) (g : nat -> nat) (l : list nat),
  fold_right (fun x acc => (c + g x + acc)%nat) 0%nat l
  = (c * length l + fold_right (fun x acc => (g x + acc)%nat) 0%nat l)%nat.
Proof.
  intros c g l.
  rewrite (fold_add_split nat (fun _ : nat => c) g l).
  cbn beta. rewrite (nfold_const nat c l). reflexivity.
Qed.

Lemma tri_tail : forall y,
  fold_right (fun z acc => (z + acc)%nat) 0%nat (seq 1 y) = tri y.
Proof. intro y. unfold tri. reflexivity. Qed.

Theorem d4form_stats : forall M u y, In u (gen132 M) -> y <= M ->
  (d4form u M y + tri y = d4stat u M y)%nat.
Proof.
  intros M u y Hin HyM.
  assert (Hp : is_perm u M) by (apply gen132_perm; exact Hin).
  assert (Hg : y <= Hu u M y) by (apply Hu_ge; exact HyM).
  unfold d4form, d4stat.
  assert (EA1 : fold_right (fun s acc => (3 + Nat.min y (Hu u M s) + acc)%nat)
                  0%nat (seq 1 y)
              = (3 * y + Cin u M y)%nat).
  { rewrite (nfold_const_add 3 (fun s => Nat.min y (Hu u M s)) (seq 1 y)).
    rewrite length_seq. cbn beta. unfold Cin. reflexivity. }
  assert (EA2 : fold_right (fun q acc => (4 + Hu u M q + acc)%nat) 0%nat
                  (seq y (S (Hu u M y - y)))
              = (4 * S (Hu u M y - y) + Bin u M y)%nat).
  { rewrite (nfold_const_add 4 (fun q => Hu u M q)
               (seq y (S (Hu u M y - y)))).
    rewrite length_seq. cbn beta. unfold Bin. reflexivity. }
  assert (EB : (fold_right (fun z acc =>
      (3 + Nat.min y (Hu u M z)
       + fold_right (fun t acc' => (2 + Nat.min z (Hu u M t) + acc')%nat)
                    0%nat (seq 1 z)
       + fold_right (fun s acc' => (3 + Nat.min y (Hu u M s) + acc')%nat)
                    0%nat (seq z (S (Nat.min y (Hu u M z) - z)))
       + acc)%nat) 0%nat (seq 1 y) + tri y)%nat
    = fold_right (fun z acc =>
        (6 + 4 * Nat.min y (Hu u M z) + Cin u M z + Din u M y z + acc)%nat)
        0%nat (seq 1 y)).
  { rewrite <- (tri_tail y).
    rewrite <- (fold_add_split nat (fun z =>
        (3 + Nat.min y (Hu u M z)
         + fold_right (fun t acc' => (2 + Nat.min z (Hu u M t) + acc')%nat)
                      0%nat (seq 1 z)
         + fold_right (fun s acc' => (3 + Nat.min y (Hu u M s) + acc')%nat)
                      0%nat (seq z (S (Nat.min y (Hu u M z) - z))))%nat)
        (fun z => z) (seq 1 y)).
    apply nfold_ext_in. intros z Hz. apply in_seq in Hz.
    rewrite (nfold_const_add 2 (fun t => Nat.min z (Hu u M t)) (seq 1 z)),
            length_seq.
    rewrite (nfold_const_add 3 (fun s => Nat.min y (Hu u M s))
               (seq z (S (Nat.min y (Hu u M z) - z)))), length_seq.
    assert (Hgz : z <= Hu u M z) by (apply Hu_ge; lia).
    assert (Hzy : z <= Nat.min y (Hu u M z)) by lia.
    cbn beta. unfold Cin, Din. lia. }
  assert (EC : fold_right (fun w acc =>
      (4 + Hu u M w
       + fold_right (fun t acc' => (2 + Nat.min y (Hu u M t) + acc')%nat)
                    0%nat (seq 1 y)
       + fold_right (fun r acc' => (3 + Nat.min w (Hu u M r) + acc')%nat)
                    0%nat (seq y (S (w - y)))
       + fold_right (fun q acc' => (4 + Hu u M q + acc')%nat) 0%nat
                    (seq w (S (Hu u M w - w)))
       + acc)%nat) 0%nat (seq y (S (Hu u M y - y)))
    = fold_right (fun w acc =>
        (11 + Hu u M w + 2 * y + Cin u M y + 3 * (w - y) + Ein u M w y
         + 4 * (Hu u M w - w) + Bin u M w + acc)%nat) 0%nat
        (seq y (S (Hu u M y - y)))).
  { apply nfold_ext_in. intros w Hw. apply in_seq in Hw.
    rewrite (nfold_const_add 2 (fun t => Nat.min y (Hu u M t)) (seq 1 y)).
    rewrite (nfold_const_add 3 (fun r => Nat.min w (Hu u M r))
               (seq y (S (w - y)))).
    rewrite (nfold_const_add 4 (fun q => Hu u M q)
               (seq w (S (Hu u M w - w)))).
    rewrite !length_seq.
    cbn beta. unfold Cin, Ein, Bin. lia. }
  rewrite EA1, EA2, EC. lia.
Qed.

(* The second-order statistics the d = 4 level sum runs into. *)


(* The second-order statistics the d = 4 level sum runs into. *)

Definition CCin (u : list nat) (M y : nat) : nat :=
  fold_right (fun z acc => (Cin u M z + acc)%nat) 0%nat (seq 1 y).

Definition DDin (u : list nat) (M y : nat) : nat :=
  fold_right (fun z acc => (Din u M y z + acc)%nat) 0%nat (seq 1 y).

Definition EEin (u : list nat) (M y : nat) : nat :=
  fold_right (fun w acc => (Ein u M w y + acc)%nat) 0%nat
             (seq y (S (Hu u M y - y))).

Definition BBin (u : list nat) (M y : nat) : nat :=
  fold_right (fun w acc => (Bin u M w + acc)%nat) 0%nat
             (seq y (S (Hu u M y - y))).

Definition GGin (u : list nat) (M y : nat) : nat :=
  fold_right (fun w acc => (hgap u M w + acc)%nat) 0%nat
             (seq y (S (Hu u M y - y))).

Definition CCw (u : list nat) (M : nat) : nat :=
  fold_right (fun y acc => (CCin u M y + acc)%nat) 0%nat (seq 0 (S M)).
Definition DDw (u : list nat) (M : nat) : nat :=
  fold_right (fun y acc => (DDin u M y + acc)%nat) 0%nat (seq 0 (S M)).
Definition EEw (u : list nat) (M : nat) : nat :=
  fold_right (fun y acc => (EEin u M y + acc)%nat) 0%nat (seq 0 (S M)).
Definition BBw (u : list nat) (M : nat) : nat :=
  fold_right (fun y acc => (BBin u M y + acc)%nat) 0%nat (seq 0 (S M)).
Definition GGw (u : list nat) (M : nat) : nat :=
  fold_right (fun y acc => (GGin u M y + acc)%nat) 0%nat (seq 0 (S M)).
Definition PCw (u : list nat) (M : nat) : nat :=
  fold_right (fun y acc => (S (hgap u M y) * Cin u M y + acc)%nat) 0%nat
             (seq 0 (S M)).
Definition Yw (u : list nat) (M : nat) : nat :=
  fold_right (fun y acc => (y * S (hgap u M y) + acc)%nat) 0%nat
             (seq 0 (S M)).
Definition Tw (u : list nat) (M : nat) : nat :=
  fold_right (fun y acc => (tri (hgap u M y) + acc)%nat) 0%nat (seq 0 (S M)).

Lemma seq_gap_tri : forall a n,
  fold_right (fun w acc => (w - a + acc)%nat) 0%nat (seq a (S n)) = tri n.
Proof.
  intros a n.
  replace (seq a (S n)) with (map (fun t => t + a) (seq 0 (S n)))
    by (rewrite seq_add_map; reflexivity).
  rewrite (nfold_map_gen nat nat (fun w => (w - a)%nat) (fun t => t + a)
             (seq 0 (S n))).
  cbn beta.
  transitivity (fold_right (fun t acc => (t + acc)%nat) 0%nat (seq 0 (S n))).
  - apply nfold_ext_in. intros t _. lia.
  - unfold tri. reflexivity.
Qed.

Lemma Lsum_succ : forall u M,
  fold_right (fun y acc => (S (hgap u M y) + acc)%nat) 0%nat (seq 0 (S M))
  = (Lsum u M + S M)%nat.
Proof.
  intros u M.
  transitivity (fold_right (fun y acc => (hgap u M y + 1 + acc)%nat) 0%nat
                           (seq 0 (S M))).
  - apply nfold_ext_in. intros y _. lia.
  - rewrite (fold_add_split nat (hgap u M) (fun _ : nat => 1) (seq 0 (S M))).
    cbn beta. rewrite (nfold_const nat 1 (seq 0 (S M))), length_seq.
    unfold Lsum. lia.
Qed.

Lemma d4stat_B : forall u M y,
  fold_right (fun z acc =>
    (6 + 4 * Nat.min y (Hu u M z) + Cin u M z + Din u M y z + acc)%nat) 0%nat
    (seq 1 y)
  = (6 * y + 4 * Cin u M y + CCin u M y + DDin u M y)%nat.
Proof.
  intros u M y.
  rewrite (nfold_four nat (fun _ : nat => 6)
             (fun z => (4 * Nat.min y (Hu u M z))%nat)
             (fun z => Cin u M z) (fun z => Din u M y z) (seq 1 y)).
  cbn beta.
  rewrite (nfold_const nat 6 (seq 1 y)), length_seq.
  rewrite (nfold_scal nat 4 (fun z => Nat.min y (Hu u M z)) (seq 1 y)).
  unfold Cin, CCin, DDin. reflexivity.
Qed.

Lemma d4stat_C : forall u M y,
  fold_right (fun w acc =>
    (11 + Hu u M w + 2 * y + Cin u M y + 3 * (w - y) + Ein u M w y
     + 4 * (Hu u M w - w) + Bin u M w + acc)%nat) 0%nat
    (seq y (S (Hu u M y - y)))
  = (11 * S (hgap u M y) + Bin u M y + 2 * (y * S (hgap u M y))
     + S (hgap u M y) * Cin u M y + 3 * tri (hgap u M y) + EEin u M y
     + 4 * GGin u M y + BBin u M y)%nat.
Proof.
  intros u M y.
  rewrite (nfold_eight nat (fun _ : nat => 11) (fun w => Hu u M w)
             (fun _ : nat => (2 * y)%nat) (fun _ : nat => Cin u M y)
             (fun w => (3 * (w - y))%nat) (fun w => Ein u M w y)
             (fun w => (4 * (Hu u M w - w))%nat) (fun w => Bin u M w)
             (seq y (S (Hu u M y - y)))).
  cbn beta.
  rewrite (nfold_const nat 11 (seq y (S (Hu u M y - y)))), length_seq.
  rewrite (nfold_const nat (2 * y) (seq y (S (Hu u M y - y)))), length_seq.
  rewrite (nfold_const nat (Cin u M y) (seq y (S (Hu u M y - y)))), length_seq.
  rewrite (nfold_scal nat 3 (fun w => (w - y)%nat)
             (seq y (S (Hu u M y - y)))).
  rewrite (nfold_scal nat 4 (fun w => (Hu u M w - w)%nat)
             (seq y (S (Hu u M y - y)))).
  rewrite (seq_gap_tri y (Hu u M y - y)).
  cbn beta. unfold BBin, EEin, GGin, Bin, hgap. lia.
Qed.

Lemma d4stat_sum : forall M u,
  fold_right (fun y acc => (d4stat u M y + acc)%nat) 0%nat (seq 0 (S M))
  = (23 * S M + 2 * Aw u M + 9 * tri M + 15 * Lsum u M + 5 * Cw u M
     + 2 * Bw u M + CCw u M + DDw u M + 2 * Yw u M + PCw u M + 3 * Tw u M
     + EEw u M + 4 * GGw u M + BBw u M)%nat.
Proof.
  intros M u.
  transitivity (fold_right (fun y acc =>
      ((12 + 2 * Hu u M y + 3 * y + 4 * hgap u M y + Cin u M y + Bin u M y)
       + (6 * y + 4 * Cin u M y + CCin u M y + DDin u M y)
       + (11 * S (hgap u M y) + Bin u M y + 2 * (y * S (hgap u M y))
          + S (hgap u M y) * Cin u M y + 3 * tri (hgap u M y) + EEin u M y
          + 4 * GGin u M y + BBin u M y)
       + acc)%nat) 0%nat (seq 0 (S M))).
  - apply nfold_ext_in. intros y _.
    unfold d4stat. rewrite (d4stat_B u M y), (d4stat_C u M y).
    unfold hgap. lia.
  - rewrite (nfold_three nat
      (fun y => (12 + 2 * Hu u M y + 3 * y + 4 * hgap u M y + Cin u M y
                 + Bin u M y)%nat)
      (fun y => (6 * y + 4 * Cin u M y + CCin u M y + DDin u M y)%nat)
      (fun y => (11 * S (hgap u M y) + Bin u M y + 2 * (y * S (hgap u M y))
                 + S (hgap u M y) * Cin u M y + 3 * tri (hgap u M y)
                 + EEin u M y + 4 * GGin u M y + BBin u M y)%nat)
      (seq 0 (S M))).
    cbn beta.
    rewrite (nfold_six nat (fun _ : nat => 12) (fun y => (2 * Hu u M y)%nat)
               (fun y => (3 * y)%nat) (fun y => (4 * hgap u M y)%nat)
               (fun y => Cin u M y) (fun y => Bin u M y) (seq 0 (S M))).
    rewrite (nfold_four nat (fun y => (6 * y)%nat)
               (fun y => (4 * Cin u M y)%nat)
               (fun y => CCin u M y) (fun y => DDin u M y) (seq 0 (S M))).
    rewrite (nfold_eight nat (fun y => (11 * S (hgap u M y))%nat)
               (fun y => Bin u M y) (fun y => (2 * (y * S (hgap u M y)))%nat)
               (fun y => (S (hgap u M y) * Cin u M y)%nat)
               (fun y => (3 * tri (hgap u M y))%nat) (fun y => EEin u M y)
               (fun y => (4 * GGin u M y)%nat) (fun y => BBin u M y)
               (seq 0 (S M))).
    cbn beta.
    rewrite (nfold_const nat 12 (seq 0 (S M))), length_seq.
    rewrite (nfold_scal nat 2 (fun y => Hu u M y) (seq 0 (S M))).
    rewrite (nfold_scal nat 3 (fun y => y) (seq 0 (S M))).
    rewrite (nfold_scal nat 4 (fun y => hgap u M y) (seq 0 (S M))).
    rewrite (nfold_scal nat 6 (fun y => y) (seq 0 (S M))).
    rewrite (nfold_scal nat 4 (fun y => Cin u M y) (seq 0 (S M))).
    rewrite (nfold_scal nat 11 (fun y => S (hgap u M y)) (seq 0 (S M))).
    rewrite (Lsum_succ u M).
    rewrite (nfold_scal nat 2 (fun y => (y * S (hgap u M y))%nat)
               (seq 0 (S M))).
    rewrite (nfold_scal nat 3 (fun y => tri (hgap u M y)) (seq 0 (S M))).
    rewrite (nfold_scal nat 4 (fun y => GGin u M y) (seq 0 (S M))).
    cbn beta.
    unfold Aw, Lsum, Cw, Bw, CCw, DDw, EEw, BBw, GGw, PCw, Yw, Tw, tri.
    lia.
Qed.

(* The d = 4 level sum. *)


Definition tri3 (M : nat) : nat :=
  fold_right (fun y acc => (tri y + acc)%nat) 0%nat (seq 0 (S M)).

Lemma tri3_val : forall M, (6 * tri3 M = M * (M + 1) * (M + 2))%nat.
Proof.
  induction M as [|m IH]; [reflexivity|].
  assert (E : tri3 (S m) = (tri3 m + tri (S m))%nat).
  { unfold tri3 at 1. rewrite (seq_snoc (S m) 0).
    rewrite (nfold_app nat (fun y => tri y)).
    rewrite (nfold_single nat (fun y => tri y) (0 + S m)).
    cbn beta. replace (0 + S m)%nat with (S m) by lia. reflexivity. }
  rewrite E. assert (Ht := tri_val (S m)). nia.
Qed.

Definition CCtot (M : nat) : nat :=
  fold_right (fun u acc => (CCw u M + acc)%nat) 0%nat (gen132 M).
Definition DDtot (M : nat) : nat :=
  fold_right (fun u acc => (DDw u M + acc)%nat) 0%nat (gen132 M).
Definition EEtot (M : nat) : nat :=
  fold_right (fun u acc => (EEw u M + acc)%nat) 0%nat (gen132 M).
Definition BBtot (M : nat) : nat :=
  fold_right (fun u acc => (BBw u M + acc)%nat) 0%nat (gen132 M).
Definition GGtot (M : nat) : nat :=
  fold_right (fun u acc => (GGw u M + acc)%nat) 0%nat (gen132 M).
Definition PCtot (M : nat) : nat :=
  fold_right (fun u acc => (PCw u M + acc)%nat) 0%nat (gen132 M).
Definition Ytot (M : nat) : nat :=
  fold_right (fun u acc => (Yw u M + acc)%nat) 0%nat (gen132 M).
Definition Ttot (M : nat) : nat :=
  fold_right (fun u acc => (Tw u M + acc)%nat) 0%nat (gen132 M).

Lemma d4stat_sum' : forall M u,
  fold_right (fun y acc => (d4stat u M y + acc)%nat) 0%nat (seq 0 (S M))
  = (((23 * S M + 9 * tri M) + 2 * Aw u M + 15 * Lsum u M + 5 * Cw u M
      + 2 * Bw u M)
     + (CCw u M + DDw u M + 2 * Yw u M + PCw u M)
     + (3 * Tw u M + EEw u M + 4 * GGw u M + BBw u M))%nat.
Proof. intros M u. assert (K := d4stat_sum M u). lia. Qed.

Theorem Ddiag_four_stats : forall M,
  (Ddiag 4 M + card132 M * tri3 M
   = ((23 * S M + 9 * tri M) * card132 M + 2 * Atot M + 15 * Ltot M
      + 5 * Ctot M + 2 * Btot M)
     + (CCtot M + DDtot M + 2 * Ytot M + PCtot M)
     + (3 * Ttot M + EEtot M + 4 * GGtot M + BBtot M))%nat.
Proof.
  intro M.
  assert (Ec : (card132 M * tri3 M)%nat
    = fold_right (fun (_ : list nat) (acc : nat) => (tri3 M + acc)%nat) 0%nat
                 (gen132 M)).
  { rewrite (nfold_const (list nat) (tri3 M) (gen132 M)).
    unfold card132. ring. }
  assert (E1 : (Ddiag 4 M + card132 M * tri3 M)%nat
    = fold_right (fun u acc =>
        (fold_right (fun y acc' => (d4stat u M y + acc')%nat) 0%nat
                    (seq 0 (S M)) + acc)%nat) 0%nat (gen132 M)).
  { rewrite (Ddiag_four_H M), Ec.
    rewrite <- (fold_add_split (list nat)
      (fun u => fold_right (fun y acc' => (d4form u M y + acc')%nat) 0%nat
                           (seq 0 (S M)))
      (fun _ : list nat => tri3 M) (gen132 M)).
    apply nfold_ext_in. intros u Hin.
    unfold tri3.
    rewrite <- (fold_add_split nat (fun y => d4form u M y) (fun y => tri y)
                  (seq 0 (S M))).
    apply nfold_ext_in. intros y Hy. apply in_seq in Hy.
    apply (d4form_stats M u y Hin ltac:(lia)). }
  rewrite E1.
  transitivity (fold_right (fun u acc =>
      (((23 * S M + 9 * tri M) + 2 * Aw u M + 15 * Lsum u M + 5 * Cw u M
        + 2 * Bw u M)
       + (CCw u M + DDw u M + 2 * Yw u M + PCw u M)
       + (3 * Tw u M + EEw u M + 4 * GGw u M + BBw u M)
       + acc)%nat) 0%nat (gen132 M)).
  - apply nfold_ext_in. intros u _. apply d4stat_sum'.
  - rewrite (nfold_three (list nat)
      (fun u => ((23 * S M + 9 * tri M) + 2 * Aw u M + 15 * Lsum u M
                 + 5 * Cw u M + 2 * Bw u M)%nat)
      (fun u => (CCw u M + DDw u M + 2 * Yw u M + PCw u M)%nat)
      (fun u => (3 * Tw u M + EEw u M + 4 * GGw u M + BBw u M)%nat)
      (gen132 M)).
    cbn beta.
    rewrite (nfold_five (list nat)
      (fun _ : list nat => (23 * S M + 9 * tri M)%nat)
      (fun u => (2 * Aw u M)%nat) (fun u => (15 * Lsum u M)%nat)
      (fun u => (5 * Cw u M)%nat) (fun u => (2 * Bw u M)%nat) (gen132 M)).
    rewrite (nfold_four (list nat) (fun u => CCw u M) (fun u => DDw u M)
      (fun u => (2 * Yw u M)%nat) (fun u => PCw u M) (gen132 M)).
    rewrite (nfold_four (list nat) (fun u => (3 * Tw u M)%nat)
      (fun u => EEw u M) (fun u => (4 * GGw u M)%nat) (fun u => BBw u M)
      (gen132 M)).
    cbn beta.
    rewrite (nfold_const (list nat) (23 * S M + 9 * tri M) (gen132 M)).
    rewrite (nfold_scal (list nat) 2 (fun u => Aw u M) (gen132 M)).
    rewrite (nfold_scal (list nat) 15 (fun u => Lsum u M) (gen132 M)).
    rewrite (nfold_scal (list nat) 5 (fun u => Cw u M) (gen132 M)).
    rewrite (nfold_scal (list nat) 2 (fun u => Bw u M) (gen132 M)).
    rewrite (nfold_scal (list nat) 2 (fun u => Yw u M) (gen132 M)).
    rewrite (nfold_scal (list nat) 3 (fun u => Tw u M) (gen132 M)).
    rewrite (nfold_scal (list nat) 4 (fun u => GGw u M) (gen132 M)).
    cbn beta.
    unfold Atot, Ltot, Ctot, Btot, CCtot, DDtot, EEtot, BBtot, GGtot,
           PCtot, Ytot, Ttot, card132.
    lia.
Qed.

(* the redundancy among the new statistics: the subtree gap sum is the subtree
   H sum less the positions it runs over *)
Lemma GGin_split : forall u M y, y <= M ->
  (GGin u M y + (y * S (hgap u M y) + tri (hgap u M y)) = Bin u M y)%nat.
Proof.
  intros u M y HyM.
  assert (Hgy : y <= Hu u M y) by (apply Hu_ge; exact HyM).
  assert (Hcy := Hu_le_cap u M y).
  assert (E : fold_right (fun w acc => (hgap u M w + w + acc)%nat) 0%nat
                (seq y (S (Hu u M y - y)))
            = Bin u M y).
  { unfold Bin. apply nfold_ext_in. intros w Hw. apply in_seq in Hw.
    assert (HwM : w <= M) by lia.
    assert (Hg : w <= Hu u M w) by (apply Hu_ge; exact HwM).
    unfold hgap. lia. }
  rewrite <- E.
  rewrite (fold_add_split nat (fun w => hgap u M w) (fun w => w)
             (seq y (S (Hu u M y - y)))).
  cbn beta.
  assert (F : fold_right (fun w acc => (w + acc)%nat) 0%nat
                (seq y (S (Hu u M y - y)))
            = (y * S (Hu u M y - y) + tri (Hu u M y - y))%nat).
  { transitivity (fold_right (fun w acc => (y + (w - y) + acc)%nat) 0%nat
                    (seq y (S (Hu u M y - y)))).
    - apply nfold_ext_in. intros w Hw. apply in_seq in Hw. lia.
    - rewrite (fold_add_split nat (fun _ : nat => y) (fun w => (w - y)%nat)
                 (seq y (S (Hu u M y - y)))).
      cbn beta.
      rewrite (nfold_const nat y (seq y (S (Hu u M y - y)))), length_seq.
      rewrite (seq_gap_tri y (Hu u M y - y)). lia. }
  rewrite F. unfold GGin, hgap. lia.
Qed.

Lemma GGw_split : forall u M,
  (GGw u M + Yw u M + Tw u M = Bw u M)%nat.
Proof.
  intros u M. unfold GGw, Yw, Tw, Bw.
  rewrite <- (nfold_three nat (fun y => GGin u M y)
                (fun y => (y * S (hgap u M y))%nat)
                (fun y => tri (hgap u M y)) (seq 0 (S M))).
  apply nfold_ext_in. intros y Hy. apply in_seq in Hy.
  assert (K := GGin_split u M y ltac:(lia)). lia.
Qed.

Lemma GGtot_split : forall M, (GGtot M + Ytot M + Ttot M = Btot M)%nat.
Proof.
  intro M. unfold GGtot, Ytot, Ttot, Btot.
  rewrite <- (nfold_three (list nat) (fun u => GGw u M) (fun u => Yw u M)
                (fun u => Tw u M) (gen132 M)).
  apply nfold_ext_in. intros u _. apply GGw_split.
Qed.


(* The position-weighted statistics reduce to the sum of y H(y). *)


(* The two position-weighted statistics reduce to one: the sum of y H(y). *)

Definition Sq (M : nat) : nat :=
  fold_right (fun y acc => (y * y + acc)%nat) 0%nat (seq 0 (S M)).

Lemma Sq_val : forall M, (6 * Sq M = M * (M + 1) * (2 * M + 1))%nat.
Proof.
  induction M as [|m IH]; [reflexivity|].
  assert (E : Sq (S m) = (Sq m + S m * S m)%nat).
  { unfold Sq at 1. rewrite (seq_snoc (S m) 0).
    rewrite (nfold_app nat (fun y => (y * y)%nat)).
    rewrite (nfold_single nat (fun y => (y * y)%nat) (0 + S m)).
    cbn beta. replace (0 + S m)%nat with (S m) by lia. reflexivity. }
  rewrite E. nia.
Qed.

Definition YHw (u : list nat) (M : nat) : nat :=
  fold_right (fun y acc => (y * Hu u M y + acc)%nat) 0%nat (seq 0 (S M)).

Definition Hsq0 (u : list nat) (M : nat) : nat :=
  fold_right (fun y acc => (Hu u M y * Hu u M y + acc)%nat) 0%nat
             (seq 0 (S M)).

Lemma Hsq0_split : forall u M, Hsq0 u M = (M * M + Hsq u M)%nat.
Proof.
  intros u M. unfold Hsq0, Hsq.
  change (seq 0 (S M)) with (0%nat :: seq 1 M).
  rewrite (nfold_cons nat (fun y => (Hu u M y * Hu u M y)%nat) 0%nat
             (seq 1 M)).
  rewrite (Hu_zero u M). reflexivity.
Qed.

Lemma Yw_YH : forall u M, (Yw u M + Sq M = YHw u M + tri M)%nat.
Proof.
  intros u M. unfold Yw, Sq, YHw, tri.
  rewrite <- (fold_add_split nat (fun y => (y * S (hgap u M y))%nat)
                (fun y => (y * y)%nat) (seq 0 (S M))).
  rewrite <- (fold_add_split nat (fun y => (y * Hu u M y)%nat) (fun y => y)
                (seq 0 (S M))).
  apply nfold_ext_in. intros y Hy. apply in_seq in Hy.
  assert (Hg : y <= Hu u M y) by (apply Hu_ge; lia).
  unfold hgap. nia.
Qed.

Lemma Tw_YH : forall u M,
  (2 * Tw u M + 2 * YHw u M = Hsq0 u M + Sq M + Lsum u M)%nat.
Proof.
  intros u M. unfold Tw, YHw, Hsq0, Sq, Lsum.
  rewrite <- (nfold_scal nat 2 (fun y => tri (hgap u M y)) (seq 0 (S M))).
  rewrite <- (nfold_scal nat 2 (fun y => (y * Hu u M y)%nat) (seq 0 (S M))).
  rewrite <- (fold_add_split nat (fun y => (2 * tri (hgap u M y))%nat)
                (fun y => (2 * (y * Hu u M y))%nat) (seq 0 (S M))).
  rewrite <- (nfold_three nat (fun y => (Hu u M y * Hu u M y)%nat)
                (fun y => (y * y)%nat) (hgap u M) (seq 0 (S M))).
  apply nfold_ext_in. intros y Hy. apply in_seq in Hy.
  assert (Hg : y <= Hu u M y) by (apply Hu_ge; lia).
  unfold hgap.
  remember (Hu u M y - y)%nat as g eqn:Eg.
  assert (EH : Hu u M y = (y + g)%nat) by lia.
  assert (Ht := tri_val g).
  rewrite EH. nia.
Qed.

Definition YHtot (M : nat) : nat :=
  fold_right (fun u acc => (YHw u M + acc)%nat) 0%nat (gen132 M).

Definition Hsq0tot (M : nat) : nat :=
  fold_right (fun u acc => (Hsq0 u M + acc)%nat) 0%nat (gen132 M).

Lemma Hsq0tot_split : forall M,
  Hsq0tot M = (card132 M * (M * M) + Hsqtot M)%nat.
Proof.
  intro M. unfold Hsq0tot, Hsqtot.
  transitivity (fold_right (fun u acc => (M * M + Hsq u M + acc)%nat) 0%nat
                           (gen132 M)).
  - apply nfold_ext_in. intros u _. apply Hsq0_split.
  - rewrite (fold_add_split (list nat) (fun _ : list nat => (M * M)%nat)
               (fun u => Hsq u M) (gen132 M)).
    cbn beta. rewrite (nfold_const (list nat) (M * M) (gen132 M)).
    unfold card132. ring.
Qed.

Lemma Ytot_YH : forall M,
  (Ytot M + card132 M * Sq M = YHtot M + card132 M * tri M)%nat.
Proof.
  intro M. unfold Ytot, YHtot.
  assert (E1 : (card132 M * Sq M)%nat
    = fold_right (fun (_ : list nat) (acc : nat) => (Sq M + acc)%nat) 0%nat
                 (gen132 M)).
  { rewrite (nfold_const (list nat) (Sq M) (gen132 M)). unfold card132. ring. }
  assert (E2 : (card132 M * tri M)%nat
    = fold_right (fun (_ : list nat) (acc : nat) => (tri M + acc)%nat) 0%nat
                 (gen132 M)).
  { rewrite (nfold_const (list nat) (tri M) (gen132 M)). unfold card132. ring. }
  rewrite E1, E2.
  rewrite <- (fold_add_split (list nat) (fun u => Yw u M)
                (fun _ : list nat => Sq M) (gen132 M)).
  rewrite <- (fold_add_split (list nat) (fun u => YHw u M)
                (fun _ : list nat => tri M) (gen132 M)).
  apply nfold_ext_in. intros u _. apply Yw_YH.
Qed.

Lemma Ttot_YH : forall M,
  (2 * Ttot M + 2 * YHtot M
   = Hsq0tot M + card132 M * Sq M + Ltot M)%nat.
Proof.
  intro M. unfold Ttot, YHtot, Hsq0tot, Ltot.
  assert (E1 : (card132 M * Sq M)%nat
    = fold_right (fun (_ : list nat) (acc : nat) => (Sq M + acc)%nat) 0%nat
                 (gen132 M)).
  { rewrite (nfold_const (list nat) (Sq M) (gen132 M)). unfold card132. ring. }
  rewrite E1.
  rewrite <- (nfold_scal (list nat) 2 (fun u => Tw u M) (gen132 M)).
  rewrite <- (nfold_scal (list nat) 2 (fun u => YHw u M) (gen132 M)).
  rewrite <- (fold_add_split (list nat) (fun u => (2 * Tw u M)%nat)
                (fun u => (2 * YHw u M)%nat) (gen132 M)).
  rewrite <- (nfold_three (list nat) (fun u => Hsq0 u M)
                (fun _ : list nat => Sq M) (fun u => Lsum u M) (gen132 M)).
  apply nfold_ext_in. intros u _. apply Tw_YH.
Qed.

(* The total of the safe values. *)


(* The total of the safe values.  Under the max-split only the right factor's
   safe values survive, together with the new maximum. *)

Definition SSw (u : list nat) (M : nat) : nat :=
  fold_right (fun y acc => ((if safeb u y then y else 0) + acc)%nat) 0%nat
             (seq 1 M).

Definition SStot (M : nat) : nat :=
  fold_right (fun u acc => (SSw u M + acc)%nat) 0%nat (gen132 M).

Theorem SSw_midmax : forall a b,
  is_perm a (length a) -> is_perm b (length b) ->
  SSw (midmax a b) (length a + S (length b))
  = (SSw b (length b) + (length a + S (length b)))%nat.
Proof.
  intros a b Hpa Hpb.
  assert (HN : length (midmax a b) = (length a + S (length b))%nat)
    by apply midmax_length.
  assert (Hpw0 : is_perm (midmax a b) (S (length a + length b)))
    by (apply midmax_perm; assumption).
  assert (Hpw : is_perm (midmax a b) (length (midmax a b))).
  { rewrite HN.
    replace (length a + S (length b))%nat with (S (length a + length b))
      by lia. exact Hpw0. }
  assert (Hsafe_w : forall y, safe_at (midmax a b) y
                    <-> Hu (midmax a b) (length a + S (length b)) y
                        = (length a + S (length b))%nat).
  { intro y. rewrite <- HN. apply (safe_iff_Hu (midmax a b) y Hpw). }
  assert (Hfalse : forall y,
    Hu (midmax a b) (length a + S (length b)) y
      <> (length a + S (length b))%nat ->
    (if safeb (midmax a b) y then y else 0) = 0).
  { intros y Hne.
    destruct (safeb (midmax a b) y) eqn:E2; [|reflexivity].
    exfalso. apply Hne. apply Hsafe_w. apply safeb_spec. exact E2. }
  unfold SSw at 1. rewrite (seq_split_hi (length a) (length b)).
  rewrite !(nfold_app nat
    (fun y => if safeb (midmax a b) y then y else 0)).
  replace (seq (length a + S (length b)) 1)
    with ((length a + S (length b)) :: nil) by reflexivity.
  rewrite (nfold_single nat
    (fun y => if safeb (midmax a b) y then y else 0)
    (length a + S (length b))).
  cbn beta.
  assert (Ptop : (if safeb (midmax a b) (length a + S (length b))
                  then (length a + S (length b))%nat else 0)
               = (length a + S (length b))%nat).
  { assert (Hs : safe_at (midmax a b) (length a + S (length b))).
    { apply Hsafe_w. apply Hu_top. }
    assert (K : safeb (midmax a b) (length a + S (length b)) = true)
      by (apply safeb_spec; exact Hs).
    rewrite K. reflexivity. }
  assert (Plo : fold_right (fun y acc =>
      ((if safeb (midmax a b) y then y else 0) + acc)%nat) 0%nat
      (seq 1 (length b))
    = SSw b (length b)).
  { unfold SSw. apply nfold_ext_in. intros y Hy. apply in_seq in Hy.
    destruct (safeb b y) eqn:Es.
    - assert (Hsb : safe_at b y) by (apply safeb_spec; exact Es).
      assert (Ew := Hu_midmax_lo_safe a b y ltac:(lia) ltac:(lia) Hsb).
      assert (Hsw : safe_at (midmax a b) y) by (apply Hsafe_w; exact Ew).
      assert (Ks : safeb (midmax a b) y = true)
        by (apply safeb_spec; exact Hsw).
      rewrite Ks. reflexivity.
    - assert (Hnsb : ~ safe_at b y).
      { intro C. assert (K : safeb b y = true) by (apply safeb_spec; exact C).
        rewrite Es in K. discriminate. }
      assert (Ew := Hu_midmax_lo_unsafe a b y ltac:(lia) ltac:(lia) Hpb Hnsb).
      assert (Hc := Hu_le_cap b (length b) y).
      rewrite (Hfalse y ltac:(lia)). reflexivity. }
  assert (Phi : fold_right (fun y acc =>
      ((if safeb (midmax a b) y then y else 0) + acc)%nat) 0%nat
      (seq (S (length b)) (length a))
    = 0%nat).
  { transitivity (fold_right (fun y acc => (0 + acc)%nat) 0%nat
                    (seq (S (length b)) (length a))).
    - apply nfold_ext_in. intros y Hy. apply in_seq in Hy.
      assert (Ew := Hu_midmax_hi a b y Hpa Hpb ltac:(lia) ltac:(lia)).
      assert (Hc := Hu_le_cap a (length a) (y - length b)).
      rewrite (Hfalse y ltac:(lia)). reflexivity.
    - rewrite (nfold_const nat 0 (seq (S (length b)) (length a))). ring. }
  rewrite Plo, Phi, Ptop. lia.
Qed.

Theorem SStot_expand : forall m,
  SStot (S m)
  = fold_right (fun k acc =>
      (card132 k * SStot (m - k) + card132 k * card132 (m - k) * S m
       + acc)%nat) 0%nat (seq 0 (S m)).
Proof.
  intro m. unfold SStot at 1.
  rewrite (nfold_pairs132 m (fun w => SSw w (S m))).
  apply nfold_ext_in. intros k Hk. apply in_seq in Hk. destruct Hk as [_ Hk].
  assert (HkM : (k <= m)%nat) by lia.
  transitivity (fold_right (fun a acc =>
      (SStot (m - k) + card132 (m - k) * S m + acc)%nat) 0%nat (gen132 k)).
  - apply nfold_ext_in. intros a Ha.
    assert (Hpa0 : is_perm a k) by (apply gen132_perm; exact Ha).
    assert (Hla : length a = k) by (apply (perm_len a k); exact Hpa0).
    assert (Hpa : is_perm a (length a)) by (rewrite Hla; exact Hpa0).
    transitivity (fold_right (fun v acc =>
        (SSw v (m - k) + S m + acc)%nat) 0%nat (gen132 (m - k))).
    + apply nfold_ext_in. intros v Hv.
      assert (Hpv0 : is_perm v (m - k)) by (apply gen132_perm; exact Hv).
      assert (Hlv : length v = (m - k)%nat)
        by (apply (perm_len v (m - k)); exact Hpv0).
      assert (Hpv : is_perm v (length v)) by (rewrite Hlv; exact Hpv0).
      assert (K := SSw_midmax a v Hpa Hpv).
      rewrite Hla, Hlv in K.
      replace (k + S (m - k))%nat with (S m) in K by lia.
      exact K.
    + rewrite (fold_add_split (list nat) (fun v => SSw v (m - k))
                 (fun _ : list nat => S m) (gen132 (m - k))).
      cbn beta.
      rewrite (nfold_const (list nat) (S m) (gen132 (m - k))).
      unfold SStot, card132. ring.
  - rewrite (nfold_const (list nat)
               (SStot (m - k) + card132 (m - k) * S m) (gen132 k)).
    unfold card132. ring.
Qed.

Lemma conv_shift_lin : forall m,
  (conv card132 (fun n => (n * card132 (S n))%nat) m
   + conv (fun k => (k * card132 k)%nat) (fun n => card132 (S n)) m
   = m * conv card132 (fun n => card132 (S n)) m)%nat.
Proof.
  intro m. unfold conv.
  rewrite <- (nfold_scal nat m (fun k => (card132 k * card132 (S (m - k)))%nat)
                (seq 0 (S m))).
  rewrite <- (fold_add_split nat
    (fun k => (card132 k * ((m - k) * card132 (S (m - k))))%nat)
    (fun k => (k * card132 k * card132 (S (m - k)))%nat) (seq 0 (S m))).
  apply nfold_ext_in. intros k Hk. apply in_seq in Hk.
  remember (m - k)%nat as d eqn:Ed.
  assert (EM : m = (k + d)%nat) by lia. rewrite EM. ring.
Qed.

Lemma SStot_step : forall m,
  (forall j, (j <= m)%nat -> (2 * SStot j = j * card132 (S j))%nat) ->
  (2 * SStot (S m) = S m * card132 (S (S m)))%nat.
Proof.
  intros m IH.
  assert (E : (2 * SStot (S m))%nat
    = (conv card132 (fun n => (n * card132 (S n))%nat) m
       + 2 * S m * conv card132 card132 m)%nat).
  { rewrite (SStot_expand m).
    rewrite <- (conv_scal_l (2 * S m) card132 card132 m).
    unfold conv.
    rewrite <- (nfold_scal nat 2
      (fun k => (card132 k * SStot (m - k)
                 + card132 k * card132 (m - k) * S m)%nat) (seq 0 (S m))).
    rewrite <- (fold_add_split nat
      (fun k => (card132 k * ((m - k) * card132 (S (m - k))))%nat)
      (fun k => (2 * S m * card132 k * card132 (m - k))%nat) (seq 0 (S m))).
    apply nfold_ext_in. intros k Hk. apply in_seq in Hk.
    assert (K := IH (m - k)%nat ltac:(lia)).
    assert (K2 := f_equal (Nat.mul (card132 k)) K). nia. }
  assert (V0 := conv_V0 m).
  assert (V1 := conv_shift1 (fun k => k) m). cbn beta in V1.
  assert (W := wsum_id_val (S m)).
  assert (L := conv_shift_lin m).
  assert (Ccat := conv_cat m).
  assert (R := card132_ratio (S m)).
  nia.
Qed.

Theorem SStot_closed_upto : forall N M, (M <= N)%nat ->
  (2 * SStot M = M * card132 (S M))%nat.
Proof.
  induction N as [|N IHN]; intros M HM.
  - assert (E : M = 0%nat) by lia. subst M. reflexivity.
  - destruct (le_lt_dec M N) as [H|H]; [apply IHN; exact H|].
    assert (EM : M = S N) by lia. subst M.
    apply SStot_step. intros j Hj. apply IHN. lia.
Qed.

Theorem SStot_closed : forall M, (2 * SStot M = M * card132 (S M))%nat.
Proof. intro M. apply (SStot_closed_upto M M). lia. Qed.
