(* Print Assumptions over every result of Av1324.v. *)

Require Import List ZArith.
Import ListNotations.
Require Import Av1324.
Open Scope nat_scope.
Print Assumptions max_insertion.
Print Assumptions append_1324.
Print Assumptions append_rule.
Print Assumptions append_downward_closed.
Print Assumptions append_new_minimum.
Print Assumptions safe_iff_split.
Print Assumptions split_132.
Print Assumptions tail_confinement.
Print Assumptions localise.
Print Assumptions decreasing_tail_avoids.
Print Assumptions dsort_perm.
Print Assumptions dsort_sortedD.
Print Assumptions sortedD_strict.
Print Assumptions dsort_avoids.
Print Assumptions dsort_length.
Print Assumptions dsort_In.
Print Assumptions rankin_lt.
Print Assumptions rankin_inj.
Print Assumptions perm_filter.
Print Assumptions rankin_perm.
Print Assumptions map_nth_def.
Print Assumptions std_perm_eq.
Print Assumptions filter_all_true.
Print Assumptions dec_rankin.
Print Assumptions dec_std_nth.
Print Assumptions is_perm_perm.
Print Assumptions decpat_nth.
Print Assumptions dec_std.
Compute (decpat 4, std (7::4::2::nil)).
Compute (std (7::4::2::nil)).
Compute (dsort (2::0::3::1::nil)).
Print Assumptions tromino_fibre.
Print Assumptions domino_criterion_conv.
Print Assumptions c1324_c132.
Print Assumptions high_block_criterion.
Print Assumptions high_block_criterion_conv.
Print Assumptions domino_criterion.
Print Assumptions skew_avoids.
Print Assumptions skew_perm.
Print Assumptions skew_inj.
Print Assumptions card_supermult.
Print Assumptions chain_local.
Print Assumptions chain_pairwise.
Print Assumptions chain_two_cells.
Print Assumptions chain_pairs_suffice.
Print Assumptions layer_cake.
Print Assumptions layer_A.
Print Assumptions layer_B.
Print Assumptions layer_AB.
Print Assumptions sumn_prodn.
Print Assumptions pqd_chebyshev.
Print Assumptions pqd_square.
Print Assumptions append_132.
Print Assumptions bump_gt_v.
Print Assumptions ext_132.
Print Assumptions safe_at_dec.
Print Assumptions safeb_spec.
Print Assumptions gen132_sound.
Print Assumptions gen132_complete.
Print Assumptions gen132_spec.
Print Assumptions gen132_nodup.
Print Assumptions card132_is_cardinality.
Print Assumptions gen132_incl.
Print Assumptions card132_le_card.
Print Assumptions relab_132.
Print Assumptions dec_fibre_free.
Print Assumptions midmax_132.
Print Assumptions midmax_avoids.
Print Assumptions midmax_perm.
Print Assumptions midmax_inj.
Print Assumptions perm_full.
Print Assumptions contains_132_addc.
Print Assumptions midmax_split.
Print Assumptions midmax_max_unique.
Print Assumptions midmax_len_eq.
Print Assumptions length_flat_map_gen.
Print Assumptions pairs132_sound.
Print Assumptions pairs132_complete.
Print Assumptions pairs132_nodup.
Print Assumptions card132_convolution.
Print Assumptions binomN_central.
Print Assumptions card132_binom_of_ratio.
Print Assumptions card132_ratio_of_binom.
Print Assumptions card132_ratio_upto_6.
Print Assumptions card132_binom_upto_7.
(* (m+1) card132 m against C(2m,m), at every size the enumerator reaches *)
Compute (map (fun m => (S m * card132 m, binomN (2 * m) m)) (seq 0 8)).
Print Assumptions strict_dec_sortedD.
Print Assumptions dec_std_conv.
Print Assumptions dec_fibre_iff.
Print Assumptions dec_fibre_avoids.
Print Assumptions choose_length.
Print Assumptions choose_incr.
Print Assumptions nth_firstn_lt.
Print Assumptions dominates_upto_firstn.
Print Assumptions pqd_gives_chebyshev.
Print Assumptions idx_lt.
Print Assumptions idx_nth.
Print Assumptions nth_idx.
Print Assumptions pinv_length.
Print Assumptions pinv_nth.
Print Assumptions pinv_nth_nth.
Print Assumptions nth_pinv_nth.
Print Assumptions pinv_perm.
Print Assumptions pinv_involutive.
Print Assumptions pinv_132.
Print Assumptions pinv_avoids_132.
Print Assumptions pinv_1324.
Print Assumptions pinv_avoids_1324.
Print Assumptions pinv_inj.
Print Assumptions pinv_gen132.
Print Assumptions allpairs_spec.
Print Assumptions allpairs_nodup.
Print Assumptions invpairs_transport.
Print Assumptions swapnth_inj.
Print Assumptions invcount_le.
Print Assumptions invcount_pinv.
(* 201 and its inverse 120 both have two inversions *)
Compute (invcount (2 :: 0 :: 1 :: nil), invcount (pinv (2 :: 0 :: 1 :: nil))).
(* the inversion strata of Av(132)_4, which the involution permutes *)
Compute (map invcount (gen132 4)).
Print Assumptions nfold_perm.
Print Assumptions nfold_map.
Print Assumptions pqd_totals_agree.
Print Assumptions pqd_suffices.
Print Assumptions sV_cov_pair_form.
(* the two coordinate totals of pqd_pairs agree at m = 4 *)
Compute (sumA (pqd_pairs 4), sumB (pqd_pairs 4)).
(* 201 inverts to 120, and back *)
Compute (pinv (2 :: 0 :: 1 :: nil), pinv (pinv (2 :: 0 :: 1 :: nil))).
Print Assumptions dedup_snd_incl.
Print Assumptions dedup_snd_nodup.
Print Assumptions dedup_snd_distinct.
Print Assumptions phipairs_shape.
Print Assumptions incl_map_of.
Print Assumptions witness_19.
Print Assumptions no_coarsening.
(* 23 avoiders of length 4, 19 distinct one-step lookaheads, 16 states allowed *)
Compute (length (gen 4), length (dedup_snd phipairs), Nat.pow 2 4).
(* the statistic behind the correlation inequality, and its transpose *)
Compute (pqd_pairs 3).
Compute (map (fun d => length (choose 5 d)) (seq 0 6)).
(* the convolution, checked numerically: 42 = 14+5+4+5+14 *)
Compute (card132 5,
         fold_right (fun k acc => (card132 k * card132 (4 - k) + acc)%nat)
                    0%nat (seq 0 5)).
(* the enumerator must reproduce the Catalan numbers *)
Compute (card132 0, card132 1, card132 2, card132 3, card132 4, card132 5).
Compute (card132 6, card 6).
Print Assumptions foldZ_pick_one.
Print Assumptions foldZ_add.
Print Assumptions csum_fibres.
(* summing Pstat over the inversion strata of Av(132)_4 recovers the total *)
Compute (csum (map Pz (gen132 4)),
         foldZ (fun k => csum (map Pz
                  (filter (fun b => if Nat.eq_dec (invcount b) k
                                    then true else false) (gen132 4))))
               (nodup Nat.eq_dec (map invcount (gen132 4)))).
Print Assumptions cov_symmetric_split.
Print Assumptions sym_antisym_orthogonal.
Print Assumptions var_splits.
Print Assumptions csum_nonneg.
Print Assumptions z_sq_nonneg.
Print Assumptions minors_nonneg.
Print Assumptions minors_head.
Print Assumptions lagrange_identity.
Print Assumptions cauchy_schwarz.
Print Assumptions nprodz_pos.
Print Assumptions nsumz_nonneg.
Print Assumptions weighted_cauchy_schwarz.
Print Assumptions defw_closed.
Print Assumptions strata_split.
Print Assumptions between_nonneg.
Print Assumptions cov_ge_within.
Print Assumptions cov_nonneg_of_within_bounded.
Print Assumptions invkeys_witness.
Print Assumptions strata_posw.
Print Assumptions sV_cov_ge_within.
Print Assumptions sV_between_nonneg.
Print Assumptions ssumz_map_strata.
Print Assumptions strata_S_total.
Print Assumptions strata_P_total.
(* the inversion strata of Av(132)_4 and their sizes: 1,3,3,3,2,1,1 over 14 *)
Compute (invkeys 4, map (fun k => length (invfibre 4 k)) (invkeys 4)).
(* the split at m = 4 for sV, the corner a = c = 2: total, within, between *)
Compute (let l := strata_of Pz 4 in
         ((nprodz (proj_ns l) * (nsumz (proj_ns l) * stP l
                                 - ssumz (proj_ns l) * ssumz (proj_ns l)))%Z,
          (nsumz (proj_ns l) * defw l)%Z,
          (nsumz (proj_ns l) * qsumz (proj_ns l)
           - nprodz (proj_ns l) * ssumz (proj_ns l)
             * ssumz (proj_ns l))%Z)).
(* two strata, sizes 1 and 2, sums 3 and 5, cross sums 9 and 13:
   the split reads 2*(3*22 - 8^2) = 4 = 3 + 1, within then between *)
Compute (let l := (mkStratum 1 3 9 :: mkStratum 2 5 13 :: nil) in
         ((nprodz (proj_ns l)
           * (nsumz (proj_ns l) * stP l
              - ssumz (proj_ns l) * ssumz (proj_ns l)))%Z,
          (nsumz (proj_ns l) * defw l)%Z,
          (nsumz (proj_ns l) * qsumz (proj_ns l)
           - nprodz (proj_ns l) * ssumz (proj_ns l) * ssumz (proj_ns l))%Z)).
(* weights 1 and 2 with sums 3 and 5: 2*8^2 = 128 against 3*43 = 129 *)
Compute (let l := ((1%nat, 3%Z) :: (2%nat, 5%Z) :: nil) in
         ((nprodz l * ssumz l * ssumz l)%Z, (nsumz l * qsumz l)%Z)).
Print Assumptions csum_map_lin4.
Print Assumptions csum_inner.
Print Assumptions cov_pair_form.
Print Assumptions cov_iff_pair_sum.
(* f n = n^2 and s n = 3 - n on {0,1,2,3}: both sides come to -328 *)
Compute (let L := (0 :: 1 :: 2 :: 3 :: nil)%nat in
         let f := (fun n : nat => Z.of_nat (n * n)) in
         let s := (fun n : nat => 3 - n)%nat in
         ((2 * (Z.of_nat (length L) * csum (map (fun x => (f x * f (s x))%Z) L)
                - csum (map f L) * csum (map f L)))%Z,
          csum2 L (fun x y => ((f x - f y) * (f (s x) - f (s y)))%Z))).
(* Lagrange on (1,2),(3,4),(5,6): 35*56 - 44*44 = 24 = 4 + 16 + 4 *)
Compute (let L := ((1,2) :: (3,4) :: (5,6) :: nil)%Z in
         ((sqf L * sqs L - dotp L * dotp L)%Z, minors L)).
Print Assumptions csum_perm.
Print Assumptions csum_map_invol.
Print Assumptions cell_close.
Print Assumptions dsum_avoids.
Print Assumptions dsum_132_gives_1324.
Compute (skew [1;0] [0;2;1]).
Compute (card 2 * card 3, card 5).
Print Assumptions block_split_1324.
Print Assumptions candidates_low.
Print Assumptions candidates_high.
Print Assumptions append_rule_profile.
Print Assumptions three_values_append.
Print Assumptions legality_capped.
Print Assumptions mu_exists.
Print Assumptions legal_iff_le_mu.
Print Assumptions max_last_indecomposable.
Print Assumptions indecomposable_iff_max_last.
Print Assumptions block_iff_body.
Print Assumptions factor_exists.
Print Assumptions factor_unique.
Print Assumptions factor_avoids.
Print Assumptions ext_iff_append.
Print Assumptions ext_bijection.
Print Assumptions gen_sound.
Print Assumptions gen_complete.
Print Assumptions gen_nodup.
Print Assumptions card_is_cardinality.
Print Assumptions fibre_count.
Print Assumptions card_succ.
Print Assumptions cons_1324.
Print Assumptions cons_1324_avoid.
Print Assumptions subseq_index.
Print Assumptions subseq_213.
Print Assumptions filter_subseq.
Print Assumptions rank_spec.
Print Assumptions rank_mono.
Print Assumptions above_213_gives_above.
Print Assumptions above_gives_above_213.
Print Assumptions above_213_iff.
Print Assumptions cons_1324_above.
Print Assumptions cons_1324_above_avoid.
Print Assumptions cons_min_1324.
Compute card 0. Compute card 1. Compute card 2.
Compute card 3. Compute card 4. Compute card 5.
Print Assumptions sub_1324_213.
Print Assumptions cons_min_1324.
Print Assumptions rc_involutive.
Print Assumptions rc_avoid_1324.
Print Assumptions rc_perm.
Print Assumptions rc_gen.
Print Assumptions avoid_1324_quadrant.
Print Assumptions mu_append.
Print Assumptions mu_append_free.
Print Assumptions mu_append_none.
Print Assumptions no_new_three_iff_safe.
Print Assumptions transfer_step.
Print Assumptions mfun_exists.
Print Assumptions new_three_dec.
Print Assumptions new_three_append.
Print Assumptions mfun_append_low.
Print Assumptions mfun_append_high.
Print Assumptions mfun_append_new.
Print Assumptions gen_extend.
Print Assumptions card_extend.
Print Assumptions card_extend_one.
Compute card (2 + 3).
Compute fold_right (fun u acc => (length (extend u 2 3) + acc)%nat) 0%nat (gen 2).
Print Assumptions binomZ_step.
Print Assumptions binomZ_pivot.
Print Assumptions Ssum_rec.
Print Assumptions Tsum_rec.
Print Assumptions sumZ_comb.
Print Assumptions padd_spec.
Print Assumptions psub_spec.
Print Assumptions shiftp_spec.
Print Assumptions shiftp_len.
Print Assumptions diff_drop.
Print Assumptions delta_shift_in.
Print Assumptions delta_vanishes.
Print Assumptions sum_telescope.
Print Assumptions sum_delta.
Print Assumptions polyQ_ext.
Print Assumptions delta_ext.
Print Assumptions sumQn_ext.
Print Assumptions odd_coeffs_sum.
Print Assumptions binQ_absorb.
Print Assumptions binQ_pascal.
Print Assumptions binQ_ext.
Print Assumptions binQ_diag.
Print Assumptions binQ_zero.
Print Assumptions Qn_S.
Print Assumptions Qn_add.
Print Assumptions Qn_mul.
Print Assumptions Qn_sub.
Print Assumptions Qn_pos_nonzero.
Print Assumptions altQ_S.
Print Assumptions altQ_sub.
Print Assumptions Qdiv_zero_num.
Print Assumptions wQ_nonzero.
Print Assumptions sumQn_ext_le.
Print Assumptions sumQn_shift.
Print Assumptions sumQn_rev.
Print Assumptions sumQn_scal.
Print Assumptions alt_partial.
Print Assumptions alt_row.
Print Assumptions collapse_term.
Print Assumptions collapse_sum.
Print Assumptions binomN_binomZ.
Print Assumptions binomZ_mid.
Print Assumptions binomZ_central.
Print Assumptions wQ_eq.
Print Assumptions wQ_div.
Print Assumptions pscale_spec.
Print Assumptions binlist_spec.
Print Assumptions binlist_len.
Print Assumptions binlist_lead.
Print Assumptions delta_binlist.
Print Assumptions delta_congr.
Print Assumptions delta_psub.
Print Assumptions delta_padd.
Print Assumptions delta_pscale.
Print Assumptions polyQ_firstn.
Print Assumptions sumQn_add.
Print Assumptions sumQn_trunc.
Print Assumptions nth_psub.
Print Assumptions nth_pscale.
Print Assumptions weighted_basis.
Print Assumptions weighted_sum.
Print Assumptions rcoef_even.
Print Assumptions rcoef_odd.
Print Assumptions even_coeffs_sum.
Print Assumptions odd_coeffs_sum_rcoef.
Print Assumptions R_at_one.
Print Assumptions R_at_minus_one_split.
Print Assumptions two_term_at_zero.
Print Assumptions two_term_at_one.
Print Assumptions two_term_at_two.
Print Assumptions R_at_one_card.
Print Assumptions R_deriv_from_card.
Print Assumptions filter_all_gen.
Print Assumptions Ddiag_short.
Print Assumptions sum_i_telescope.
Print Assumptions sum_i_delta.
Print Assumptions alt_row_i.
Print Assumptions collapse_sum_i.
Print Assumptions binQ_one.
Print Assumptions weighted_i_basis.
Print Assumptions weighted_i_sum.
Print Assumptions even_coeffs_weighted.
Print Assumptions odd_coeffs_weighted.
Print Assumptions R_deriv_at_minus_one.
Print Assumptions filter_filter.
Print Assumptions fold_count_zero.
Print Assumptions fold_count_one.
Print Assumptions fold_add_split.
Print Assumptions fold_ext.
Print Assumptions fold_zero.
Print Assumptions length_fibres.
Print Assumptions avoids132b_true.
Print Assumptions NoDup_skipn.
Print Assumptions flatten_perm.
Print Assumptions flatten_firstn.
Print Assumptions flatten_skipn.
Print Assumptions flatten_in_gen.
Print Assumptions flatten_pat.
Print Assumptions flatten_inj.
Print Assumptions Nsig_le_dec.
Print Assumptions Ddiag_partition.
Compute (Nsig 3 2 (0::1::2::nil), Nsig 3 2 (decpat 3)).
Compute suffix_pat 3 (0::3::1::2::nil).
Compute Ddiag 3 0.
Compute card 3.
Compute Ddiag 2 1.
Compute Nsig 2 1 (0::1::nil).
Compute Nsig 2 1 (1::0::nil).
Compute Ddiag 3 0.
Compute Ddiag 2 1.
Compute Ddiag 2 2.
Compute Ddiag 1 3.
Compute (Nsig 2 1 (0::1::nil) + Nsig 2 1 (1::0::nil))%nat.
Compute (Nsig 3 1 (2::1::0::nil)).

(* The decreasing sigma is unconstrained by decreasing_tail_avoids, so its count
   is a free product: choose which d values form the suffix, then any 132-free
   prefix pattern.  Nsig d M dec = Cat(M) * C(M+d, d). *)
Compute (Nsig 2 2 (1::0::nil)).          (* Cat 2 * C(4,2) = 2*6  = 12 *)
Compute (Nsig 3 2 (2::1::0::nil)).       (* Cat 2 * C(5,3) = 2*10 = 20 *)
Compute (Nsig 2 3 (1::0::nil)).          (* Cat 3 * C(5,2) = 5*10 = 50 *)
Compute (Nsig 4 1 (3::2::1::0::nil)).    (* Cat 1 * C(5,4) = 1*5  = 5  *)

(* Ddiag_partition at M = 0 forces p_sigma(0) + q_sigma(0) = 1 for every sigma
   that occurs: N_sigma(0) is 1 when sigma avoids 1324 and 0 otherwise, and the
   partition sums them to card d.  The decreasing sigma puts its whole unit on
   the Catalan term; the fitted data says every other sigma splits it evenly. *)
Compute (Nsig 3 0 (2::1::0::nil)).       (* decreasing, avoids 1324    -> 1 *)
Compute (Nsig 3 0 (0::1::2::nil)).       (* increasing, avoids 1324    -> 1 *)
Compute (Nsig 4 0 (0::2::1::3::nil)).    (* the pattern 1324 itself    -> 0 *)
Compute (Ddiag 4 0, card 4).             (* the partition totals agree      *)

(* d = 2 closes in full: N_10(M) = Cat(M) C(M+2,2) and
   N_01(M) = (C(2M,M) + 4^M)/2, the lower half of row 2M of Pascal. *)
Compute (Nsig 2 2 (0::1::nil)).          (* (C(4,2) + 16)/2 = (6+16)/2  = 11 *)
Compute (Nsig 2 3 (0::1::nil)).          (* (C(6,3) + 64)/2 = (20+64)/2 = 42 *)
Compute (Ddiag 2 3, (50 + 42)%nat).      (* the two pieces total D(2,3) = 92 *)

(* d = 3 in full at M = 2: the six patterns and their total, card 5. *)
Compute (Nsig 3 2 (0::1::2::nil)).       (* 17 *)
Compute (Nsig 3 2 (0::2::1::nil)).       (* 18 *)
Compute (Nsig 3 2 (1::0::2::nil)).       (* 11 *)
Compute (Nsig 3 2 (1::2::0::nil)).       (* 18 *)
Compute (Nsig 3 2 (2::0::1::nil)).       (* 19 *)
Compute (Nsig 3 2 (2::1::0::nil)).       (* 20 *)
Compute (Ddiag 3 2, card 5).             (* (103, 103) *)

(* d = 4 at M = 2, against the closed forms.
   0123: p = 1/2+3M/4, q = 1/2+M/8   -> 2*C(4,2) + (3/4)*16      = 24
   2013: p = 1/2,      q = 1/2       -> 3 + 8                    = 11
   3210: Cat(2)*C(6,4)               -> 2*15                     = 30 *)
Compute (Nsig 4 2 (0::1::2::3::nil)).
Compute (Nsig 4 2 (2::0::1::3::nil)).
Compute (Nsig 4 2 (3::2::1::0::nil)).
Compute (Ddiag 4 2, card 6).

Print Assumptions in_idxs.
Print Assumptions contains132b_spec.
Print Assumptions avoids132b_alt.
Print Assumptions contains213b_spec.
Print Assumptions contains1324b_spec.
Print Assumptions dominoes_spec.
Print Assumptions dominoes_nodup.
Print Assumptions dominoes_locell_132.
Print Assumptions Dcount_fibres.
(* the balanced vertical domino counts, straight from 1324-avoidance:
   the held values are 2, 23, 424, 9751 *)
Compute (Dcount 1 1, Dcount 2 2, Dcount 3 3).
(* at the smallest outer cell d_A is C(b+2,2) + sV, cell by cell and not
   merely on average: 20,19,18,18,17 against 10,9,8,8,7 with C(5,2) = 10 *)
Compute (map (dA 2 3) (gen132 3), map Pstat (gen132 3)).

Print Assumptions locell_is_perm.
Print Assumptions dominoes_locell_gen132.
(* The decreasing lower cell imposes no condition: the domino filter over it is
   exactly "the upper cell avoids 213", so d_A there is the free product
   C(a+b,a) Cat(a). *)
Print Assumptions decpat_dec.
Print Assumptions decpat_avoids_132.
Print Assumptions locell_dec_pos.
Print Assumptions locell_dec_132_pos.
Print Assumptions hicell_213_pos.
Print Assumptions dec_cell_domino.
Print Assumptions dec_cell_iff.
(* d_A(dec, a) against C(a+3,a) Cat(a) at a = 0..3: 1, 4, 20, 100 *)
Compute (map (fun a => (dA a 3 (decpat 3), (binomN (a + 3) a * card132 a)%nat))
             (seq 0 4)).
Print Assumptions Dcount_over_gen132.
Print Assumptions lookup_map_pair.
Print Assumptions dAlook_dAtable.
Print Assumptions strata_cov_ge_within.
Print Assumptions strata_between_nonneg.
Print Assumptions diag_cov_ge_within.
Print Assumptions diag_between_nonneg.
Print Assumptions diag_S_total.
Print Assumptions diag_P_total.
(* the diagonal statistic itself, over the lower cells of Av(132)_3 *)
Compute (map (dA 3 3) (gen132 3)).

Print Assumptions sumAB_map.
Print Assumptions diag_length.
Print Assumptions diag_sumA.
Print Assumptions diag_sumAB.
Print Assumptions diag_totals_agree.
Print Assumptions dA_le_Dcount.
Print Assumptions chebyshev_holds_spec.
Print Assumptions invfibre_gen132.
Print Assumptions pinv_invfibre.
Print Assumptions csum_map_pinv.
Print Assumptions stratum_antisym_zero.
Print Assumptions antisym_zero.
Print Assumptions symp_antip_sq.
Print Assumptions sum_symp_gen.
Print Assumptions sum_sq_gap.
Print Assumptions cov_is_var_gap.
Print Assumptions stratum_hg_identity.
Print Assumptions global_hg_identity.
Print Assumptions cov_nonneg_iff_var_gap.
Print Assumptions diag_var_gap.
Print Assumptions symp_sq_expand.
Print Assumptions antip_sq_expand.
Print Assumptions sum_sq_pinv.
Print Assumptions antip_sq_sum.
Print Assumptions cov_nonneg_iff_spread.
Print Assumptions csum_ones.
Print Assumptions csum_sq_bound.
Print Assumptions spread_le_four_var.
Print Assumptions cov_gives_chebyshev.
Print Assumptions natlook_dAtable.
Print Assumptions nfold_ext_in.
Print Assumptions Tcount_tab_eq.
Print Assumptions foldZ_of_nat.
Print Assumptions Tz_eq.
Print Assumptions chebyshev_holdsZ_eq.
(* T(4,4,4) = 6949612 from the definition of 1324-avoidance, held value.
   Tcount rebuilds the domino list per lookup, Tz tabulates it once and stays
   in Z, since seven million unary constructors exhaust the VM. *)
Compute (Tz 3).
(* The mu-based enumerators, and the four m = 4 statements they carry.  Every
   reduction below routes through them: genf hoists mu out of the inner loop
   and gen132f replaces the O(n^2) safety decider by the O(n) prefix test, and
   the same four statements over gen and gen132 directly do not terminate. *)
Print Assumptions threevals_spec.
Print Assumptions minopt_in.
Print Assumptions minopt_le.
Print Assumptions mub_is_mu.
Print Assumptions mub_none_132free.
Print Assumptions legalf_legalb.
Print Assumptions genf_eq.
Print Assumptions gen132f_eq.
Print Assumptions dominoesf_eq.
Print Assumptions Dcountf_eq.
Print Assumptions dAtablef_eq.
Print Assumptions Tzf_eq.
Print Assumptions chebyshev_holdsZf_eq.
(* Tcount counts pairs of dominoes glued along inverse shared cells, rather
   than being a bare sum.  At m = 2 both sides are 265. *)
Print Assumptions length_filter_prod.
Print Assumptions glued_fold.
Print Assumptions csum_map_ext_in.
Print Assumptions csum_const.
Print Assumptions foldZ_csum.
Print Assumptions Tcount_glued.
Print Assumptions Tz_glued.
Compute (Tcount 2, length (glued 2)).
Print Assumptions domino_4.
Print Assumptions tromino_4.
Print Assumptions chebyshev_upto_4.
Print Assumptions chebyshev_le_4.
Print Assumptions csum_map_of_nat1.
Print Assumptions csum_map_of_nat2.
Print Assumptions straight_chebyshev.
(* the straight tromino total against the staircase one at m = 3:
   sum d_A^2 = 36406 and sum d_A(l) d_A(l^-1) = 36325, so Cauchy-Schwarz gives
   5 * 36406 = 182030 free where the conjecture asks for 5 * 36325 = 181625,
   against D(3,3)^2 = 179776 *)
Compute (Tstraight 3, Tcount 3).
Print Assumptions filter_flat_map.
Print Assumptions firstn_len_app.
Print Assumptions firstn_ext.
Print Assumptions legalb_of_avoids132.
Print Assumptions avoids132b_ext.
Print Assumptions filter_map_ext.
Print Assumptions filter_gen_gen132.
Print Assumptions Ddiag_one.
Print Assumptions card132_recurrence.
Print Assumptions filter_all_false.
Print Assumptions count_ge_in_perm.
Print Assumptions safe_iff_top_prefix.
Print Assumptions safeb_topsplit.
Print Assumptions seq_sub_perm.
Print Assumptions safecount_sccount.
Print Assumptions card132_sccount.
Print Assumptions forallb_false_ex.
Print Assumptions NoDup_firstn.
Print Assumptions topsplit_in_firstn.
Print Assumptions topsplit_ext.
Print Assumptions topsplit_full.
Print Assumptions sccount_ext.
Print Assumptions map_app_ext.
Print Assumptions cntle_filter_seq.
Print Assumptions cntle_splits.
Print Assumptions map_filter_comm.
Print Assumptions children_gen132.
Print Assumptions children_sccounts.
(* the triangle at m = 3: each avoider's split count and its children's *)
Compute (map (fun u => (sccount u 3, map (fun w => sccount w 4) (children u 3)))
             (gen132 3)).
(* The triangle recurrence over the whole class, from the per-word statement:
   each row is the cumulative sum of the one above, and the rows sum to the
   class sizes.  Rows 1..5 are 1; 1,1; 2,2,1; 5,5,3,1; 14,14,9,4,1. *)
Print Assumptions count_eqb_seq_out.
Print Assumptions count_eqb_seq_in.
Print Assumptions length_filter_fold.
Print Assumptions length_filter_eqb_map.
Print Assumptions children_count.
Print Assumptions Ttri_rec.
Print Assumptions Ttri_low.
Print Assumptions filter_le_split.
Print Assumptions Ttri_step.
Print Assumptions filter_ext_gen.
Print Assumptions length_filter_le_gen.
Print Assumptions eqdec_eqb.
Print Assumptions Ttri_row.
Compute (map (fun m => map (fun j => Ttri m j) (seq 2 m)) (seq 1 5)).
Compute (map (fun m => (fold_right (fun j acc => (Ttri m j + acc)%nat) 0%nat
                                   (seq 0 (S (S m))), card132 m))
             (seq 0 6)).
Print Assumptions safecount_rlmax_upto_6.
Print Assumptions card132_rlmax_upto_6.
(* legal insertions into a 132-avoider, against its right-to-left maxima:
   zero mismatches at every size, and the recurrence gives the Catalan numbers *)
Compute (map (fun m => length (filter (fun u => negb (Nat.eqb (safecount u m)
                                                              (S (rlmax u))))
                                      (gen132 m)))
             (seq 0 6)).
Compute (map (fun m => (card132 (S m),
                        fold_right (fun u acc => (S (rlmax u) + acc)%nat)
                                   0%nat (gen132 m)))
             (seq 0 6)).
(* the d = 1 column in closed form: 1, 2, 6, 20, 70, which is (M+1) Cat(M)
   and also C(2M,M), the two-term law at d = 1 with p = 1 and q empty *)
Compute (map (fun M => (Ddiag 1 M, S M * card132 M)) (seq 0 5)).
(* the spread form at the diagonal, m = 3: the antisymmetric second moment, the
   bound the conjecture asks for, and the bound Cauchy-Schwarz gives free.
   810 <= 4508, with 9016 available without any conjecture *)
Compute (let L := gen132 3 in let F := dAz 3 in
         ((Z.of_nat (length L)
           * csum (map (fun b => (antip F b * antip F b)%Z) L))%Z,
          (2 * (Z.of_nat (length L)
                * csum (map (fun b => (F b * F b)%Z) L)
                - csum (map F L) * csum (map F L)))%Z,
          (4 * (Z.of_nat (length L)
                * csum (map (fun b => (F b * F b)%Z) L)
                - csum (map F L) * csum (map F L)))%Z)).
(* the identity at the diagonal, m = 3: four times the covariance form, the
   symmetric term, the antisymmetric term.  7396 = 8206 - 810 *)
Compute (let L := gen132 3 in let F := dAz 3 in
         ((4 * (Z.of_nat (length L)
                * csum (map (fun b => (F b * F (pinv b))%Z) L)
                - csum (map F L) * csum (map F L)))%Z,
          (Z.of_nat (length L)
           * csum (map (fun b => (symp F b * symp F b)%Z) L)
           - csum (map (symp F) L) * csum (map (symp F) L))%Z,
          (Z.of_nat (length L)
           * csum (map (fun b => (antip F b * antip F b)%Z) L))%Z)).
(* the identity at m = 4 for Pstat: four times the covariance form, then the
   symmetric term and the antisymmetric term *)
Compute (let L := gen132 4 in
         ((4 * (Z.of_nat (length L)
                * csum (map (fun b => (Pz b * Pz (pinv b))%Z) L)
                - csum (map Pz L) * csum (map Pz L)))%Z,
          (Z.of_nat (length L)
           * csum (map (fun b => (symp Pz b * symp Pz b)%Z) L)
           - csum (map (symp Pz) L) * csum (map (symp Pz) L))%Z,
          (Z.of_nat (length L)
           * csum (map (fun b => (antip Pz b * antip Pz b)%Z) L))%Z)).
(* the antisymmetric part vanishes on each stratum of Av(132)_4 and globally *)
Compute (map (fun k => csum (map (fun b => (Pz b - Pz (pinv b))%Z)
                                 (invfibre 4 k)))
             (invkeys 4),
         csum (map (fun b => (Pz b - Pz (pinv b))%Z) (gen132 4))).
(* the balanced tromino counts, held as 4, 265, 36325 *)
Compute (Tcount 1, Tcount 2, Tcount 3).
(* the Chebyshev square at m = 3: D(3,3)^2 against Cat(3)*T(3,3,3),
   179776 <= 181625, which is the inequality PQD would supply.  Both products
   are formed in Z; as unary nats they overflow the printer. *)
Compute ((Z.of_nat (Dcount 3 3) * Z.of_nat (Dcount 3 3))%Z,
         (Z.of_nat (card132 3) * Z.of_nat (Tcount 3))%Z).
(* the split at the diagonal, m = 3: total, within, between, scaled by the
   product of the stratum sizes.  -405 + 4103 = 3698, share 405/4103 *)
Compute (let l := dstrata 3 in
         ((nprodz (proj_ns l)
           * (nsumz (proj_ns l) * stP l
              - ssumz (proj_ns l) * ssumz (proj_ns l)))%Z,
          (nsumz (proj_ns l) * defw l)%Z,
          (nsumz (proj_ns l) * qsumz (proj_ns l)
           - nprodz (proj_ns l) * ssumz (proj_ns l) * ssumz (proj_ns l))%Z)).

(* ---- The Catalan count of Av(132), from Segner's convolution alone ---- *)
Print Assumptions nfold_rev_seq.
Print Assumptions card132_0.
Print Assumptions wsum_ext.
Print Assumptions wsum_add.
Print Assumptions wsum_scal.
Print Assumptions wsum_const.
Print Assumptions wsum_rev.
Print Assumptions wsum_S_sym.
Print Assumptions wsum_S_ratio.
Print Assumptions card132_ratio_upto.
Print Assumptions card132_ratio.
Print Assumptions card132_binom.
Print Assumptions Ddiag_one_binom.
Print Assumptions diagonal_one.
(* the ratio, both sides, at every size the enumerator reaches *)
Compute (map (fun m => ((S (S m) * card132 (S m))%nat,
                        (2 * (2 * m + 1) * card132 m)%nat)) (seq 0 6)).
(* the closed count (m+1) card132 m = C(2m,m) *)
Compute (map (fun m => ((S m * card132 m)%nat, binomN (2 * m) m)) (seq 0 8)).
(* the weighted convolution wsum S m = (2m+1) Cat(m) = C(2m+1,m) *)
Compute (map (fun m => (wsum S m, ((2 * m + 1) * card132 m)%nat,
                        binomN (2 * m + 1) m)) (seq 0 6)).
(* the d = 1 diagonal: Ddiag 1 M = C(2M,M), and the coefficient lists it carries *)
Compute (map (fun M => (Ddiag 1 M, binomN (2 * M) M)) (seq 0 5)).
Compute (dp 1 diagonal_one, dq 1 diagonal_one).

(* ---- Av(213) as the other cell class, and the decreasing cell counted ---- *)
Print Assumptions rc_132.
Print Assumptions rc_213.
Print Assumptions rc_avoid_213.
Print Assumptions gen213_spec.
Print Assumptions gen213_nodup.
Print Assumptions card213_card132.
Print Assumptions card213_binom.
Print Assumptions card_succ_mu.
Print Assumptions countt_le.
Print Assumptions countt_map.
Print Assumptions binomN_0.
Print Assumptions bwords_length.
Print Assumptions bwords_spec.
Print Assumptions bwords_nodup.
Print Assumptions mrg_spec.
Print Assumptions mrg_split.
Print Assumptions perm_filter_split.
Print Assumptions negb_leb_ltb.
Print Assumptions length_list_prod.
Print Assumptions NoDup_list_prod.
Print Assumptions decpat_bound.
Print Assumptions decpat_nodup.
Print Assumptions decpat_is_perm.
Print Assumptions contains_213_addc.
Print Assumptions map_sub_add.
Print Assumptions decdom_spec.
Print Assumptions decdom_in_dominoes.
Print Assumptions dec_cell_recover.
Print Assumptions dA_dec.
Print Assumptions dA_dec_catalan.
(* Av(213) is Catalan, cell for cell against Av(132) *)
Compute (map (fun m => (card213 m, card132 m)) (seq 0 6)).
(* masks of length n with a true entries are Pascal's triangle *)
Compute (map (fun n => map (fun a => length (bwords n a)) (seq 0 (S n))) (seq 0 5)).
(* the decreasing cell of d_A at b = 3: 1, 4, 20, 100 against C(a+3,a) Cat(a) *)
Compute (map (fun a => (dA a 3 (decpat 3), (binomN (a + 3) a * card213 a)%nat))
             (seq 0 4)).
(* and at b = 2 and b = 4 *)
Compute (map (fun a => (dA a 2 (decpat 2), (binomN (a + 2) a * card213 a)%nat))
             (seq 0 4)).
Compute (map (fun a => (dA a 4 (decpat 4), (binomN (a + 4) a * card213 a)%nat))
             (seq 0 3)).
(* the branching identity with the fibre count evaluated: card 1 .. card 5 *)
Compute (map (fun m => fold_right (fun u acc => (mucount u m + acc)%nat) 0%nat
                                  (gen m)) (seq 0 5)).

(* ---- Increasing lists, standardisation, and the decreasing suffix fibre ---- *)
Print Assumptions incr_cons_min.
Print Assumptions incr_tl.
Print Assumptions incr_seq.
Print Assumptions incr_filter.
Print Assumptions incr_eq.
Print Assumptions length_filter_lt.
Print Assumptions incr_rank.
Print Assumptions incr_nth_rank.
Print Assumptions rankin_lt_length.
Print Assumptions std_is_perm.
Print Assumptions relab_std.
Print Assumptions relab_inj.
Print Assumptions map_nth_seq.
Print Assumptions skipn_len_app.
Print Assumptions nth_rev_nat.
Print Assumptions rev_decreasing.
Print Assumptions rev_incr.
Print Assumptions is_perm_of_perm_seq.
Print Assumptions perm_seq_of_is_perm.
Print Assumptions relab_perm.
Print Assumptions hiv_lov_perm.
Print Assumptions hiv_length.
Print Assumptions lov_length.
Print Assumptions hiv_incr.
Print Assumptions lov_incr.
Print Assumptions hiv_nodup.
Print Assumptions lov_nodup.
Print Assumptions hiv_bound.
Print Assumptions nth_hiv.
Print Assumptions nth_lov.
Print Assumptions hiv_inj.
Print Assumptions map_nth_defb.
Print Assumptions existsb_eqb_In.
Print Assumptions existsb_eqb_notIn.
Print Assumptions in_firstn_w.
Print Assumptions in_skipn_w.
Print Assumptions in_firstn_or_skipn.
Print Assumptions nodup_firstn_skipn.
Print Assumptions decword_spec.
Print Assumptions decword_recover.
Print Assumptions Nsig_dec.
Print Assumptions Nsig_dec_catalan.
Print Assumptions Nsig_le_free.
Print Assumptions Ddiag_ge_free.
(* N_dec(M) = Cat(M) C(M+d,d), at d = 2 and d = 3 *)
Compute (map (fun M => (Nsig 2 M (decpat 2), (binomN (M + 2) 2 * card132 M)%nat))
             (seq 0 5)).
Compute (map (fun M => (Nsig 3 M (decpat 3), (binomN (M + 3) 3 * card132 M)%nat))
             (seq 0 4)).
Compute (Nsig 4 1 (decpat 4), (binomN 5 4 * card132 1)%nat).

(* ---- Balanced trominoes as gridded permutations of [0,3m) ---- *)
Print Assumptions trominoes_spec.
Print Assumptions trominoes_nodup.
Print Assumptions Trominof_eq.
Print Assumptions tromino_count_1.
Print Assumptions tromino_count_2.
(* the objects themselves, against Tcount *)
Compute (Tromino 0, Tcount 0).
Compute (Tromino 1, Tcount 1).
Compute (Tromino 2, Tcount 2).

(* ---- Standardisation as a class map, and the tromino/glued correspondence ---- *)
Print Assumptions subseq_refl.
Print Assumptions firstn_subseq.
Print Assumptions skipn_subseq.
Print Assumptions subseq_132.
Print Assumptions subseq_1324.
Print Assumptions relab_213.
Print Assumptions relab_1324.
Print Assumptions sortset_incr.
Print Assumptions sortset_nodup.
Print Assumptions sortset_In.
Print Assumptions sortset_perm.
Print Assumptions sortset_length.
Print Assumptions relab_std_set.
Print Assumptions std_132.
Print Assumptions std_213.
Print Assumptions std_1324.
Print Assumptions length_filter_mono.
Print Assumptions rankin_cut.
Print Assumptions cell_split_perm.
Print Assumptions rankin_cut_hi.
Print Assumptions std_cut_test.
Print Assumptions std_locell.
Print Assumptions std_hicell.
Print Assumptions idx_app_in.
Print Assumptions idx_app_notin.
Print Assumptions std_length.
Print Assumptions std_nth_rank.
Print Assumptions idx_of_rank.
Print Assumptions locell_pinv_prefix.
Print Assumptions hicell_pinv_suffix.
Print Assumptions pinv_213.
Print Assumptions pinv_avoids_213.
Print Assumptions tromino_hicell_left.
Print Assumptions tromino_cellsizes.
Print Assumptions tromino_vdomino.
Print Assumptions tromino_locell_split.
Print Assumptions tromino_low_perm.
Print Assumptions tromino_vlocell.
Print Assumptions tromino_hdomino.
Print Assumptions tromino_glue.
Print Assumptions tromino_in_glued.
Print Assumptions tromino_firstn_mem.
Print Assumptions tgpair_inj.
Print Assumptions tromino_le_glued.
Print Assumptions tromino_le_Tcount.
Print Assumptions locell_1324_pos.
Print Assumptions domino_cellsizes.
(* the pair a tromino determines, at m = 2: every one lands in glued *)
Compute (length (glued 2), Tromino 2).

(* ---- The pair-to-tromino construction, closing the correspondence ---- *)
Print Assumptions locell_as_negb.
Print Assumptions rankin_addc.
Print Assumptions std_addc.
Print Assumptions hicell_perm_values.
Print Assumptions hicell_perm_length.
Print Assumptions sortset_hicell.
Print Assumptions relab_seq.
Print Assumptions hicell_std_back.
Print Assumptions mrg_left_spec.
Print Assumptions std_left.
Print Assumptions tromino_of_unfold.
Print Assumptions tromino_of_spec.
Print Assumptions glued_nodup.
Print Assumptions glued_spec.
Print Assumptions glued_le_tromino.
Print Assumptions tromino_eq_Tcount.

(* ---- The decreasing cell maximises d_A: the tight case of PQD ---- *)
Print Assumptions locell_as_negb.
Print Assumptions hicell_perm_length.
Print Assumptions flatlo_spec.
Print Assumptions flatlo_in.
Print Assumptions dA_le_dec.
Print Assumptions dA_le_free.
(* the maximum of d_A on the diagonal, against C(2m,m) Cat(m) *)
Compute (map (fun m => (fold_right (fun l acc => Nat.max (dA m m l) acc) 0%nat
                                   (gen132 m),
                        (binomN (m + m) m * card213 m)%nat)) (seq 1 4)).

(* ---- PQD at a threshold whose up-set is closed under the involution ---- *)
Print Assumptions decpat_pinv.
Print Assumptions filter_ext_in_gen.
Print Assumptions cntA_map_count.
Print Assumptions cntB_map_count.
Print Assumptions cnt2_map_count.
Print Assumptions count_max_bound.
Print Assumptions pqd_diag_closed.
Compute (map (fun b => (pinv (decpat b), decpat b)) (seq 0 4)).

(* ---- uniqueness of the maximiser, and PQD at the top threshold ---- *)
Print Assumptions nth_skipn_nat.
Print Assumptions map_leb_low.
Print Assumptions map_leb_high.
Print Assumptions incr_no_213.
Print Assumptions upvals_no_213.
Print Assumptions upvals_cons.
Print Assumptions insword_length.
Print Assumptions insword_locell.
Print Assumptions insword_hicell.
Print Assumptions insword_mask.
Print Assumptions insword_perm.
Print Assumptions insword_domino.
Print Assumptions insword_nth_lo.
Print Assumptions insword_nth_mid.
Print Assumptions insword_nth_hi.
Print Assumptions insword_nth_top.
Print Assumptions insword_1324.
Print Assumptions insword_rebuild.
Print Assumptions rankin_perm_id.
Print Assumptions std_perm_id.
Print Assumptions perm_no_ascent_dec.
Print Assumptions dec_or_ascent.
Print Assumptions dA_lt_dec.
Print Assumptions dA_dec_pos.
Print Assumptions pqd_diag_top.
Compute (insword 3 0 2 (decpat 3)).
Compute (map (fun l => dA 2 3 l) (gen132 3)).

(* ---- the m = 5 computations ---- *)
Print Assumptions domino_5.
Print Assumptions tromino_count_3.
Print Assumptions tromino_3.
Print Assumptions tromino_5.
Print Assumptions chebyshevZ_upto_5.
Print Assumptions chebyshev_le_5.

(* ---- Targets: the six open statements ---- *)
Print Assumptions two_term_law.
Print Assumptions p_degree_pattern.
Print Assumptions q_degree_pattern.
Print Assumptions R_at_minus_one.
Print Assumptions exponent_law.
Print Assumptions av1324_not_Precursive.

(* ---- the d = 2 diagonal, and the diagonal against its decreasing fibre ---- *)
Print Assumptions perm_two_cases.
Print Assumptions Ddiag_two.
Print Assumptions binomN_one_val.
Print Assumptions binomN_two_val.
Print Assumptions Ddiag_two_closed.
Print Assumptions diagonal_two.
Print Assumptions fold_Nsig_le.
Print Assumptions suffix_pat_in_gen.
Print Assumptions Ddiag_le_dec.
Print Assumptions Ddiag_sandwich.
Compute (map (fun M => (Nsig 2 M [0; 1], (binomN (2 * M) M + 4 ^ M) / 2)%nat)
              (seq 0 5)).
