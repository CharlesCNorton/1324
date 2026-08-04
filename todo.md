1. Construct Diagonal d for every d ≥ 2. Present unconditionally at d = 1, 2, 3, and at d = 4 modulo item 7.
2. Prove p_degree_pattern: for each j exhibit a degree-4j polynomial c with d!·p_{d,d-1-j} = c(d) for all d > j. Holds at j = 0, d = 2 (p_lead_two_poly).
3. Prove q_degree_pattern: for each j exhibit a degree-(2+4j) polynomial c with d!·q_{d,d-2-j} = c(d) for all d > j+1. Holds at j = 0, d = 2 (q_lead_two).
4. Prove R_at_minus_one: p_d(0) − q_d(0) = 1 for d ≥ 1. Holds at d = 1 and d = 2; the fibrewise route fibres_at_minus_one reduces it to every non-decreasing suffix pattern splitting its unit evenly.
5. Prove exponent_law: for each t exhibit C and k with |[s^t] R_d| ≤ C·d^k whenever t ≤ 2d−2. Holds at t = 0 given the leading coefficient.
6. Prove av1324_not_Precursive: the counting sequence satisfies no nontrivial linear recurrence with polynomial coefficients. Open in the literature; only numerical evidence from Conway, Guttmann and Zinn-Justin.
7. Prove DDIAG_FOUR_CLOSED: 24·Ddiag 4 M = (M³+35M²+216M+288)·C(2M,M) + (6M²+78M+264)·4^M. Reduced by Ddiag_four_stats to items 10 through 14.
8. Prove PQD_statement: positive quadrant dependence for the pairs (Pstat b, Pstat (pinv b)) over Av(132)_m. Unconditional at the top threshold (pqd_diag_top).
9. Prove DIAG_COV: the covariance of d_A against its transpose is non-negative. Implied by item 8 and strictly weaker than it; gives the Chebyshev square for all m, currently verified only to m = 5.
10. Prove the third moment of the state function: 32·Hcubetot M = 8(M⁴−M³+M²−3M−2)·Cat(M) + (15M²−15M+16)·4^M. Fitted exactly against M = 0..10, proof route is the max-split expansion one degree above Hsqtot_expand.
11. Close CCtot. Already reduced to item 10 by CCtot_kCtot and kCtot_Hcubetot, with sqsum2_val, Ctot_closed and Awptot_closed supplying the rest.
12. Close DDtot, the level total of the clipped H between two nodes.
13. Close EEtot, the level total of the clipped H over the interval above a node.
14. Close PCtot, the level total of Cin weighted by subtree size. This one I had previously reported as done; it is not, and it appears in Ddiag_four_stats alongside the other three.
