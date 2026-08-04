1. Construct Diagonal d for every d ≥ 2. Present unconditionally at d = 1, 2, 3, and at d = 4 modulo item 7.
2. Prove p_degree_pattern: for each j exhibit a degree-4j polynomial c with d!·p_{d,d-1-j} = c(d) for all d > j. Holds at j = 0, d = 2 (p_lead_two_poly).
3. Prove q_degree_pattern: for each j exhibit a degree-(2+4j) polynomial c with d!·q_{d,d-2-j} = c(d) for all d > j+1. Holds at j = 0, d = 2 (q_lead_two).
4. Prove R_at_minus_one: p_d(0) − q_d(0) = 1 for d ≥ 1. Holds at d = 1 and d = 2; the fibrewise route fibres_at_minus_one reduces it to every non-decreasing suffix pattern splitting its unit evenly.
5. Prove exponent_law: for each t exhibit C and k with |[s^t] R_d| ≤ C·d^k whenever t ≤ 2d−2. Holds at t = 0 given the leading coefficient.
6. Prove av1324_not_Precursive: the counting sequence satisfies no nontrivial linear recurrence with polynomial coefficients. Open in the literature; only numerical evidence from Conway, Guttmann and Zinn-Justin.
7. Prove DDIAG_FOUR_CLOSED: 24·Ddiag 4 M = (M³+35M²+216M+288)·C(2M,M) + (6M²+78M+264)·4^M. Reduced by Ddiag_four_stats to items 10 through 12.
8. Prove PQD_statement: positive quadrant dependence for the pairs (Pstat b, Pstat (pinv b)) over Av(132)_m. Unconditional at the top threshold (pqd_diag_top).
9. Prove DIAG_COV: the covariance of d_A against its transpose is non-negative. Implied by item 8 and strictly weaker than it; gives the Chebyshev square for all m, currently verified only to m = 5.
10. Close Bsqwptot, the level total of the second moment of H over a subtree: 96·Bsqwptot M + (48+56M)·C(2M,M) + 15M·4^M = 56M²·C(2M,M) + (48+15M²)·4^M. The max-split chain through Bsqwp_midmax is in place; the level sum and its induction remain. This closes DDtot, the level total of the clipped H between two nodes, through 2·DDtot = (2M+1)·Bwptot − Bsqwptot − 2·Astri, with Astri supplied by Hcubetot_closed and Awptot_closed.
11. Close the level total of H weighted by the subtree sum, Σ_y H_y·Bin(y). With item 10 this closes EEtot, the level total of the clipped H over the interval above a node.
12. Close the level total of H weighted by the clipped prefix sum, Σ_y H_y·Cin(y). With Ctot_closed and kCtot this closes PCtot, the level total of Cin weighted by subtree size.
