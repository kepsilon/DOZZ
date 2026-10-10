# Errata and deviations

This document records two things found while formalizing in Lean 4 / Mathlib the proof of the DOZZ
formula by A. Kupiainen, R. Rhodes and V. Vargas, together with the prerequisites it relies on:

1. **Errata** — statements, constants or arguments in the source papers that are incorrect as printed,
   with the corrected version that was formalized (Part I);
2. **Deviations** — places where the Lean statements differ from the papers for reasons other than an
   erratum: scope, conventions, strengthened or reformulated statements, and different proof routes
   (Part II).

Nothing here changes the main result. Every erratum is local: the corrected statement is what the
Lean development proves, and the published conclusions survive. The three main theorems
(`dozz_main`, `dozz_unitVolume`, `dozz_existence`) are proved with no `sorry` and depend only on the
axioms `propext`, `Classical.choice` and `Quot.sound`.

**Sources.**

| Short name | Paper | Version used |
|---|---|---|
| **[KRV]** | A. Kupiainen, R. Rhodes, V. Vargas, *Integrability of Liouville theory: proof of the DOZZ formula*, Ann. of Math. 191 (2020), 81–166 | arXiv:1707.08785, TeX source of the Annals revision |
| **[DKRV]** | F. David, A. Kupiainen, R. Rhodes, V. Vargas, *Liouville quantum gravity on the Riemann sphere*, Comm. Math. Phys. 342 (2016) | arXiv:1410.7318v4; journal version where stated |
| **[KRV-local]** | A. Kupiainen, R. Rhodes, V. Vargas, *Local conformal structure of Liouville quantum gravity*, Comm. Math. Phys. 371 (2019) | arXiv:1512.01802v3; journal version where stated |

Locations are given by section, statement and equation label of the LaTeX source (for example
`(shift1)`), since printed equation numbers differ between versions. Notation follows [KRV]:
0 < γ < 2, Q = γ/2 + 2/γ, μ > 0, l(x) = Γ(x)/Γ(1−x), and s = (Σαᵢ − 2Q)/γ.

**Kinds.** *typo*: a misprint whose intended meaning is clear; *wrong constant/sign*: a formula that
is incorrect as printed; *missing hypothesis*: the statement is false without an extra condition;
*false as stated*: the statement itself is false; *gap*: the conclusion is true but the printed
argument does not prove it.

---

# Part I — Errata

## I.1 Errata in [KRV]

Thirty items. None affects the main theorem `(theoremDOZZ)` or the identification R = R^DOZZ.

### Summary

| # | Location in [KRV] | Kind | Lean statement of the correction |
|---|---|---|---|
| K1 | §BPZ, crossing relation, `(f+)`, `(f-)` | typo | `gauss_connection_minus`, `gauss_connection_plus` |
| K2 | App., Cameron–Martin theorem `(th:Girsanov)` | missing hypothesis | `equatorGFF_cameron_martin(_signed)` |
| K3 | App., corollary `(coroGirs)` | wrong constant | `equatorGFF_rooted_GMC_identity` |
| K4 | Proof of the γ/2 shift, `(estF)` | wrong sign + omitted factor | `poleSubtractedObservable_holomorphic` |
| K5 | End of proof of `(theo4point2overgamma)` | typo (inequality) | `dual_full_fusion_and_asymptotic` |
| K6 | Proof of the 2/γ shift, `(TKEA)` | wrong sign | `reflectionR_dual_shift_unknown_constant` |
| K7 | Proof of Lemma `(lastone)` | wrong constant/sign + gap | `structureConstant_lastone_limit` |
| K8 | §Some identities, parent of `(gammaz)` | wrong sign | `planar_taylor_integral` |
| K9 | §Tail estimate around two insertions | false as stated | `exists_exteriorPinned_markov_uniform` |
| K10 | Proof of `(analytic_hyperbolic)` | false as stated | `differentiableOn_gaussian_charge_moment` |
| K11 | `(sketch:shift1)`, `(shift1)`, `(shiftcoro2)` | wrong constant | `reflectionR_first_shift_meromorphic` |
| K12 | §Derivation of R^DOZZ from C^DOZZ | wrong sign of exponent | `dozzFormula_bridge` |
| K13 | App., proof of Lemma `(defmomR)` | gap (index) | `twoSidedReflectionMass_moment_range` |
| K14 | Same appendix | wrong constant | same |
| K15 | Proof of `(analytic_hyperbolic)`, after `(ymombound)` | typo (min/max) | `unitVolumeNPoint_holomorphic_near_extended_domain` |
| K16 | Proof of `(analytic_hyperbolic)` | typo (empty set) | same |
| K17 | Lemma `(simpletail)` | missing hypothesis | `oneInsertion_tail_uniform` |
| K18 | Proof of Lemma `(lemmaintegral)` | gap | `beta_negative_power_integral` |
| K19 | Proof of `(lemma2int)`, display `(fuck)` | typo | absolute-kernel majorant in the proof of `gammaHalf_twoRooted_Taylor_is_littleO` |
| K20 | Proof of `(fundest)` | typo (false equality) | `twoRooted_time_exponent` |
| K21 | Lemma `(fusion4)` | missing hypothesis | `localized_four_insertion_fusion_case_one/two` |
| K22 | Proof of `(ibo)` | typo (permutations) | not needed: the formal proof does not apply `(fusion4)` in `(ibo)` |
| K23 | Proof of `(theo4point2overgamma)`, `(A2bound2)` | false intermediate bound | `dual_fusion_radial_three_case` |
| K24 | Proof of `(simpletail)`, `(lb1)` | wrong sign + gap | `oneInsertion_tail_uniform` |
| K25 | Proof of `(ibo)` with `(fusion4)` | gap (lemma outside hypotheses) | `localized_four_insertion_fusion_case_one/two` |
| K26 | Proof of `(poleresult)` | wrong constant | `structureConstant_two_pole_expansion` |
| K27 | §BPZ equations, `(Tsolution)`, `(Fundrelation)` | missing hypothesis | `real_gauss_solution_coefficient_ratio` |
| K28 | Lemma `(analy2a)` as used in `(poleresult)` | gap (domain) | `complexMoment_two_tail_residues_of_inverse_moments` |
| K29 | §Proof of analyticity of R̄, `(formulaforbarR)` | wrong constant and sign | `reflectionBarR_holomorphic_representation` |
| K30 | Proposition `(defR1)`, Remark `(unitvolrel)` | missing hypothesis (domain) | `structureConstant_threeToTwo_residue_bridge` |

### Details

**K1 — Duplicated connection power in the hypergeometric basis change.**
§BPZ equations, crossing relation, equations `(f+)` and `(f-)`.
*Printed:* G₊(z) = (1−z)^{1−c′}₂F₁(…; 1−z) already carries the exponent δ = c−a−b, and `(f+)`, `(f-)`
multiply G₊ by (1−z)^{c−a−b} once more.
*Correct:* F₋ = Γ(c)Γ(δ)/(Γ(c−a)Γ(c−b)) G₋ + Γ(c)Γ(−δ)/(Γ(a)Γ(b)) G₊, and similarly for F₊, with no extra
power; the Gamma coefficients are unchanged (counterexample to the print: a = b = 1, c = 5/2; cf. DLMF
15.10.21–22).
*Kind:* typo. *Impact:* none on the connection coefficients or the crossing relation.

**K2 — Cameron–Martin needs joint Gaussianity.**
Appendix, Cameron–Martin theorem `(th:Girsanov)`.
*Printed:* for 𝒳 "some Gaussian variable measurable with respect to the GFF X", E[e^{𝒳−E𝒳²/2}F(X)] =
E[F(X + E[X(·)𝒳])].
*Correct:* 𝒳 must be centered and jointly Gaussian with the field (first chaos). Counterexample to the
print: 𝒳 = Z on {|Z| ≤ a} and −Z otherwise is N(0,1), measurable in X, but has zero covariance shift.
*Kind:* missing hypothesis. *Impact:* none — every application uses linear functionals of the field.

**K3 — Missing γ in the rooted GMC shift.**
Appendix, corollary `(coroGirs)` and its proof.
*Printed:* shift E[X(x)X(u)]. *Correct:* shift γG(u,·), i.e.
E[F(X)∫f dM_γ] = ∫ f(u) E[F(X+γG(u,·))] |u|₊^{−4} d²u.
*Kind:* wrong constant. *Impact:* none — downstream rooted masses already use e^{γ²G}.

**K4 — Reversed Markov threshold and missing time factor.**
Proof of the γ/2 shift equation, estimate `(estF)`.
*Printed:* P(Y_t ≥ e^{−θt})^{1/p} ≤ e^{−θmt/p}(E Y_t^m)^{1/p} ≤ e^{(γ(Q−ε₁−θ)m − m²γ²/2)/p} (the last
exponent lacks t). *Correct:* the threshold factor is e^{+θmt/p} and the bound is
C·exp{−t[(γ(Q−ε₁)−θ)m − γ²m²/2]/p}; the decaying form used afterwards `(estF1)` holds after re-choosing θ
and m small.
*Kind:* wrong sign + omitted factor. *Impact:* none.

**K5 — Reversed slack inequality.**
End of the proof of `(theo4point2overgamma)`.
*Printed:* 4 − γ(2Q−α₁) = 4 − γα₁ − 2γ(Q−α₁) ≤ 4 − γα₁ − 2γη.
*Correct:* for Q−η < α₁ < Q the inequality is strict and reversed (>), which is the direction the
argument needs.
*Kind:* typo. *Impact:* none.

**K6 — Empty limiting region in `(TKEA)`.**
Proof of the 2/γ shift equation.
*Printed:* "α′ = 2/γ + η′ = Q − ε … in the region 0 < η″ < 2η′", with η′ < 0, so the region is empty.
*Correct:* α′ = 2/γ − η′ = Q − ε with ε = γ/2 + η′, and the region is 0 < η″ < −2η′.
*Kind:* wrong sign. *Impact:* none.

**K7 — Critical-mass squeeze in Lemma `(lastone)`.**
Proof of Lemma `(lastone)`, displays `(Thekeyequationagain1)`.
*Printed:* the squeeze is closed using only "E B^p < ∞ ⇒ lim E B^{η″/γ} = 1", and the conclusion is
written lim η″ C_γ(ε+2/γ, γ/2+η″, Q−ε) = 2 lim E A^{η″/γ}, with the wrong structure constant and a positive
prefactor.
*Correct:* the squeeze needs E[(A_h+B_h)^r − A_h^r] → 0, which requires A_h → ∞ in probability plus
uniform integrability; then E A_h^r → 2 and h·C_γ(ε, Q−h, Q−ε) → −4. The lemma's stated value −4 is right.
*Kind:* wrong constant/sign + gap. *Impact:* none on the lemma.

**K8 — Wrong sign of the Taylor counterterm.**
§Some identities, the identity from which `(gammaz)` and `(gammazbarz)` are derived.
*Printed:* numerator |u−z|^{γ²/2} − |u|^{γ²/2} **−** (γ²/4)|u|^{γ²/2}(z/u + z̄/ū); as printed the integral is
not absolutely convergent for any z ≠ 0.
*Correct:* the counterterm sign is **+**. With k = γ²/2 and β = γα₁ the integral converges absolutely
and equals π|z|^{2+k−β}/(l(β/2) l(−k/2) l(2−β/2+k/2)).
*Kind:* wrong sign. *Impact:* none — the differentiated identities and their constants are unchanged.

**K9 — Markov decomposition across the equator pin.**
§Tail estimate around two insertions (argument for `(doubletail)`).
*Printed:* inside B(z₂, 3/2), X = X̃ + 𝒫(X) with X̃ a Dirichlet GFF independent of X outside the ball.
*Correct:* false, because the ball meets the unit circle where the field's average is pinned. The repair
subtracts an average over an auxiliary circle outside both disks: X = Y − L, where Y decomposes
independently and the correlated scalar L is handled by Hölder's inequality.
*Kind:* false as stated (gap). *Impact:* none — the joint-tail and double-tail exponents are unchanged.

**K10 — Finite-radius moments are not entire in the charges.**
Proof of `(analytic_hyperbolic)`.
*Printed:* "F_r is defined for all α ∈ ℂ^N … hence defines an entire function".
*Correct:* F_r is holomorphic only on {−Re s < 4/γ²}; for real charges all equal to −T with T large,
F_r = ∞. Only a neighborhood of the real extended Seiberg domain is needed.
*Kind:* false as stated. *Impact:* none.

**K11 — Wrong l-argument in the first reflection shift.**
`(sketch:shift1)`, `(shift1)` and the corollary `(shiftcoro2)`.
*Printed:* R(α−γ/2) = −μπR(α) / (l(−γ²/4) l(γα/2−γ²/4) l(2 + **γ²/4** − γα/2)); the corollary has
l(2 − γα₁/2).
*Correct:* the last factor is l(2 + **γ²/2** − γα/2), and the corollary's is l(2 + γ²/4 − γα₁/2). The
appendix version `(shift1DOZZ)` and the paper's own residue computation already give the correct factor.
Numerically at γ = 1, μ = 1, α = 2.1: exact ratio −9.28914, corrected formula −9.28914, printed −14.52336.
*Kind:* wrong constant. *Impact:* none — the identification R = R^DOZZ is unaffected.

**K12 — Reversed power of 2/γ in the DOZZ bridge.**
§Derivation of R^DOZZ from C^DOZZ.
*Printed:* the factor (2/γ)^{−2}. *Correct:* (2/γ)^{+2}. The final line, lim ε C^DOZZ(α, ε, α) =
4R^DOZZ(α), is correct.
*Kind:* wrong sign of the exponent. *Impact:* none.

**K13 — Omitted initial interval in the reflection-moment sums.**
Appendix, proof of Lemma `(defmomR)`.
*Printed:* Σ_{n=1}^∞ in the subadditivity and Minkowski bounds for E(∫₀^∞ e^{γ𝓑}Z ds)^p.
*Correct:* Σ_{n=0}^∞, with the block [0,1) bounded separately; at p = 1 the printed bound is too small.
*Kind:* gap. *Impact:* none on the moment conclusions.

**K14 — Missing γ in the infimum bound.**
Same appendix.
*Printed:* e^{−q inf_{[0,1]}(B_s − νs)}. *Correct:* e^{−qγ inf(B_s − νs)}; the printed bound fails for γ > 1.
*Kind:* wrong constant. *Impact:* none.

**K15 — A minimum cannot define a neighborhood of charges.**
Proof of `(analytic_hyperbolic)`, after `(ymombound)`.
*Printed:* "θ > 0 for all **a** with min_k |a_k − a⁰_k| ≤ δ". *Correct:* max_k (a polydisk); with the min,
one coordinate can be moved past Q.
*Kind:* typo. *Impact:* none.

**K16 — Empty annulus in a negative-moment bound.**
Proof of `(analytic_hyperbolic)`.
*Printed:* a bound by C E(∫_{ℂ₁∖ℂ₂} M_γ(d²x))^{−Re s−1}; since ℂ₁ ⊂ ℂ₂ the set is empty and the negative
moment is infinite. *Correct:* use a fixed disk with closure in ℂ₁ away from the insertions.
*Kind:* typo. *Impact:* none.

**K17 — `(simpletail)` needs a positive multiplier.**
Lemma `(simpletail)`.
*Printed:* "for F bounded and C¹ in a neighborhood of z". *Correct:* F real, bounded, ≥ 0, C¹ near z,
with F(z) > 0; for uniform constants F(z) ≥ c₀ on compact parameter sets, and the error exponent strictly
below its ceiling. Counterexample to the print: F ≡ −1.
*Kind:* missing hypothesis. *Impact:* none — all applications use positive multipliers.

**K18 — Endpoint hypergeometric series need not converge.**
Proof of Lemma `(lemmaintegral)`.
*Printed:* the value is obtained through ₂F₁ at z = −1. *Correct:* that series has terms ~k^{p−2} and
diverges for p ≥ 2; integration by parts proves the stated value Γ(1−a)Γ(p+a−1)/Γ(p) for all p > 0,
1 < a < 2.
*Kind:* gap. *Impact:* none.

**K19 — Complex denominator in a nonnegative kernel.**
Proof of `(lemma2int)`, display `(fuck)`.
*Printed:* kernel denominator (x−z)(x′−z) in the expansion of a nonnegative quantity.
*Correct:* |x−z||x′−z|, as in the next display.
*Kind:* typo. *Impact:* none.

**K20 — False equality in a Taylor exponent.**
Proof of `(fundest)`.
*Printed:* γ(Q−α₁) − 2 = γ²/2 − 2 > −1. *Correct:* γ(Q−α₁) − 2 = γ²/2 − γα₁ > γ²/2 − 2 > −1 (equality would
need α₁ = 2/γ, which is excluded).
*Kind:* typo. *Impact:* none.

**K21 — Four-insertion fusion needs γ² > 4/3.**
Lemma `(fusion4)` (the restriction Q < 2γ appears only as a LaTeX comment in the source).
*Printed:* the bounds in both cases under only αᵢ < Q and p > 0.
*Correct:* add Q < 2γ (γ² > 4/3) and keep the parameters in compact sets. Counterexample to the printed
range: γ = 1, charges (0.9, 0.9, 1.8, 2), points (0, ε, −2ε, 10ε), where E I^{−q} ≥ cε^{4.68} contradicts the
printed Cε^{4.805}.
*Kind:* missing hypothesis (false as stated). *Impact:* none — the application has γ² > 2 (see also K25).

**K22 — Wrong point permutations when invoking `(fusion4)`.**
Proof of `(ibo)`, sets A₁ and A₃.
*Printed:* (y₁, y₂, y₃, y₄) = (z, zy′, zy, 0) on A₁ and (zy, z, zy′, 0) on A₃.
*Correct:* (z, zy, zy′, 0) and (zy, zy′, z, 0), with the charges permuted to match; only these satisfy
the lemma's ordering hypothesis.
*Kind:* typo. *Impact:* none.

**K23 — Annular bound misses two cases.**
Proof of `(theo4point2overgamma)`, bound `(A2bound2)`.
*Printed:* C|z|∫_A |x|^{1−γα₁} ≤ C|z|^{1+(1−ξ)(3−γα₁)}.
*Correct:* C|z| if γα₁ < 3, C|z|log(1/|z|) if γα₁ = 3, the printed power if γα₁ > 3. All three are
o(|z|^{4(Q−α₁)/γ}).
*Kind:* false intermediate bound. *Impact:* none on the conclusion.

**K24 — Sign error and wrong comparison in the lower-tail cutoff.**
Proof of `(simpletail)`, estimate `(lb1)`.
*Printed:* from e^{γM} ≥ x^{η′} the text concludes M ≥ −(η′/γ)ln x, and the comparison replaces e^{γM} by
the deterministic e^{γC}.
*Correct:* M ≥ (a/γ) log x > 0, and the comparison variable is S e^{γM} J_c (the Pareto maximum must be
kept).
*Kind:* wrong sign + gap. *Impact:* none on the tail asymptotics.

**K25 — `(fusion4)` applied outside its hypotheses.**
Proof of `(ibo)`, quantity A(y, y′, z).
*Printed:* `(fusion4)` is applied to the local charges (−γ/2, γ, γ, α₁) at order p+2.
*Correct:* there the local Seiberg sum fails (α₁ + γ/2 − 4/γ < 0), so the lemma does not apply even
after K21. The repair is a localized fusion bound valid for any order above an explicit allocation budget.
*Kind:* gap. *Impact:* none — the diagonal bounds survive.

**K26 — Misprinted tail constants in `(poleresult)`.**
Proof of `(poleresult)`, the constants c₁, c₂ obtained from `(analy2a)`.
*Printed:* c₁ = |z₂|^{−4ηQ}|z₂−z₃|^{−2(1+Qη+η²)}R̄(α₂), c₂ = |z₃|^{4ηQ}|z₂−z₃|^{−2(1−Qη+η²)}R̄(α₃); with these the
position dependence does not cancel, although the text says it must.
*Correct:* computing c₁, c₂ from `(simpletail)` with the correct finite-position prefactor, all position
exponents cancel.
*Kind:* wrong constant. *Impact:* none — the residues derived in the paper are correct.

**K27 — One-dimensionality of real solutions needs K₂ ≠ 0.**
§BPZ equations, `(Tsolution)` and `(Fundrelation)`.
*Printed:* under only c, c−a−b ∉ ℤ, the real single-valued C² solutions form a one-dimensional family with
coefficient ratio as in `(Fundrelation)`.
*Correct:* the coefficient relation defines a line only if (K₁, K₂) ≠ (0, 0), and the ratio form needs
K₂ ≠ 0 ([KRV-local] states this condition; it was dropped here). Counterexample: a = 0, b = 1, c ∉ ℤ, where 1
and |z/(1−z)|^{2(1−c)} are both solutions. On the physical parameter range K₂ ≠ 0 holds.
*Kind:* missing hypothesis. *Impact:* none for the physical parameters.

**K28 — `(analy2a)` does not reach the moment domain used in `(poleresult)`.**
Lemma `(analy2a)` (continuation on the strip 0 < Re s < β₃) as applied in `(poleresult)`.
*Printed/used:* the moment order p(ε) = 1 − ε/γ, which is ≤ 0 for γ < 1 and ε ∈ [γ, 1/γ), outside the
lemma's strip.
*Correct:* add a lower-tail input — all inverse moments of Y are finite — which extends E Y^s
meromorphically to Re s < β₃; the residues are unchanged.
*Kind:* gap (domain). *Impact:* none.

**K29 — The constant in `(formulaforbarR)` is +2π/γ, not −π/γ.**
§Proof of analyticity of R̄, the limit before `(formulaforbarR)` and `(formulaforbarR)` itself.
*Printed:* lim_{ε↓γ/2}(ε − γ/2)T̄(α, ε, α) = −4π(Q−α)K/γ², hence R̄(α) = −(π/γ)K C̄(α, γ, α), where
K = l(γα/2 − γ²/4 − 1)/(l(1 + γ(α−Q)/2) l(−γ²/4) l(γ²/4)).
*Correct:* the limit is +8π(Q−α)K/γ², so R̄(α) = +(2π/γ)K C̄(α, γ, α) (the printed value times −2). Since K > 0
on (γ/2, Q) (e.g. K = 0.25 at γ = 1, α = 1.5), the printed formula would make R̄ negative. A 30-digit
evaluation against the DOZZ formula confirms the corrected constant.
*Kind:* wrong constant and sign. *Impact:* confined to this display; analyticity of R̄ and R = R^DOZZ are
unaffected.

**K30 — The three-to-two residue bridge is used outside its stated domain.**
Proposition `(defR1)` and Remark `(unitvolrel)`, as used in §Proof of analyticity of R̄.
*Printed:* the hypothesis γ/2 < α₂ ≤ α₃ < Q; the application takes α₂ = α − γ/2, which is ≤ γ/2 whenever
α ≤ γ.
*Correct:* the bridge holds on the larger domain 0 < α₂ ≤ α₃, γ/2 < α₃ < Q, by the same tail argument.
*Kind:* missing hypothesis (domain). *Impact:* none once the domain is extended.

**Withdrawn.** Two suspected errata were checked and found correct: the appendix formula
`(shift1DOZZ)` (the error is only in the main-text copies, K11), and the use of |z| rather than |z|₊ in the
tail statements (they assume |z| > 2, where the two agree).

**Not an erratum.** The phase-bearing estimate in the proof of `(analytic_hyperbolic)` bounds an absolute
difference of expectations; we did not verify the cancellation it would need, and the formalization uses
only the weaker expectation-of-absolute-difference bound, which suffices.

## I.2 Errata in [DKRV]

None of these affects [KRV]; corrected versions are used where the main proof needs the content.
Line-level locations refer to arXiv:1410.7318v4 unless marked *journal*.

| # | Location | Kind | Correction |
|---|---|---|---|
| D1 | §2, definition of X_g (Poisson problem) | missing hypothesis | Δ_g u = −2πf with ∫u = 0 needs m_g(f) = 0 (or project f); for f = 1 there is no solution. |
| D2 | Round-metric Green function `(hatGformula)` | wrong constant | The constant is ln 2 − ½, not −½ (otherwise the kernel's mean is −ln 2, contradicting the zero-mean pin). Corrected in the journal. |
| D3 | Prop. 2.6 `(law)` | wrong constant | e^{(γ²/2)(θ_ĝ + ln 2)}, not e^{(γ²/2)θ_ĝ + ln 2} (at γ = 0 the print gives 2ĝ d²z). Corrected in the journal. |
| D4 | Zero-mode integral `(int1)` | wrong sign | μ^{−s}, not μ^{+s} (Theorem 3.4 has it right). Kept in the journal. |
| D5 | Heat-kernel cutoff covariance `(def:covWN)` | wrong constant | Lower limit (ε ∨ ε′)², not (ε ∧ ε′)²; prefactor √(2π), not 1/√(2π). Kept in the journal. |
| D6 | Lemma 3.10, proof, first inequality of `(ineqrecursiv)` | gap | Uses (A+B)^p ≤ A^p + B^p for p > 1 (false); Minkowski in L^p is needed. The same display has coordinate typos (|x| for |x−z_j|). The journal's Appendix A repairs it. |
| D7 | Lemma 3.10, "only if" part | gap | The display gives only a non-strict inequality; strictness, and the critical divergence at p = 4/γ², need a separate argument. |
| D8 | `(moments)`, "by Jensen it suffices…" | gap | For 0 < q < 1 Jensen goes the other way (E M_ε^q ≥ E M^q); the cutoff-uniform bound must be proved directly. |
| D9 | End of proof of `(ZREPS1)` | false as stated | t ↦ X̃_t(0) is a time-changed Brownian motion with clock ln(1/ε) + O(1), not exactly Brownian at time −ln t. |
| D10 | Appendix, `(tdpsifinal)` in Lemma `(lem:zarb)` | typo | D_ψ = ¼(m_{g_ψ}φ − m_ĝφ), not (1/4π)(…); the final value used in Thm 3.5 is right. |
| D11 | *Journal*, Lemma A.1 (cited by [KRV] §Tail estimate around two insertions) | typo, false as printed | Weight (|x−z|+ε)^{−γα}, not (|x−z|+ε)^{−α}. |
| D12 | *Journal*, Lemma A.1, (A.2) | typo, false as printed | Integrate over B(z, r), not B(z, 1) (the left side does not depend on r). |
| D13 | Proof of Lemma `(exist)` | gap + typo | Convergence of negative moments needs uniform integrability; the Schwarz step gives r^{β/2}, not r^β. |
| D14 | Killed-correlation argument `(momentq1)` | gap | A supremum event is used where an infimum is needed. |
| D15 | Proof of Prop. 2.6 | gap | The extension from local convergence to bounded global test functions is not given. |
| D16 | Appendix, proof of `(Grule)` | gap (minor) | Divides by c; the affine case c = 0 is not covered. |
| D17 | Proof of Lemma 3.10 (and journal Lemma A.1) | other (minor) | Exact scaling of the ln₊ 1/|x−y| field is asserted on the unit disk; it holds only on disks of diameter < 1. |

## I.3 Errata in [KRV-local]

Locations refer to arXiv:1512.01802v3; "kept in the journal" means the published version has the same text.

| # | Location | Kind | Correction |
|---|---|---|---|
| L1 | Lemma 4.4 `(lemmaPDEsbis)` | missing hypothesis, false as stated | "Every solution" must be "every real-valued single-valued C² solution": for a = 0, b = 1/4, c = 1/2 every z̄ⁿ solves the equation, so the solution space is infinite-dimensional. Kept in the journal. |
| L2 | Appendix, proof of Lemma 4.4 | typo | Mixed solutions need complex conjugates, F₋·conj(F₊), not F₋F₊ (in general L_z(F₋F₊) ≠ 0). Kept in the journal. |
| L3 | Paragraph after Lemma `(asyex)` | typo | c − a − b = γ(Q − α₂)/2, not ½(1 − α₃); the continuity argument must vary α₂. Kept in the journal. |
| L4 | `(funamental)` | wrong constant | e^{γΣα_k G(x, z_k)}, not e^{Σα_k G(x, z_k)}. |
| L5 | Appendix, "at most four dimensional" | wrong sign | −½v₀′ − ½Pv₀ = 0, not −½v₀′ + Pv₀ = 0. |
| L6 | Proof of Lemma 4.5 `(asyex)`, collision limit | typo | R_t(re^{iθ}, rv), not R_t(re^{iθ}, v/r). |
| L7 | Proof of Lemma 4.5, `(ineqT2)` | gap | The remainder bound ∫|m_z(u)|1_{|u|≥½}du ≤ C|z| fails when γα₂ ≥ 2 (the integrand is not integrable near u = 1); e.g. γ = 1, α = (1.9, 2.2, 2.2). A reverse Cameron–Martin bound repairs it; a Fubini step is also unjustified. |
| L8 | Lemma `(decompmeas)` | wrong constant | The radial chaos factor is ĝ^{1+γ²/4}, not ĝ. Kept in the journal. |
| L9 | Normalization of the radial decomposition | wrong constant | No leftover mollifier factor A^{γ²/2}: it cancels against the variance asymptotics. Kept in the journal. |
| L10 | `(def:Kepsilon)` | false as stated | The sum must be over i < j: the printed sum includes diagonal terms and diverges (order ε^{−12} for γ = 1, N = 3, αᵢ = 2). Kept in the journal. |
| L11 | Definition of H̃ and `(def:Hepsilon)` | wrong sign, false as stated | The function claimed bounded is unbounded (it grows like 2 ln|x|); the bounded function is ln|x|₊ + ¼ ln ĝ. Kept in the journal. |
| L12 | `(barB)`, `(remindderiv)` | wrong constant | Prefactor γ/2, not γ/(2π); the first term of `(remindderiv)` is missing its correlation factor. |
| L13 | Lemma `(corner)` | false as stated | The four rates fail as r ↓ 0; they hold for r ≥ 1 (terminal rates r ≥ 2) with a separate short-time bound. |
| L14 | Proof of Lemma `(appliBPZ2)` | gap | The case split covers γ² ≥ 8/3 and γ² < 2 and misses 2 ≤ γ² < 8/3. |
| L15 | Props. `(holdercorrel)`, `(holdercorrelbis)` and proof | gap | A |log ε| case at γ² = 2 is missed, a division by γ is missing in s, the proof moves the degenerate point instead of the screening point, and the dual case is only "similar". |
| L16 | arXiv proof of C² regularity | gap | Only ∂_{z_i}∂_{z_j} is computed; real C² also needs the mixed derivatives. Added in the journal. |

Several further proof steps in [KRV-local] are terse rather than wrong (hypoellipticity and Cauchy
uniqueness without a regularity class; continuity across the cut; the BPZ equation for the −2/γ charge "by
analogy"; repeated "similar" steps in the differentiation lemma; constant dependence in `(corner)`). All
were supplied in full for the formalization. The Beurling lemma, placed after `\end{document}`, and the
second Ward identity, also only sketched, are not needed for the DOZZ formula (see V25 and V5).

## I.4 External literature

No erratum was found in the other cited sources (Kahane convexity, Berestycki's GMC construction, Doob's
h-transform, DLMF), all of which were proved in Lean or found in Mathlib.

---

# Part II — Differences between the Lean formalization and the papers

## II.1 The main theorems

The main theorem of [KRV] (`theoremDOZZ`): for γ ∈ (0, 2), μ > 0 and charges α₁, α₂, α₃ satisfying the extended
Seiberg bounds, C_γ(α₁, α₂, α₃) = C_γ^DOZZ(α₁, α₂, α₃). The Lean counterpart:

```lean
theorem dozz_main (γ μ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (α₁ α₂ α₃ : ℝ) (hα : ExtendedSeiberg3 γ α₁ α₂ α₃)
    (hs : ∀ n : ℕ, sExp γ α₁ α₂ α₃ ≠ -(n : ℝ))
    (U : ℂ → ℂ) (hU : IsUpsilon γ U)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    (structureConstant P M γ μ α₁ α₂ α₃ : ℂ) = dozzFormula γ μ U α₁ α₂ α₃
```

together with `dozz_unitVolume` (the unit-volume constant as a limit, valid at every point including the
poles) and `dozz_existence` (models of the hypotheses exist). The differences:

**V1 — C_γ is the GMC moment formula.** [KRV] defines correlations as limits of regularized vertex
operators in the Liouville path integral (§2, `(lcorre)`, `(Vdefi)`) and derives the moment formula
`(expression3pointstruct)`. In Lean, `structureConstant` *is* that formula,
2μ^{−s}γ^{−1}Γ(s)·E[ρ^{−s}], and the path-integral definition is not formalized. A bridge to the
correlation limit `(Climit)` (`structureConstant_infinity_limit`) is proved for s > 0. *Effect:* the theorem
is about the probabilistic expression that the paper's proof works with; its identification with the
regularized path integral ([DKRV] Thms 3.2, 3.4) is outside the formalization.

**V2 — Poles.** The paper sets correlations equal to ∞ when s ∈ −ℕ. `dozz_main` instead assumes
s ∉ {0, −1, −2, …} (the hypothesis also excludes s = 0, where Γ(s) has a pole; the unit-volume constant remains finite there), and `dozz_unitVolume`
covers every point, poles included, as a limit of μ^s C^DOZZ/Γ(s). *Effect:* none on the content.

**V3 — Objects are characterized, not constructed.** The theorems quantify over every probability
space and every field X and chaos M satisfying the predicates `IsEquatorGFF` and `IsGMCOf`, and over every
function U satisfying `IsUpsilon`; existence of such objects is the separate theorem `dozz_existence`, and
the joint law of (X, M) is shown to be model-independent. *Effect:* formally stronger, same content.

**V4 — Real-valued, totalized arithmetic.** Lean's Γ is 0 at its poles, x/0 = 0, an infinite integral
converts to the real number 0, and μ^{−s} is a real power. Each such convention was checked to be harmless
on the theorem's domain (for example, an infinite moment would give 0 on the left while the DOZZ formula is
nonzero there, so the identity would be false rather than vacuous).

## II.2 Scope

**V5 — Ward identities are not formalized.** [KRV-local]'s Ward identities and stress-tensor theory are
not needed: the BPZ equation is proved directly by Gaussian integration by parts (the route of
[KRV-local] §§4–5, regularized as in V25). The regularity and kernel bounds that BPZ needs are formalized.

**V6 — Parts of [DKRV] not formalized.** Smooth-metric Liouville theory and the Weyl anomaly, the law of
the Liouville field, the regime γ ≥ 2, and the conjectures. The normalization on the round sphere is
transported to the equator-pinned field by a direct argument instead of the Weyl anomaly.

**V7 — Remarks and motivation.** The conformal bootstrap and AGT discussion, the formal reflection
relation V_α = R V_{2Q−α}, smooth dependence on γ (the paper notes it is not needed; continuity in γ is
proved), and several statements not used by the corrected proof (continuum FKG, the second SDE comparison
lemma, [KRV-local] Lemma `(corner)`) are not formalized.

## II.3 Definitions and modelling choices

**V8 — The field.** X is a random Mathlib distribution `𝓓′(ℂ, ℝ)` (test functions C^∞ with compact
support) rather than a tempered one; only its evaluations X(f) are required to be measurable. The
Cameron–Martin theorem on 𝒮′ is replaced by finite-dimensional Gaussian tilts extended by a monotone-class
argument.

**V9 — Circle averages and GMC.** The circle average is characterized as an L² limit of test-function
evaluations, and the GMC as the limit in probability, against every bounded continuous test function, of
the circle-average chaos with the exact variance; the predicate `IsGMCOf` contains the existence of a
circle average. The concrete model behind `dozz_existence` is built from white noise on a scale space (an
isonormal construction with a log-correlated field), not from Minlos' theorem; GMC existence and
uniqueness follow Berestycki's good-point argument, with uniqueness across admissible regularizations.

**V10 — Υ and ₂F₁ by characterizing predicates.** `IsUpsilon γ U` says U is entire and equals the
integral formula on the strip 0 < Re z < Q; uniqueness is the identity theorem. Υ is constructed from
Malmsten's formula for log Γ and the shift equations, without double-gamma functions. Gauss's
hypergeometric function is characterized the same way (holomorphic on the cut plane and equal to its
series on the unit disk).

**V11 — Brownian objects without stochastic calculus.** Brownian motion conditioned to stay negative is
defined by its entrance and transition densities (including zero drift, a Bessel-3 law), Williams'
decomposition is proved by conditioning on thin bands, SDE comparison is replaced by quantile couplings, and
Wiener measure is obtained from circle averages of the concrete field. No stochastic integration is used.

**V12 — R̄ and R take their probabilistic data as arguments.** The reflection coefficients are defined
for any admissible pair (two-sided conditioned Brownian motion, independent lateral chaos), and separate
theorems show that the value does not depend on the choice.

**V13 — Lateral chaos.** The paper's Z_s = ∫e^{γY}dθ is formalized as a random measure on ℝ, the
pushforward of the planar chaos by −log|x|, characterized by invariance in law and its intensity. No density
is asserted (it may fail to exist for γ ≥ √2).

## II.4 Statement-level differences

These are reformulations made because of Lean conventions or to make a "for η small enough" explicit.
None changes the mathematical content.

**V14 — Meromorphic identities on a generic set.** Identities stated in the papers "for all α ∈ ℂ" between
meromorphic functions (shift equations of C^DOZZ and R^DOZZ, reflection, the three-to-two bridge) are
stated for all α₁ outside a discrete set, with Lean's total functions. Values at poles or at α = Q (for
example R^DOZZ(Q) = −1, R(Q) = −1, R̄(Q) = 1) are stated as punctured or one-sided limits.

**V15 — Extra conditions forced by Γ's convention.** The Υ shift equations exclude the points where
Γ(γz/2) or Γ(2z/γ) has a pole; the dual shift equations of C^DOZZ and R^DOZZ assume 4/γ² ∉ ℕ. Without these
the Lean statements are false because both sides take conventional values. The main theorem is unaffected
(it is first proved for γ² ∉ ℚ and extended by continuity).

**V16 — Theorem `(Rtheor)` off its poles.** R(α) = R^DOZZ(α) is stated off the points 2/γ − nγ/2, where
the paper's own definition of R is not available, with a companion limit statement at those points.

**V17 — "η small enough" made explicit.** Statements of the form "for η sufficiently small" are stated
on explicit parameter windows (two-pole expansion, near-Q slices, crossing, fusion), and "constants depend
on the parameters" is strengthened to uniformity over compact parameter sets.

**V18 — Strengthened intermediate statements.** Many lemmas are proved in more general form than
printed: the Cameron–Martin and rooted identities for measurable functionals; Kahane's inequality for all
convex or concave functions; GMC moment ranges as two-sided "iff" statements, including negative orders and
the 4/γ² cap; Möbius covariance and symmetry of the moment formula on the extended Seiberg domain,
including s ≤ 0; and joint continuity in (γ, α).

**V19 — The irrationality of γ².** The paper assumes γ² ∉ ℚ throughout its last sections. In Lean it is
kept where needed (the dual shift with unknown constant, the quotient argument, the residual factor) and
dropped where the argument does not use it.

## II.5 Proof routes that differ from the papers

**V20 — Continuity in γ.** The paper proves the theorem for γ² ∉ ℚ and states that "the general case
follows by continuity". Lean carries this out: it builds GMCs for all γ on one field, proves continuity in γ
of both sides, and concludes by density of irrational γ².

**V21 — The quotient argument without comparing zeros.** The paper concludes that C/C^DOZZ is holomorphic
"since C and C^DOZZ have the same simple poles and zeros", which relies on the zeros of Υ being simple and is
not proved there. Lean instead shows that a meromorphic function on a strip with two periods of irrational
ratio is constant and pole-free, so no comparison of divisors is needed. (Simplicity of the zeros of Υ for
γ² ∉ ℚ and the reflection relation of C^DOZZ are still proved, as standalone results.)

**V22 — Normalization at the zero mode.** The paper fixes the remaining constant by the three-to-two
bridge and Lemma `(defR)`. Lean calibrates it at the point s = 0, where the unit-volume constant equals 2/γ
and the zero of Υ at 0 cancels the pole of Γ(s).

**V23 — No circular use of the dual shift.** The general dual-shift statement on the strip is proved
using the main theorem itself; the proof of the main theorem uses only its first case (η ≤ γ/4), which is
proved independently.

**V24 — Other substitutions.** A rooted fixed-disk bound replaces continuum FKG; the hypergeometric
classification uses a Hermitian/monodromy construction; and the Markov decomposition of the field uses an
auxiliary exterior pin (the repair of K9).

**V25 — No Beurling transform and no strong Markov property.** [KRV-local] derives the BPZ equation from an
exact Gaussian integration-by-parts identity, whose singular terms are controlled by the Beurling transform
(Beurling's estimate for the Cauchy transform, with Calderón–Zygmund theory in Lᵖ). Lean derives it from
regularized Ward-type identities instead: Gaussian integration by parts against the vector field
x(x − 1)/(z − x) multiplied by smooth cutoffs that vanish near 0, 1, z and ∞, followed by removal of the
cutoffs by dominated convergence. The Beurling transform is not used. Nor is the strong Markov property of
the conditioned process: at last-exit times, which are not stopping times, an initial-block argument
replaces it.
