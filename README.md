# The DOZZ formula, formalized in Lean 4

[![Build](https://github.com/scottnarmstrong/DOZZ/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/DOZZ/actions/workflows/build.yml)
[![Comparator](https://github.com/scottnarmstrong/DOZZ/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/DOZZ/actions/workflows/comparator.yml)

A **Lean 4 / Mathlib** formalization of the theorem of Kupiainen, Rhodes and Vargas that the
three-point structure constants of Liouville conformal field theory on the Riemann sphere, defined
probabilistically through the Gaussian free field and Gaussian multiplicative chaos, are given by the
formula conjectured by Dorn and Otto and by Zamolodchikov and Zamolodchikov:

```math
C_\gamma(\alpha_1,\alpha_2,\alpha_3)=\Bigl(\pi\mu\,l\bigl(\tfrac{\gamma^2}{4}\bigr)\bigl(\tfrac{\gamma}{2}\bigr)^{2-\gamma^2/2}\Bigr)^{\frac{2Q-\bar\alpha}{\gamma}}
\frac{\Upsilon'_{\frac\gamma2}(0)\,\Upsilon_{\frac\gamma2}(\alpha_1)\,\Upsilon_{\frac\gamma2}(\alpha_2)\,\Upsilon_{\frac\gamma2}(\alpha_3)}
{\Upsilon_{\frac\gamma2}\bigl(\frac{\bar\alpha-2Q}{2}\bigr)\,\Upsilon_{\frac\gamma2}\bigl(\frac{\bar\alpha}{2}-\alpha_1\bigr)\,\Upsilon_{\frac\gamma2}\bigl(\frac{\bar\alpha}{2}-\alpha_2\bigr)\,\Upsilon_{\frac\gamma2}\bigl(\frac{\bar\alpha}{2}-\alpha_3\bigr)},
```

where $`0\lt\gamma\lt2`$, $`Q=\frac\gamma2+\frac2\gamma`$, $`\mu\gt0`$, $`\bar\alpha=\alpha_1+\alpha_2+\alpha_3`$,
$`l(x)=\Gamma(x)/\Gamma(1-x)`$ and $`\Upsilon_{\gamma/2}`$ is the entire function of Zamolodchikov and
Zamolodchikov. The main results are:

- **The DOZZ formula.** For every $`0\lt\gamma\lt2`$, $`\mu\gt0`$ and real charges satisfying the
  extended Seiberg bounds, the probabilistic structure constant equals the DOZZ formula
  ([KRV, Theorem 2.4]). A companion theorem covers every point of the domain, including the poles of
  $`\Gamma(s)`$, through the unit-volume structure constant.
- **The reflection coefficient.** The probabilistic reflection coefficient, built from Brownian motion
  conditioned to stay negative and the lateral chaos measure, equals the formula $`R^{\mathrm{DOZZ}}`$ of
  Zamolodchikov and Zamolodchikov ([KRV, Theorem 3.5]).
- **Existence.** For every $`0\lt\gamma\lt2`$ the Gaussian free field pinned on the equator, its
  Gaussian multiplicative chaos, and the function $`\Upsilon_{\gamma/2}`$ exist, so the theorems are not
  vacuous; the chaos is almost surely unique and its joint law with the field does not depend on the
  model.
- **Prerequisites.** The results of [DKRV] and [KRV-local] that the proof uses, among them the
  construction and moment theory of the chaos, the extended Seiberg bounds, the BPZ differential
  equations for degenerate four-point functions, and the classification of their real single-valued
  solutions by the Gauss hypergeometric function.

The library contains no `sorry`, and every result uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Results formalized

The following lists the results covered from each paper. The detailed formulations and Lean
declarations appear below.

- **Antti Kupiainen, Rémi Rhodes and Vincent Vargas, “Integrability of Liouville theory: proof of the
  DOZZ formula”, Annals of Mathematics 191 (2020), 81–166** ([DOI](https://doi.org/10.4007/annals.2020.191.1.2);
  [arXiv:1707.08785](https://arxiv.org/abs/1707.08785)), cited as [KRV]. Numbering refers to the arXiv
  version.

  - Theorem 2.4, the DOZZ formula, on the full extended Seiberg domain; Theorem 3.5, the formula for
    the reflection coefficient.
  - The intermediate results of Sections 3 and 6–12, each as a separate Lean statement: analytic
    continuation of the correlation functions (Theorem 6.1), the tail estimates for multiplicative
    chaos (Lemmas 7.1 and 7.3), the reflection coefficient and its moments (Lemmas 3.3–3.4,
    Proposition 8.1), the BPZ equations and the shift equations (Sections 9–11), and the appendix on
    Gaussian tilts, fusion estimates and integral identities (Section 12).
  - Thirty errata are corrected; see [Errata and deviations](#errata-and-deviations).

- **François David, Antti Kupiainen, Rémi Rhodes and Vincent Vargas, “Liouville quantum gravity on the
  Riemann sphere”, Communications in Mathematical Physics 342 (2016), 869–907**
  ([DOI](https://doi.org/10.1007/s00220-016-2572-4); [arXiv:1410.7318](https://arxiv.org/abs/1410.7318)),
  cited as [DKRV].

  - The construction of the chaos measure and its moment theory, the extended Seiberg bounds for the
    finiteness of correlation moments (Lemma 3.10), and Möbius covariance, for the
    equator-pinned field used in [KRV]. The Liouville field on a general metric, the Weyl anomaly and the
    regime $`\gamma\ge2`$ are not formalized.

- **Antti Kupiainen, Rémi Rhodes and Vincent Vargas, “Local conformal structure of Liouville quantum
  gravity”, Communications in Mathematical Physics 371 (2019), 1005–1069**
  ([DOI](https://doi.org/10.1007/s00220-018-3260-3); [arXiv:1512.01802](https://arxiv.org/abs/1512.01802)),
  cited as [KRV-local].

  - The BPZ equations for the four-point function with a degenerate insertion of charge
    $`-\gamma/2`$ or $`-2/\gamma`$, proved by Gaussian integration by parts together with the regularity
    of correlation functions; the classification of real single-valued solutions of the hypergeometric
    equation (Lemma 4.4, corrected) and the restricted fusion asymptotics (Lemma 4.5). The Ward
    identities and the stress-energy tensor are not formalized; the DOZZ proof does not need them.

## Sources

The proofs also draw on the following results; each was proved in the formalization or found in Mathlib.

- Nathanaël Berestycki, *An elementary approach to Gaussian multiplicative chaos*, Electronic
  Communications in Probability **22** (2017), paper 27 ([arXiv:1506.09113](https://arxiv.org/abs/1506.09113); [DOI](https://doi.org/10.1214/17-ECP58)).
  The good-point argument for existence and uniqueness of the chaos.
- Rémi Rhodes and Vincent Vargas, *Gaussian multiplicative chaos and applications: a review*,
  Probability Surveys **11** (2014), 315–392 ([arXiv:1305.6221](https://arxiv.org/abs/1305.6221); [DOI](https://doi.org/10.1214/13-PS218)).
  Kahane's convexity inequality and moment bounds.
- David Williams, *Path decomposition and continuity of local time for one-dimensional diffusions, I*,
  Proceedings of the London Mathematical Society **28** (1974), 738–768, and L. C. G. Rogers and J. W.
  Pitman, *Markov functions*, Annals of Probability **9** (1981), 573–582. The path decomposition of
  Brownian motion with drift at its maximum, and conditioned Brownian motion as the norm of a drifted
  three-dimensional Brownian motion.
- NIST Digital Library of Mathematical Functions, §§15.2–15.10 (Gauss hypergeometric function and its
  connection formulas) and Malmsten's integral for $`\log\Gamma`$ (§5.9).
- Rémy Degenne and collaborators, *Brownian motion in Lean*
  ([github.com/RemyDegenne/brownian-motion](https://github.com/RemyDegenne/brownian-motion), Apache 2.0).
  The Kolmogorov–Chentsov continuity theorem is adapted from this project, with its copyright notices.

The proofs follow [KRV]. Where [KRV], [DKRV] or [KRV-local] omit steps, the arguments are supplied in
the formalization.

## Errata and deviations

[`docs/ERRATA-AND-DEVIATIONS.md`](docs/ERRATA-AND-DEVIATIONS.md) lists, with locations and the
corrected statements that the Lean code proves:

- **errata**: 30 in [KRV], 17 in [DKRV] and 16 in [KRV-local], among them wrong constants (for example
  the coefficient $`+2\pi/\gamma`$ rather than $`-\pi/\gamma`$ in the formula for $`\bar R`$, and the last
  factor of the first reflection shift), statements that need an extra hypothesis (four-insertion
  fusion needs $`\gamma^2\gt4/3`$; the classification of real hypergeometric solutions needs real-valued
  solutions and a nonvanishing coefficient) and gaps in arguments. None of them affects the main
  theorems;
- **deviations**: the places where the Lean statements differ from the papers — scope, conventions
  forced by Mathlib's total functions, explicit parameter windows in place of "small enough", and the
  points where the formal proof takes a different route (for example, the quotient argument of
  [KRV, Section 11] is completed without comparing zeros, which the paper leaves unproved).

## Liouville correlation functions

The field and its chaos are characterized by their laws, so every theorem holds for every model; the
existence theorem below shows that models exist.

**The field.** Test functions are smooth compactly supported functions $`\mathbb C\to\mathbb R`$, and a
field is a random real distribution on $`\mathbb C`$ (Mathlib's `𝓓'`). The equator-pinned Gaussian free
field `IsEquatorGFF P X` is a field whose evaluation $`X(f)`$ at every test function is measurable and
centered Gaussian with variance

```math
\iint f(x)\,G(x,y)\,f(y)\,dx\,dy,\qquad G(x,y)=\log\frac1{|x-y|}+\log|x|_++\log|y|_+,\qquad |x|_+=\max(1,|x|).
```

**Circle averages and chaos.** A circle-average process `IsCircleAverage P X Xc` is jointly measurable,
square integrable, and is the $`L^2`$ limit of $`X(f_n)`$ along every sequence of test functions converging
in log-energy to the uniform measure on the circle of center $`x`$ and radius $`e^{-r}`$. A random finite
measure $`M_\gamma`$ is the chaos of $`X`$, `IsGMCOf P X γ M`, if for a circle-average process $`X_r`$ and
every bounded continuous $`f`$, in probability,

```math
\int f(x)\,e^{\gamma X_r(x)-\frac{\gamma^2}{2}\mathbb E[X_r(x)^2]}\,|x|_+^{-4}\,d^2x\longrightarrow\int f\,dM_\gamma\qquad(r\to\infty).
```

**Structure constants.** For real charges with $`s=(\bar\alpha-2Q)/\gamma`$,

```math
C_\gamma(\alpha_1,\alpha_2,\alpha_3)=\frac{2\mu^{-s}}{\gamma}\,\Gamma(s)\,\mathbb E\bigl[\rho^{-s}\bigr],\qquad
\bar C_\gamma=\frac2\gamma\,\mathbb E\bigl[\rho^{-s}\bigr],\qquad
\rho=\int_{\mathbb C}\frac{|x|_+^{\gamma\bar\alpha}}{|x|^{\gamma\alpha_1}|x-1|^{\gamma\alpha_2}}\,M_\gamma(d^2x).
```

This is the moment formula of [KRV, Section 2] for the three-point function with insertions at
$`0,1,\infty`$; the unit-volume constant $`\bar C_\gamma=\mu^sC_\gamma/\Gamma(s)`$ has no Gamma factor. The
*extended Seiberg bounds* `ExtendedSeiberg3` are $`\alpha_k\lt Q`$ for each $`k`$ and
$`-s\lt\min\bigl(4/\gamma^2,\ \min_k\tfrac2\gamma(Q-\alpha_k)\bigr)`$; under them
$`0\lt\mathbb E[\rho^{-s}]\lt\infty`$.

**Upsilon.** `IsUpsilon γ U` says that $`U`$ is entire and, on the strip $`0\lt\mathrm{Re}\,z\lt Q`$,

```math
U(z)=\exp\int_0^\infty\Bigl(\bigl(\tfrac Q2-z\bigr)^2e^{-t}-\frac{\sinh^2\bigl((\tfrac Q2-z)\tfrac t2\bigr)}{\sinh\bigl(\tfrac{t\gamma}4\bigr)\sinh\bigl(\tfrac t\gamma\bigr)}\Bigr)\frac{dt}t .
```

Such a $`U`$ is unique, and the DOZZ formula `dozzFormula γ μ U` is the displayed expression above with
$`\Upsilon_{\gamma/2}=U`$.

The definitions are in [`DOZZ/Statements/Defs/`](DOZZ/Statements/Defs/), one per file:

| Group | Lean definitions (namespace `DOZZ`) |
| --- | --- |
| Constants | `Q`, `sExp`, `normPlus`, `lFun`, `conformalWeight`, `ExtendedSeiberg3` |
| Field | `TestFn`, `Distr`, `gffKernel`, `gffCov`, `IsEquatorGFF` |
| Circle averages and chaos | `circleMeasure`, `circleCross`, `circleSelfEnergy`, `circleEnergyGap`, `IsCircleAverage`, `regularizedGMC`, `IsGMCOf` |
| Structure constants | `rho`, `structureConstant`, `unitVolumeStructureConstant` |
| Special functions | `upsilonLogIntegrand`, `upsilonLog`, `IsUpsilon`, `dozzBase`, `dozzFormula`, `reflectionDOZZ`, `dualMu`, `shiftCoeffA` |

## The DOZZ formula

**Theorem** ([KRV, Theorem 2.4]). Let $`0\lt\gamma\lt2`$, $`\mu\gt0`$, and let $`\alpha_1,\alpha_2,\alpha_3`$
satisfy the extended Seiberg bounds with $`s\notin\{0,-1,-2,\dots\}`$. Let $`U`$ satisfy `IsUpsilon γ U`,
and let $`X`$ be an equator-pinned Gaussian free field with chaos $`M_\gamma`$, on any probability space.
Then

```math
C_\gamma(\alpha_1,\alpha_2,\alpha_3)=C^{\mathrm{DOZZ}}_\gamma(\alpha_1,\alpha_2,\alpha_3).
```

Lean: [`DOZZ.dozz_main`](DOZZ/Statements/Roots/DozzMain.lean).

```lean
theorem dozz_main (γ μ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (α₁ α₂ α₃ : ℝ) (hα : ExtendedSeiberg3 γ α₁ α₂ α₃)
    (hs : ∀ n : ℕ, sExp γ α₁ α₂ α₃ ≠ -(n : ℝ))
    (U : ℂ → ℂ) (hU : IsUpsilon γ U)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    (structureConstant P M γ μ α₁ α₂ α₃ : ℂ) = dozzFormula γ μ U α₁ α₂ α₃
```

At $`s\in\{0,-1,-2,\dots\}`$ the factor $`\Gamma(s)`$ has a pole; [KRV] sets the correlation function equal
to $`+\infty`$ there. The formalization instead proves the identity for the unit-volume constant at
*every* point of the domain, as a limit along the points where $`\Gamma(s)`$ is finite:

```math
\bar C_\gamma(\alpha)=\lim_{\substack{a\to\alpha\\ s(a)\notin-\mathbb N}}\frac{\mu^{s(a)}}{\Gamma(s(a))}\,C^{\mathrm{DOZZ}}_\gamma(a).
```

Lean: [`DOZZ.dozz_unitVolume`](DOZZ/Statements/Roots/DozzUnitVolume.lean). At a pole the right-hand
side has a finite limit because a zero of $`\Upsilon_{\gamma/2}`$ cancels the pole of $`\Gamma(s)`$.

**Existence.** For every $`0\lt\gamma\lt2`$ there are a function $`U`$ with `IsUpsilon γ U` and a
probability space carrying an equator-pinned Gaussian free field and its chaos. Lean:
[`DOZZ.dozz_existence`](DOZZ/Statements/Roots/DozzExistence.lean). The chaos is almost surely unique
([`DOZZ.equatorGFF_GMC_unique_ae`](DOZZ/Statements/GMC/EquatorGFFGMCUniqueAe.lean)) and exists for
every equator-pinned field
([`DOZZ.equatorGFF_circle_average_GMC_exists`](DOZZ/Statements/GMC/EquatorGFFCircleAverageGMCExists.lean)).
The model used for existence realizes white noise isonormally on a product of Gaussian sequences and
the log-correlated field by a scale-space construction; Wiener measure is in turn obtained from circle
averages of this field.

**The structure constant as a limit of correlations.** For $`s\gt0`$ the moment formula is the limit of
the three-point correlation with the third insertion sent to infinity, as in [KRV, Section 2]:
[`DOZZ.structureConstant_infinity_limit`](DOZZ/Statements/FourPoint/StructureConstantInfinityLimit.lean).

## The reflection coefficient

For $`\gamma/2\lt\alpha\lt Q`$ put $`p=2(Q-\alpha)/\gamma`$. Let $`\mathcal B`$ be a two-sided Brownian motion
with drift $`-(Q-\alpha)`$ conditioned to stay negative (two independent copies of the conditioned
process, defined by their entrance and transition densities), and $`Z`$ an independent lateral chaos
measure on $`\mathbb R`$ (the image of the chaos under $`x\mapsto-\log|x|`$, characterized by its
invariances and intensity). [KRV, Section 3] defines

```math
\bar R(\alpha)=\mathbb E\Bigl[\Bigl(\int_{\mathbb R}e^{\gamma\mathcal B_s}\,Z(ds)\Bigr)^{p}\Bigr],\qquad
R(\alpha)=\mu^{p}\,\Gamma(-p)\,p\,\bar R(\alpha).
```

**Theorem** ([KRV, Theorem 3.5]). For $`0\lt\gamma\lt2`$, $`\mu\gt0`$ and $`\gamma/2\lt\alpha\lt Q`$ with
$`p\notin\{1,2,\dots\}`$,

```math
R(\alpha)=R^{\mathrm{DOZZ}}(\alpha)=-\bigl(\pi\mu\,l(\tfrac{\gamma^2}4)\bigr)^{\frac{2(Q-\alpha)}\gamma}
\frac{\Gamma\bigl(-\frac\gamma2(Q-\alpha)\bigr)}{\Gamma\bigl(\frac\gamma2(Q-\alpha)\bigr)}\,
\frac{\Gamma\bigl(-\frac2\gamma(Q-\alpha)\bigr)}{\Gamma\bigl(\frac2\gamma(Q-\alpha)\bigr)},
```

and at the excluded points $`R-R^{\mathrm{DOZZ}}\to0`$. Lean:
[`DOZZ.reflection_Rtheor_off_poles`](DOZZ/Statements/Brownian/ReflectionRtheorOffPoles.lean) and
[`DOZZ.reflection_Rtheor_punctured`](DOZZ/Statements/Brownian/ReflectionRtheorPunctured.lean). The value
does not depend on the choice of the Brownian and chaos data
([`DOZZ.reflectionR_eq_of_isReflectionData`](DOZZ/Statements/Brownian/)).

## Other results

Each of the following is a separate statement in [`DOZZ/Statements/`](DOZZ/Statements/).

- **Analytic continuation** ([KRV, Theorem 6.1]): the unit-volume $`N`$-point correlation functions extend
  holomorphically to a complex neighbourhood of the extended Seiberg domain, and are symmetric and
  Möbius covariant there, including $`s\le0`$.
- **Tail estimates** ([KRV, Lemmas 7.1 and 7.3]): the chaos mass near one or two insertions has an exact
  power-law tail whose constant is the reflection coefficient $`\bar R`$, uniformly on compact sets.
- **Extended Seiberg bounds** ([DKRV, Lemma 3.10]): under the bounds, the moment of the chaos with
  insertions is strictly positive and finite; for a single weighted insertion of charge $`\alpha\lt Q`$ and a positive moment order $`p`$, the moment is finite exactly when
  $`p\lt\min\bigl(4/\gamma^2,\tfrac2\gamma(Q-\alpha)\bigr)`$.
- **BPZ equations** ([KRV-local]; [KRV, Section 4]): the four-point function with a degenerate insertion
  $`-\gamma/2`$ or $`-2/\gamma`$ is a real single-valued solution of the hypergeometric equation, and every such
  solution is a combination of $`|F_-|^2`$ and $`|F_+|^2`$ with coefficients fixed by the crossing relation.
- **Shift equations** ([KRV, Sections 9–11]): the structure constant satisfies the two functional
  equations under $`\alpha\mapsto\alpha\pm\gamma/2`$ and $`\alpha\mapsto\alpha\pm2/\gamma`$, as does the DOZZ
  formula; the reflection coefficient satisfies its shift equations.
- **Upsilon** : existence, uniqueness, the shift equations, the zero set, and simplicity of the zeros
  when $`\gamma^2`$ is irrational
  ([`DOZZ.IsUpsilon.deriv_ne_zero_of_irrational`](DOZZ/Statements/Special/IsUpsilonDerivNeZeroOfIrrational.lean));
  the reflection relation of the DOZZ formula
  ([`DOZZ.dozzFormula_reflection`](DOZZ/Statements/Special/DozzFormulaReflection.lean)).

## Proof route

The proof follows [KRV]. The chaos is constructed for any equator-pinned field by Berestycki's
good-point argument, with uniqueness across admissible regularizations; Kahane's convexity inequality
is proved by Gaussian interpolation. Correlation functions are continued analytically in the charges
(Section 6), and the tail estimates of Section 7 give the reflection coefficient. The four-point
functions with a degenerate insertion satisfy the BPZ equations; the classification of real
single-valued solutions of the hypergeometric equation and the crossing relation give the shift
equations of the structure constant (Sections 4 and 9), with the fusion asymptotics of Section 9 and
the appendix. Section 10 identifies the reflection coefficient with $`R^{\mathrm{DOZZ}}`$ through a
pole-subtracted observable, the two-pole expansion and the gluing lemma.

For irrational $`\gamma^2`$ the quotient of the structure constant by the DOZZ formula is meromorphic
on a strip with two periods of irrational ratio, hence constant; the formalization proves that such a
function is constant and pole-free, so it does not need to compare the zeros and poles of the two
functions. The constant is fixed at the point $`s=0`$, where $`\bar C_\gamma=2/\gamma`$ and the zero of
$`\Upsilon_{\gamma/2}`$ at $`0`$ cancels the pole of $`\Gamma(s)`$. The identity extends from a neighbourhood of
$`(Q,Q,Q)`$ to the whole domain along segments by analytic continuation, and to rational $`\gamma^2`$ by
continuity in $`\gamma`$, using chaos measures for all $`\gamma`$ built on one field.

Brownian motion conditioned to stay negative is defined by explicit entrance and transition densities,
including zero drift, and Williams' path decomposition is proved by conditioning on thin bands; no
stochastic integration is used. The Gaussian tilts of [KRV, Section 12] are proved for finite-dimensional
families and extended by a monotone-class argument.

## Build and verify

Install [Lean's elan toolchain manager](https://github.com/leanprover/elan). From a fresh checkout, run:

```sh
lake exe cache get
lake build
```

The toolchain is **`leanprover/lean4:v4.35.0-rc2`**. Mathlib is **`v4.35.0-rc2`**, resolved in
`lake-manifest.json` to **`065356127b1dc0016f66b7283ce0ce2c4055aa55`**. The manifest pins all
dependencies. `lake build` builds the library and the comparator files; with the Mathlib cache, a
clean build takes about an hour on an 8-core machine.

To print the axioms of a main theorem:

```sh
echo 'import DOZZ.Statements.Roots.DozzMain
#print axioms DOZZ.dozz_main' > /tmp/Axioms.lean
lake env lean /tmp/Axioms.lean
```

Two comparator configurations restate the main theorems using only Mathlib, with every definition
written out:

| Configuration | Theorems |
| --- | --- |
| [`comparators/DOZZ`](comparators/DOZZ/) | The DOZZ formula, the unit-volume formula at every point, and existence; with companion theorems certifying the characterizations: uniqueness of $`\Upsilon_{\gamma/2}`$, the law of the circle averages, almost-sure uniqueness, nontriviality and model independence of the chaos, and finiteness of $`\mathbb E[\rho^{-s}]`$ under the extended Seiberg bounds (9 theorems) |
| [`comparators/Reflection`](comparators/Reflection/) | The formula for the reflection coefficient, off the poles and as a limit at the poles; with existence and uniqueness of the law of the conditioned Brownian motion, uniqueness of the lateral chaos law, existence of the reflection data, independence of $`\bar R`$ and $`R`$ from the choice of data, and $`0\lt\bar R\lt\infty`$ (8 theorems) |

Each `Challenge.lean` states the definitions independently and leaves the main theorem bodies as
intentional `sorry` placeholders. The matching `Solution.lean` has the same statements and proves each
one from the library. Lean's [comparator](https://github.com/leanprover/comparator), configured by each
`comparator.json`, checks that Challenge and Solution state the same theorems over the same definitions
and that the Solution uses only the permitted axioms. It also replays the Solution through Lean's kernel
and the independent kernel checkers NanoDa and con-ron. To run it as the
[Palomar registry](https://submit.palomar-registry.org/) does, install
[bubblewrap](https://github.com/containers/bubblewrap) (`bwrap`) and run:

```sh
scripts/verify-comparator.sh
```

The script uses the `lake comparator` and the kernel checkers bundled with the pinned toolchain. It
judges every `comparators/*/comparator.json`, or the configurations given as arguments; set
`SKIP_CACHE_GET=1` when the Mathlib build is already present.
[`scripts/check-lean-sources.py`](scripts/check-lean-sources.py) checks the source requirements: every
Lean file is a regular UTF-8 file, starts with the `module` header of Lean's module system, and has at
most 10,000 lines.

Continuous integration runs on every push to `main` and on every pull request. The
[build workflow](.github/workflows/build.yml) runs the source check, rejects unfinished proofs and
axiom declarations outside the Challenge files, builds everything, and prints the axioms of the main
theorems and of every comparator theorem, each of which must depend on exactly `propext`,
`Classical.choice` and `Quot.sound`. The [comparator workflow](.github/workflows/comparator.yml)
installs bubblewrap and runs `scripts/verify-comparator.sh`.

## Library map

Each statement has its own short file in [`DOZZ/Statements/`](DOZZ/Statements/), stating the result in
namespace `DOZZ`; its proof is in namespace `DOZZ.Proofs`, in the topic directories below. The library
has about 2,200 Lean files and 330,000 lines, all in Lean's module system and none longer than 1,500
lines.

| Directory | Content |
| --- | --- |
| [`DOZZ/Statements`](DOZZ/Statements/) | The definitions and the statements, one per file: [`Defs`](DOZZ/Statements/Defs/) (the objects of the main theorems), [`Roots`](DOZZ/Statements/Roots/) (the three main theorems), and the statements of every area below |
| [`DOZZ/GFF`](DOZZ/GFF/), [`DOZZ/GFFStructure`](DOZZ/GFFStructure/) | The equator-pinned field: covariance algebra, construction from white noise, circle averages and their continuity, Markov decompositions, Poisson and Dirichlet fields |
| [`DOZZ/GMC`](DOZZ/GMC/) | Gaussian multiplicative chaos: Gaussian tilts, construction and uniqueness, moments and the extended Seiberg bounds, Kahane's inequality, cutoff and weighted estimates |
| [`DOZZ/Brownian`](DOZZ/Brownian/) | Brownian motion, conditioned processes, Williams' decomposition, lateral chaos, the reflection mass and its moments |
| [`DOZZ/Complex`](DOZZ/Complex/), [`DOZZ/Upsilon`](DOZZ/Upsilon/), [`DOZZ/Hypergeom`](DOZZ/Hypergeom/) | Holomorphic moments and residues; the function $`\Upsilon_{\gamma/2}`$; the Gauss hypergeometric function, connection formulas, the classification of real solutions, and planar Gamma integrals |
| [`DOZZ/DOZZAlgebra`](DOZZ/DOZZAlgebra/) | Shift, reflection and bridge identities of the DOZZ formula and of $`R^{\mathrm{DOZZ}}`$ |
| [`DOZZ/Correlations`](DOZZ/Correlations/) | [KRV, Sections 6–8]: analytic continuation, symmetry, tail estimates and the residue bridge |
| [`DOZZ/FourPoint`](DOZZ/FourPoint/) | [KRV, Section 9] and [KRV-local]: BPZ equations, crossing, fusion estimates and the shift equation in $`\gamma/2`$ |
| [`DOZZ/ShiftEquations`](DOZZ/ShiftEquations/) | [KRV, Sections 10–11]: the reflection coefficient, the two-pole expansion, gluing, the dual shift and the quotient argument |
| [`DOZZ/Roots`](DOZZ/Roots/) | Assembly of the main theorems: continuation in the charges and continuity in $`\gamma`$ |
| [`GaussianFields`](GaussianFields/) | White noise and the log-correlated scale-space field used to construct the model |
| [`comparators`](comparators/) | The two Mathlib-only comparator configurations |

## How this was built

The Lean code was written with AI coding agents under the authors' supervision. The authors approved
every exact Lean definition and theorem statement before its proof was developed, and Lean checks the
proofs against those statements. The models and tools are recorded in
[`formalization.yaml`](formalization.yaml).

## Authors and citation

The Lean development is by

- **Scott Armstrong** — CNRS and Laboratoire Jacques-Louis Lions, Sorbonne Université; Courant Institute
  School of Mathematics, Computing, and Data Science, New York University
- **Amélie Loher** — All Souls College, University of Oxford

If you use this formalization, please cite it using the metadata in [`CITATION.cff`](CITATION.cff).

## Acknowledgements

Scott Armstrong was supported by the European Research Council (ERC) under the European Union's Horizon
Europe research and innovation programme, grant agreement No. 101200828.
Amélie Loher acknowledges support from the Fondation Sciences Mathématiques de Paris.

## License

The Lean code in this repository is licensed under the **Apache License 2.0** (see [`LICENSE`](LICENSE)).
