module

public import Lib.General.Algebra.AbsIntegrallyClosed
public import Lib.General.Algebra.AdicCompletion
public import TauCeti.Analysis.Normed.Ring.Ultra

import TauCeti.RingTheory.RootsOfUnity.Ultrametric
public import Lib.ClassField.Places.GaloisDefs
public import Mathlib.RingTheory.Perfectoid.FontaineTheta
public import TauCeti.NumberTheory.Padics.AlgebraicClosure.Basic
public import TauCeti.RingTheory.Perfectoid.PreTilt.ValuationRing
public import TauCeti.Topology.Algebra.UniformMulAction
public import TauCeti.Topology.MetricSpace.IsometricSMul
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.Algebra.Nonarchimedean.Completion
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import TauCeti.NumberTheory.Padics.Complex.Basic
import TauCeti.NumberTheory.Padics.Complex.FixedPoints

/-!
# Tilting, Fontaine's θ, the ring O_C and Ax's theorem on Galois invariants in ℂ_p

This file studies the absolute Galois group `New.Gp` of `ℚ_p`, its action on `ℂ_p`, and its
invariants. For `p`-adically complete rings in which `p` is not a unit, the untilt and Fontaine's
`θ` are natural, and they are onto if the ring is also absolutely integrally closed. Ax's theorem
then describes the elements of `ℂ_p` fixed by a subgroup `J` of `New.Gp` as limits of algebraic
elements fixed by `J`.

## Main definitions and results

* Tilting for a ring `R` in which `p` is not a unit. Tau Ceti's `PreTilt.map` makes Mathlib's
  `PreTilt R p` functorial, and for `p`-adically complete `R` the untilt `x ↦ x^♯` and Fontaine's
  `θ` are natural (`PreTilt.untilt_natural`, `WittVector.theta_natural`). Both are onto if `R` is
  absolutely integrally closed (`New.Variety.fontaineTheta_surjective_of_isAbsIntegrallyClosed`).
  The tilt of a `p`-adically complete valuation ring is a valuation ring
  (`PreTilt.instValuationRing`).
* The Galois group `New.Gp` of `ℚ̄_p / ℚ_p` and its cyclotomic character `New.cyclotomicGp`.
* The continuous isometric action of `New.Gp` on `ℂ_p` (Tau Ceti's
  `UniformSpace.Completion.instMulSemiringAction`), which restricts to an action by ring
  automorphisms on the ring of integers `New.OC`.
* `O_C` is absolutely integrally closed, with `O_C[1/p] = ℂ_p`.
* `New.Period.ax_mem_closure_fixedField`: Ax's theorem; an element fixed by a subgroup `J` is a
  limit of algebraic elements fixed by `J` (Tau Ceti's
  `PadicComplex.fixedPoints_eq_closure_fixedField`).
* `New.Period.exists_algebraic_of_fixed_near_one`: an element fixed by a neighbourhood of `1` is
  algebraic.

Notions from other files:
* `New.cyclotomicChar`: the ℓ-adic cyclotomic character Γ → ℤ_ℓ^× of a group Γ that acts on a
  field Ω by ring automorphisms; `New.cyclotomicGp` is the case Γ = `New.Gp p`, Ω = ℚ̄_p, ℓ = p.

## Relation to the literature

Known; see `Lib.PadicHodge.PeriodRings.DeRhamPeriods` and `Lib.PadicHodge.TateSen` for sources.
-/

@[expose] public section

noncomputable section

/-! ## Functorial tilting, Fontaine's θ and the Galois action on ℂ_p -/

section CpIntegers

open Ideal WittVector Metric Perfection PadicComplex RingHom Valuation Valued ValuationRing

namespace New.Variety

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R]

/-! ### Surjectivity of the untilt and of `θ`

The tilt is functorial through Tau Ceti's `PreTilt.map`, and the untilt and `θ` are natural
(`PreTilt.untilt_natural`, `WittVector.theta_natural`). -/

/-- Let R be a p-adically complete ring in which p is not a unit. If R is absolutely integrally
closed (every monic polynomial of positive degree over R has a root in R), then every element of R
is the untilt x^♯ of an element x of the tilt. -/
lemma untilt_surjective_of_isAbsIntegrallyClosed [h : IsAbsIntegrallyClosed R] :
    (PreTilt.untilt : PreTilt R p → R).Surjective := by
  -- choose successive `p`-th roots of `r`; the untilt of this sequence is its first term `r`
  intro r
  let pthRoot : R → R := Function.surjInv (h.exists_pow_eq p)
  have h_roots (n : ℕ) : pthRoot^[n + 1] r ^ p = pthRoot^[n] r := by
    rw [Function.iterate_succ_apply', Function.surjInv_eq (h.exists_pow_eq p)]
  let seq : Perfection R p := ⟨fun n ↦ pthRoot^[n] r, h_roots⟩
  exact ⟨quotientMulEquiv p (span {(p : R)}) seq, teichmuller₀_mapMonoidHom_idealQuotientMk⟩

/-- Let R be a p-adically complete ring in which p is not a unit. If R is absolutely integrally
closed, then Fontaine's `θ : W(tilt R) → R` is onto. -/
lemma fontaineTheta_surjective_of_isAbsIntegrallyClosed [IsAbsIntegrallyClosed R] :
    (⇑(fontaineTheta R p)).Surjective := by
  -- every `r ∈ R` is an untilt `y^♯`, and `θ` maps the Teichmüller lift `[y]` to `y^♯`
  intro r
  obtain ⟨y, rfl⟩ := untilt_surjective_of_isAbsIntegrallyClosed (p := p) r
  exact ⟨teichmuller p y, fontaineTheta_teichmuller y⟩

end Variety

/-! ### The Galois group of `ℚ_p` and its action on `ℂ_p` -/

/-- The absolute Galois group G_p = Gal(Q̄_p over Q_p). -/
abbrev Gp (p : ℕ) [Fact p.Prime] : Type := Gal(PadicAlgCl p/ℚ_[p])

/-- The ring of integers `valRingCp p` of `ℂ_p` (its elements of norm at most `1`) as a type, for
the prime `p` fixed by the class `ThePrime p`. -/
abbrev OC {p : ℕ} [ThePrime p] : Type := ↥(valRingCp p)

/-- The valuation ring of ℚ̄_p. -/
abbrev intQpBar (p : ℕ) [Fact p.Prime] : ValuationSubring (PadicAlgCl p) :=
  (PadicAlgCl.valued p).v.valuationSubring

variable {p : ℕ} [Fact p.Prime] (g : Gp p)

open UniformSpace.Completion Variety IsLocalization

/-- The valuation of the valuation ring `intQpBar p` of `ℚ̄_p` orders elements as the norm does. -/
lemma Selmer.valuation_intQpBar_le_iff (x y : PadicAlgCl p) :
    intQpBar p x ≤ intQpBar p y ↔ ‖x‖ ≤ ‖y‖ :=
  v.isEquiv_valuation_valuationSubring.symm x y

@[simp]
lemma Selmer.valuation_intQpBar_lt_one_iff {z : PadicAlgCl p} : intQpBar p z < 1 ↔ ‖z‖ < 1 := by
  simpa using (valuation_intQpBar_le_iff 1 z).not

/-! The isometric, jointly continuous action of `Gp p` on `ℚ̄_p` and `ℂ_p` by ring automorphisms is
Tau Ceti's (`TauCeti.NumberTheory.Padics.Complex.GaloisAction`). -/

instance : UniformContinuousConstSMul ℤ_[p] (PadicAlgCl p) :=
  ⟨fun a ↦ uniformContinuous_const_smul a.val⟩

variable {p : ℕ} [ThePrime p] (g : Gp p) (x : OC)

instance : MulSemiringAction (Gp p) OC := (IsInvariantSubring.mk (by simp)).toMulSemiringAction

@[simp]
lemma OC.coe_smul : (g • x).val = g • x := rfl

/-- The p-adic cyclotomic character of the absolute Galois group of Q_p, obtained from its
action on the algebraic closure of Q_p. -/
abbrev cyclotomicGp : Gp p →* ℤ_[p]ˣ := cyclotomicChar (Γ := Gp p) (PadicAlgCl p) p

/-- `p` is not a unit in `O_C`, as `‖p‖ < 1`. -/
instance : Fact ¬IsUnit (p : OC) :=
  ⟨by simpa [isUnit_iff_dvd_one, valRingCp.dvd_iff_norm_le] using PadicComplex.norm_p_lt_one p⟩

/-- In `O_C`, a nonzero element `t` divides some power of any non-unit `s`. -/
lemma OC.exists_dvd_pow {s t : OC} (hs_nonunit : ¬IsUnit s) (ht_ne_zero : t ≠ 0) :
    ∃ n : ℕ, t ∣ s ^ n := by
  -- `‖s‖ < 1` and `0 < ‖t‖`, so `‖s‖ ^ n < ‖t‖` for some `n`
  have hs_lt : ‖s.val‖ < 1 := by
    simpa [isUnit_iff_dvd_one, valRingCp.dvd_iff_norm_le] using hs_nonunit
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖s.val‖ ^ n < ‖t.val‖ :=
    exists_pow_lt_of_lt_one (by simpa using ht_ne_zero) hs_lt
  exact ⟨n, by simpa [valRingCp.dvd_iff_norm_le] using hn.le⟩

/-- `ℂ_p` is the localization `O_C[1/p]`. -/
instance : Away (p : OC) ℂ_[p] := by
  -- if `‖z‖ < p ^ n` then `z * p ^ n` has norm at most `1`, because `‖p‖ = p⁻¹`
  have hp_one_lt : 1 < (p : ℝ) := by simp [Fact.out]
  refine .mk _ (by simp [NeZero.ne])
    (fun z ↦ (pow_unbounded_of_one_lt ‖z‖ hp_one_lt).imp fun n hz_lt ↦ ?_) (by simp)
  have h_norm_le : ‖z‖ * ((p : ℝ) ^ n)⁻¹ ≤ 1 :=
    (div_le_one (pow_pos (zero_lt_one.trans hp_one_lt) n)).mpr hz_lt.le
  simpa [norm_p_eq_inv] using h_norm_le

/-- `O_C` is absolutely integrally closed: every monic polynomial of positive degree over `O_C`
has a root in `O_C`. -/
instance : IsAbsIntegrallyClosed OC := .of_isIntegrallyClosedIn ℂ_[p]

end New

end CpIntegers

/-!
## Ax's theorem on invariants of subgroups of the Galois group

Ax's theorem is Tau Ceti's Ax–Sen–Tate theorem `PadicComplex.fixedPoints_eq_closure_fixedField`.
The norm estimates below are used elsewhere.
-/

section AxTheorem

open Polynomial Finset IsAlgClosed IsPrimitiveRoot IsUltrametricDist Multiset Nat PadicComplex Real
  UniformSpace.Completion IntermediateField InfiniteGalois Padic

namespace New.Period

variable {p : ℕ} [Fact p.Prime]
  {F : Type*} [NormedField F] [IsUltrametricDist F] {ζ : F}

/-- If `ζ` is a primitive `p ^ (m + 1)`-th root of unity in an ultrametric normed field `F`, then
`‖ζ - 1‖ ^ φ (p ^ (m + 1)) = ‖p‖`, where `φ (p ^ (m + 1)) = p ^ m (p - 1)`. -/
lemma norm_zeta_sub_one_pow {m : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ (m + 1))) :
    ‖ζ - 1‖ ^ φ (p ^ (m + 1)) = ‖(p : F)‖ :=
  hζ.norm'_sub_one_pow_totient_prime_pow

/-- Let K be algebraically closed, L a normed field over K, f in K[X] with leading coefficient
a, x in L, r ≥ 0. If ‖x − w‖ ≥ r for every root w of f, then ‖f(x)‖ ≥ ‖a‖ r^(deg f). -/
lemma pow_le_norm_aeval {K L : Type*} [Field K] [IsAlgClosed K] [NormedField L] [Algebra K L]
    (f : K[X]) (x : L) {r : ℝ} (hr_nonneg : 0 ≤ r)
    (h_roots_far : ∀ w ∈ f.roots, r ≤ ‖x - algebraMap K L w‖) :
    ‖algebraMap K L f.leadingCoeff‖ * r ^ f.natDegree ≤ ‖aeval x f‖ := by
  -- Factor `f` into linear factors and bound each of the `deg f` factors `x - w` below by `r`.
  have h_norm_aeval : ‖aeval x f‖ = ‖algebraMap K L f.leadingCoeff‖ *
      (f.roots.map fun w : K ↦ ‖x - algebraMap K L w‖).prod := by
    nth_rw 1 [(splits f).eq_prod_roots]
    simp [← normHom_apply, map_multiset_prod]
  have h_prod : r ^ f.roots.card ≤ (f.roots.map fun w : K ↦ ‖x - algebraMap K L w‖).prod := by
    simpa using prod_map_le_prod_map₀ (fun _ ↦ r) _ (fun _ _ ↦ hr_nonneg) h_roots_far
  grw [h_norm_aeval, ← card_roots_eq_natDegree, h_prod]

/-- Ax's theorem (a known result), the nontrivial inclusion of the Ax–Sen–Tate theorem: let `J` be
a subgroup of `G_p`. Every `x ∈ ℂ_p` fixed by `J` lies in the closure of the image, under the
inclusion `coe'` of `ℚ̄_p` into its completion `ℂ_p`, of the fixed field of `J` in `ℚ̄_p`. -/
lemma ax_mem_closure_fixedField (J : Subgroup (Gp p)) {x : ℂ_[p]} (hx : ∀ g ∈ J, g • x = x) :
    x ∈ closure (coe' '' fixedField J) := by
  -- this is Tau Ceti's `PadicComplex.fixedPoints_eq_closure_fixedField`
  have hx_fixed : x ∈ MulAction.fixedPoints J ℂ_[p] := fun g ↦ hx g g.property
  rw [PadicComplex.fixedPoints_eq_closure_fixedField] at hx_fixed
  simpa [Set.image_eq_range] using hx_fixed

/-- If `x ∈ ℂ_p` is fixed by every `g` in some neighbourhood of the identity of `G_p`, then `x` is
the image `coe' y` of an element `y` of `ℚ̄_p` under the inclusion of `ℚ̄_p` into `ℂ_p`. -/
lemma exists_algebraic_of_fixed_near_one {x : ℂ_[p]} (hx : ∀ᶠ g : Gp p in nhds 1, g • x = x) :
    ∃ y : PadicAlgCl p, x = coe' y := by
  -- `x` is fixed by the subgroup of a finite extension `E`, so it lies in the closure of `E`, and
  -- the finite-dimensional space `E` is closed.
  obtain ⟨E, h_findim, hE⟩ : ∃ E : IntermediateField ℚ_[p] (PadicAlgCl p),
      FiniteDimensional ℚ_[p] E ∧ (E.fixingSubgroup : Set (Gp p)) ⊆ {g : Gp p | g • x = x} :=
    (krullTopology_mem_nhds_one_iff ℚ_[p] (PadicAlgCl p) {g : Gp p | g • x = x}).mp hx
  have h_closure : x ∈ closure (coe' '' (E : Set (PadicAlgCl p))) := by
    simpa only [InfiniteGalois.fixedField_fixingSubgroup] using
      ax_mem_closure_fixedField E.fixingSubgroup hE
  obtain ⟨y, -, hy⟩ : ∃ y ∈ E.toSubmodule, (toComplL y : ℂ_[p]) = x :=
    (E.toSubmodule.map toComplL.toLinearMap).isClosed_of_finiteDimensional.closure_subset h_closure
  exact ⟨y, hy.symm⟩

end New.Period

end AxTheorem

end
