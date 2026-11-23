module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientRingIntegersCompactAdicProperties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.GoodCoeff

theorem exists_trace_form_integral_iff : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∃ lam : LL →ₗ[ℚ_[l]] ℚ_[l], ∀ a : LL, (∀ b : O, ∃ u : ℤ_[l], lam (a * algebraMap O LL b) = (u : ℚ_[l])) ↔ ∃ b : O, algebraMap O LL b = a := by
  intro l _ LL _ _ _ O _ _ hG
  have hint := (good_coeff_integers l LL O hG).1
  obtain ⟨⟨hD, hDVR, hFr⟩, hfin, hmod, htop, hopen⟩ := hG
  haveI := hD
  haveI := hDVR
  haveI := hFr
  haveI : FiniteDimensional ℚ_[l] LL := hfin
  letI : Algebra ℤ_[l] LL := ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] LL := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let A : Subring LL := (algebraMap O LL).range
  have hZ : ∀ u : ℤ_[l], algebraMap ℤ_[l] LL u ∈ A := fun u =>
    padicInt_mem A (by rw [RingHom.coe_range]; exact hopen) u
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  let ψ : O ≃+* A := RingEquiv.ofBijective (algebraMap O LL).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), (algebraMap O LL).rangeRestrict_surjective⟩
  have hψ : ∀ a : A, algebraMap O LL (ψ.symm a) = a := fun a =>
    congrArg Subtype.val (ψ.apply_symm_apply a)
  let f : ℤ_[l] →+* O := ψ.symm.toRingHom.comp ((algebraMap ℤ_[l] LL).codRestrict A hZ)
  letI : Algebra ℤ_[l] O := f.toAlgebra
  haveI : IsScalarTower ℤ_[l] O LL := IsScalarTower.of_algebraMap_eq
    (fun u => (hψ ((algebraMap ℤ_[l] LL).codRestrict A hZ u)).symm)
  haveI : IsIntegralClosure O ℤ_[l] LL :=
    { algebraMap_injective := hinj
      isIntegral_iff := fun {x} => by
        rw [← Set.mem_range]
        exact (hint x).symm }
  let D : FractionalIdeal (nonZeroDivisors O) LL := FractionalIdeal.dual ℤ_[l] ℚ_[l] 1
  have hD0 : D ≠ 0 := FractionalIdeal.dual_ne_zero ℤ_[l] ℚ_[l] one_ne_zero
  haveI hP : (D : Submodule O LL).IsPrincipal := FractionalIdeal.isPrincipal D
  set c : LL := Submodule.IsPrincipal.generator (D : Submodule O LL) with hc
  have hDc : (D : Submodule O LL) = Submodule.span O {c} :=
    (Submodule.IsPrincipal.span_singleton_generator _).symm
  have hc0 : c ≠ 0 := by
    intro h
    apply hD0
    apply FractionalIdeal.coeToSubmodule_injective
    show (D : Submodule O LL) = ((0 : FractionalIdeal (nonZeroDivisors O) LL) : Submodule O LL)
    rw [hDc, h, FractionalIdeal.coe_zero]
    exact Submodule.span_singleton_eq_bot.2 rfl
  refine ⟨(Algebra.trace ℚ_[l] LL).comp (LinearMap.mulLeft ℚ_[l] c), fun a => ?_⟩
  have key : (∀ b : O, ∃ u : ℤ_[l], (Algebra.trace ℚ_[l] LL) (c * (a * algebraMap O LL b)) = (u : ℚ_[l]))
      ↔ c * a ∈ D := by
    rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors O) LL) ≠ 0)]
    constructor
    · intro h y hy
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy
      obtain ⟨u, hu⟩ := h b
      refine ⟨u, ?_⟩
      rw [Algebra.traceForm_apply, mul_assoc, hu]
      rfl
    · intro h b
      obtain ⟨u, hu⟩ := h _ ((FractionalIdeal.mem_one_iff _).2 ⟨b, rfl⟩)
      refine ⟨u, ?_⟩
      rw [Algebra.traceForm_apply, mul_assoc] at hu
      rw [← hu]
      rfl
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
  rw [key, ← FractionalIdeal.mem_coe, hDc, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [Algebra.smul_def, mul_comm] at hz
    exact mul_left_cancel₀ hc0 hz
  · rintro ⟨z, rfl⟩
    exact ⟨z, by rw [Algebra.smul_def, mul_comm]⟩

end GlobalTheory.GoodCoeff
