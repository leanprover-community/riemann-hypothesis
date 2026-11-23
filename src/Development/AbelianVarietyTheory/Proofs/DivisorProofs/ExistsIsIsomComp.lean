module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationCoeEqNorm

@[expose] public section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.EmbConj

open GlobalTheory.PadicComplexHost

variable {p : ℕ} [Fact p.Prime]

theorem injective_of_comp {Λ : Type} [CommRing Λ] [IsDomain Λ] [Algebra ℤ_[p] Λ]
    [Module.Finite ℤ_[p] Λ] (φ : Λ →+* PadicAlgCl p)
    (h : φ.comp (algebraMap ℤ_[p] Λ) = algebraMap ℤ_[p] (PadicAlgCl p)) :
    Function.Injective φ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[p])
  change Ideal.comap (algebraMap ℤ_[p] Λ) (RingHom.ker φ) = ⊥
  rw [RingHom.comap_ker, h, ← RingHom.injective_iff_ker_eq_bot,
    IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (PadicAlgCl p), RingHom.coe_comp]
  exact (algebraMap ℚ_[p] (PadicAlgCl p)).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])

theorem exists_algEquiv {Λ : Type} [CommRing Λ] [IsDomain Λ] [Algebra ℤ_[p] Λ]
    [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (φ₀ φ₁ : Λ →+* PadicAlgCl p)
    (h₀ : φ₀.comp (algebraMap ℤ_[p] Λ) = algebraMap ℤ_[p] (PadicAlgCl p))
    (h₁ : φ₁.comp (algebraMap ℤ_[p] Λ) = algebraMap ℤ_[p] (PadicAlgCl p)) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ∀ x, σ (φ₀ x) = φ₁ x := by
  have tf : ∀ φ : Λ →+* PadicAlgCl p, Function.Injective φ →
      letI := φ.toAlgebra
      Module.IsTorsionFree Λ (PadicAlgCl p) := fun φ hφ => by
    letI := φ.toAlgebra
    haveI : FaithfulSMul Λ (PadicAlgCl p) := (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
    infer_instance
  have alg : letI := φ₀.toAlgebra
      Algebra.IsAlgebraic Λ (PadicAlgCl p) := by
    letI := φ₀.toAlgebra
    haveI : IsScalarTower ℤ_[p] Λ (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq' h₀.symm
    haveI : Algebra.IsAlgebraic ℤ_[p] (PadicAlgCl p) := ⟨fun x =>
      (IsFractionRing.isAlgebraic_iff ℤ_[p] ℚ_[p] (PadicAlgCl p)).2
        (Algebra.IsAlgebraic.isAlgebraic x)⟩
    exact Algebra.IsAlgebraic.extendScalars (R := ℤ_[p]) (FaithfulSMul.algebraMap_injective _ _)
  obtain ⟨g, hg⟩ : ∃ g : PadicAlgCl p →+* PadicAlgCl p, ∀ x, g (φ₀ x) = φ₁ x := by
    let f := @IsAlgClosed.lift (PadicAlgCl p) _ _ Λ _ _ (PadicAlgCl p) _ _ φ₀.toAlgebra
      φ₁.toAlgebra (tf φ₀ (injective_of_comp φ₀ h₀)) (tf φ₁ (injective_of_comp φ₁ h₁)) alg
    exact ⟨@AlgHom.toRingHom _ _ _ _ _ _ φ₀.toAlgebra φ₁.toAlgebra f,
      fun x => @AlgHom.commutes _ _ _ _ _ _ φ₀.toAlgebra φ₁.toAlgebra f x⟩
  have hq : g.comp (algebraMap ℚ_[p] (PadicAlgCl p)) = algebraMap ℚ_[p] (PadicAlgCl p) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (PadicAlgCl p)]
    ext a
    exact (congrArg g (RingHom.congr_fun h₀ a).symm).trans
      ((hg _).trans (RingHom.congr_fun h₁ a))
  let g' : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p := { g with commutes' := RingHom.congr_fun hq }
  exact ⟨AlgEquiv.ofBijective g' (Algebra.IsAlgebraic.algHom_bijective g'), hg⟩

end GlobalTheory.EmbConj
