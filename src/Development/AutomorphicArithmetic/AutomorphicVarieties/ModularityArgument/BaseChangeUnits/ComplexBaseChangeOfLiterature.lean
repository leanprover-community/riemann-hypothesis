module

public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChangeLifts.SplitLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.CBC

namespace UpperTheory.V.Z.Bc

def CBCc : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M],
    (Module.finrank K M).Prime → IsTotallyComplex K → ∀ n : ℕ, 1 ≤ n →
      (∀ π : Cusp K n, (∃ η : HChar K, IsNormChar M η ∧ (π.twist η).Iso π) ∨
        ∃ P : Cusp M n, WeakBC π.sat P.sat ∧ (∀ τ m, π.inf (τ.comp (algebraMap K M)) m → P.inf τ m) ∧ SplitLift π P) ∧
      (∀ P : Cusp M n, (∀ σ : M ≃ₐ[K] M, P.ConjIso σ.toRingEquiv) →
        ∃ π : Cusp K n, WeakBC π.sat P.sat ∧ (∀ τ m, P.inf τ m → π.inf (τ.comp (algebraMap K M)) m) ∧ SplitLift π P) ∧
      ∀ (π : Cusp K n) (P : Cusp M n), (∀ σ : M ≃ₐ[K] M, P.ConjIso σ.toRingEquiv) → WeakBC π.sat P.sat →
        (∀ η : HChar K, IsNormChar M η → ¬ (π.twist η).Iso π) ∧
        ∀ π₁ : Cusp K n, WeakBC π₁.sat P.sat → ∃ η : HChar K, (η = 1 ∨ IsNormChar M η) ∧ (π.twist η).Iso π₁

def CBCr : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M],
    (Module.finrank K M).Prime → IsTotallyComplex K → ∀ n : ℕ, 1 ≤ n →
      (∀ π : Cusp K n, RegInf n π.inf → (∃ η : HChar K, IsNormChar M η ∧ (π.twist η).Iso π) ∨
        ∃ P : Cusp M n, WeakBC π.sat P.sat ∧ ∀ τ m, π.inf (τ.comp (algebraMap K M)) m → P.inf τ m) ∧
      (∀ P : Cusp M n, RegInf n P.inf → (∀ σ : M ≃ₐ[K] M, P.ConjIso σ.toRingEquiv) →
        ∃ π : Cusp K n, WeakBC π.sat P.sat ∧ ∀ τ m, P.inf τ m → π.inf (τ.comp (algebraMap K M)) m) ∧
      ∀ (π : Cusp K n) (P : Cusp M n), (∀ σ : M ≃ₐ[K] M, P.ConjIso σ.toRingEquiv) → WeakBC π.sat P.sat →
        ∀ π₁ : Cusp K n, WeakBC π₁.sat P.sat → ∃ η : HChar K, (η = 1 ∨ IsNormChar M η) ∧ (π.twist η).Iso π₁

theorem cbcr_of_cbcc (h : CBCc) : CBCr := by
  intro K M _ _ _ _ _ _ hp hK n hn
  obtain ⟨a, b, c⟩ := h K M hp hK n hn
  refine ⟨fun π _ => (a π).imp_right fun ⟨P, h1, h2, _⟩ => ⟨P, h1, h2⟩, fun P _ hP => ?_, fun π P h1 h2 => (c π P h1 h2).2⟩
  obtain ⟨π, h1, h2, _⟩ := b P hP
  exact ⟨π, h1, h2⟩

end UpperTheory.V.Z.Bc
