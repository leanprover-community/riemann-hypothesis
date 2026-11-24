module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix

namespace PositivityTheory.RgDs

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def InCone (abelian₂ η : Fin n → ℝ) : Prop :=
  ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → a < b) ∧ η = abelian₂ + ∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b

theorem inCone_refl (abelian₂ : Fin n → ℝ) : InCone abelian₂ abelian₂ := ⟨0, by simp, by simp⟩

def KeyFor (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) : Prop :=
  ∀ S : Submodule ℂ (L2 ε), FiniteDimensional ℂ S → S ≤ Hlam ε Ψ T.w → Formalism.MainNotions.S.IsKStableOn ε (rreg ε) S →
    ∃ (N : Type) (_ : AddCommGroup N) (_ : Module ℂ N) (e : S →ₗ[ℂ] N) (φ : N),
      (∀ S' : Submodule ℂ (L2 ε), S' ≤ S → Formalism.MainNotions.S.IsKStableOn ε (rreg ε) S' → S' ≠ ⊥ →
        ∃ x : S, (x : L2 ε) ∈ S' ∧ e x ≠ 0) ∧
      (∀ (η : Fin n → ℝ) (x : S), Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (rreg ε) η (x : L2 ε) → e x ≠ 0 →
        InCone (lowK ε lam) η) ∧
      ∀ x : S, Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (rreg ε) (lowK ε lam) (x : L2 ε) → ∃ c : ℂ, e x = c • φ

def Key : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam)) (μ : Fin n → ℤ),
    S7.IsHCParam lam → S7.IsMu lam μ → IsPsiFor ε lam T (S7.PsiM T μ) → KeyFor ε lam T (S7.PsiM T μ)

def Hilb : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), S7.IsHCParam lam → IsPsiFor ε lam T Ψ → KeyFor ε lam T Ψ →
      Formalism.MainNotions.S.IsDS ε lam (sigLam ε Ψ T.w) ∧
        ∀ (η : Fin n → ℝ) (S : Submodule ℂ (Hlam ε Ψ T.w)), Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ T.w) η S →
          InCone (lowK ε lam) η

end PositivityTheory.RgDs
