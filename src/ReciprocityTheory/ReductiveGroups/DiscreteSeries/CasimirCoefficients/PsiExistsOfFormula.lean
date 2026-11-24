module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.GelfandSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def PsiFormulaStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (T : KType ε (lowK ε lam)),
    IsHCParam lam → GapAtLeast ε lam h → 1 ≤ q0 ε →
    ∃ Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V),
      (∀ (k₁ k₂ : KG ε) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
        Ψ (toMK k₁ * g * toMK k₂) = T.op k₁ * Ψ g * T.op k₂) ∧
      Ψ 1 = 1 ∧
      SmoothOnGV ε Ψ ∧
      (∀ g, inUJ ε g → casimirV ε Ψ g = ((casVal lam : ℝ) : ℂ) • Ψ g) ∧
      (∀ (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X →
        ‖Ψ (toMK k * NormedSpace.exp X)‖ ≤
          Real.exp (-(h / 8) * min (hs X) (Real.sqrt (hs X) / Real.sqrt (2 * q0 ε)))) ∧
      (∀ μ : Measure (UJ ε), μ.IsHaarMeasure →
        (16 * (n : ℝ) * q0 ε < h → Integrable (fun g : UJ ε => Ψ (toM g)) μ) ∧
        (8 * (n : ℝ) * q0 ε < h → MemLp (fun g : UJ ε => Ψ (toM g)) 2 μ) ∧
        (∀ s : ℝ, 0 ≤ s → 8 * (n : ℝ) * q0 ε + 4 * s * Real.sqrt (2 * q0 ε) < h →
          Integrable (fun g : UJ ε => ‖Ψ (toM g)‖ ^ 2 * hs (toM g) ^ (s / 2)) μ)) ∧
      (∀ μ : Fin n → ℤ, IsMu lam μ → ∀ X : Matrix (Fin n) (Fin n) ℂ, inP ε X →
        Ψ (NormedSpace.exp X) =
          ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
            ∫ k, PhiM μ (toMK k⁻¹ * NormedSpace.exp X * toMK k)⁻¹ • (T.op k * projW T * T.op k⁻¹) ∂(muK ε))

section Gelfand

variable {F : Type*} [AddCommGroup F] [Module ℂ F]

def opPow (A : Fin n → Fin n → F → F) : ℕ → Fin n → Fin n → F → F
  | 0, a, b, f => if a = b then f else 0
  | k + 1, a, b, f => ∑ c, A a c (opPow A k c b f)

def opGelfand (A : Fin n → Fin n → F → F) (k : ℕ) (f : F) : F := ∑ a, opPow A k a a f

end Gelfand

section Right

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def rightE (ε : Fin n → Bool) : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E) :=
  fun a b f => EabV ε a b f

def rightEanti (ε : Fin n → Bool) : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E) :=
  fun a b f => -EabV ε (Fin.rev b) (Fin.rev a) f

end Right

def PsiAllStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (T : KType ε (lowK ε lam)),
    IsHCParam lam → GapAtLeast ε lam h → 1 ≤ q0 ε →
    ∃ Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V),
      (∀ (k₁ k₂ : KG ε) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
        Ψ (toMK k₁ * g * toMK k₂) = T.op k₁ * Ψ g * T.op k₂) ∧
      Ψ 1 = 1 ∧
      SmoothOnGV ε Ψ ∧
      (∀ g, inUJ ε g → casimirV ε Ψ g = ((casVal lam : ℝ) : ℂ) • Ψ g) ∧
      (∀ (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X →
        ‖Ψ (toMK k * NormedSpace.exp X)‖ ≤
          Real.exp (-(h / 8) * min (hs X) (Real.sqrt (hs X) / Real.sqrt (2 * q0 ε)))) ∧
      (∀ μ : Measure (UJ ε), μ.IsHaarMeasure →
        (16 * (n : ℝ) * q0 ε < h → Integrable (fun g : UJ ε => Ψ (toM g)) μ) ∧
        (8 * (n : ℝ) * q0 ε < h → MemLp (fun g : UJ ε => Ψ (toM g)) 2 μ) ∧
        (∀ s : ℝ, 0 ≤ s → 8 * (n : ℝ) * q0 ε + 4 * s * Real.sqrt (2 * q0 ε) < h →
          Integrable (fun g : UJ ε => ‖Ψ (toM g)‖ ^ 2 * hs (toM g) ^ (s / 2)) μ)) ∧
      (∀ (k : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
        opGelfand (rightE ε) k Ψ g = gval (icShift lam) k • Ψ g ∧
        opGelfand (rightEanti ε) k Ψ g = gval (icShift (-lam)) k • Ψ g) ∧
      (∀ μ : Fin n → ℤ, IsMu lam μ → ∀ X : Matrix (Fin n) (Fin n) ℂ, inP ε X →
        Ψ (NormedSpace.exp X) =
          ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
            ∫ k, PhiM μ (toMK k⁻¹ * NormedSpace.exp X * toMK k)⁻¹ • (T.op k * projW T * T.op k⁻¹) ∂(muK ε))

end ReciprocityTheory.ChartRestriction.DS.S7
