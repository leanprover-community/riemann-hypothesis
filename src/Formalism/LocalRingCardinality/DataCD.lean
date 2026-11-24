module

public import Formalism.SatakeDualWeyl.Statement
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions

open MeasureTheory Filter Topology Matrix

def UpqT (P Q : ℕ) : Type := Formalism.UG.Upq P Q

instance (P Q : ℕ) : Group (UpqT P Q) := inferInstanceAs (Group (Formalism.UG.Upq P Q))
instance (P Q : ℕ) : TopologicalSpace (UpqT P Q) :=
  inferInstanceAs (TopologicalSpace (Formalism.UG.Upq P Q))
instance (P Q : ℕ) : MeasurableSpace (UpqT P Q) := borel (UpqT P Q)

def UpqT.mat {P Q : ℕ} (g : UpqT P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
  let g' : Formalism.UG.Upq P Q := g; ((g'.1 : GL (Fin P ⊕ Fin Q) ℂ) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)

def lieU (P Q : ℕ) : Submodule ℝ (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) where
  carrier := {X | Xᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc Xᴴ * Formalism.UG.Jpq P Q + Yᴴ * Formalism.UG.Jpq P Q + (Formalism.UG.Jpq P Q * X + Formalism.UG.Jpq P Q * Y)
        = (Xᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X) + (Yᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * Y) := by
          abel
      _ = 0 := by rw [hX, hY, add_zero]
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, star_trivial, ← smul_add, hX,
      smul_zero]

instance (P Q : ℕ) : MeasurableSpace (lieU P Q) := borel (lieU P Q)

def entries {P Q : ℕ} (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ := fun ij => Z ij.1 ij.2

def IsOmegaLeb {P Q : ℕ} (lam : Measure (lieU P Q)) : Prop :=
  lam.IsAddHaarMeasure ∧
    ((lam.prod lam).map (fun ab : lieU P Q × lieU P Q =>
      entries ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)))) = volume

def ballU (P Q : ℕ) (r : ℝ) : Set (lieU P Q) :=
  {X | ∑ i, ∑ j, ‖(X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) i j‖ < r}

def OmegaDensity {P Q : ℕ} (μ : Measure (UpqT P Q)) (c : ENNReal) : Prop :=
  ∃ lam : Measure (lieU P Q), IsOmegaLeb lam ∧
    Tendsto (fun r : ℝ => μ {g | ∃ X ∈ ballU P Q r, UpqT.mat g =
      NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} /
      lam (ballU P Q r)) (𝓝[>] 0) (𝓝 c)

structure CDHaar where
  cd : ∀ P Q : ℕ, Measure (UpqT P Q)
  haar : ∀ P Q, (cd P Q).IsHaarMeasure
  prob : ∀ N, IsProbabilityMeasure (cd N 0)
  trick : ∀ P Q, ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ OmegaDensity (cd P Q) c ∧ OmegaDensity (cd (P + Q) 0) c

end Formalism.BasicNotions
