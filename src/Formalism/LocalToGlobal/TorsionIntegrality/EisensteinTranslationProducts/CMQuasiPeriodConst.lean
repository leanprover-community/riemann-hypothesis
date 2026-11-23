module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaZeroLogDerivative
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

def cmTheta (b : ℤ) (d : ℕ) : ℂ := ((b : ℂ) + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2

def cmPair (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) : PeriodPair where
  ω₁ := (a : ℂ)
  ω₂ := cmTheta b d
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp [cmTheta] at him hre
    have ht : t = 0 := by
      rcases him with h1 | h1
      · exact h1
      · exact absurd h1 (by positivity)
    subst ht
    simp at hre
    refine ⟨?_, rfl⟩
    rcases hre with h1 | h1
    · exact h1
    · exact absurd h1 (by positivity)

def cmForm (a b c m n : ℤ) : ℤ := a * m ^ 2 + b * m * n + c * n ^ 2

def CmThetaEq : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ), 4 * (a : ℤ) * c = b ^ 2 + d →
    cmTheta b d ^ 2 = (b : ℂ) * cmTheta b d - (a : ℂ) * (c : ℂ) ∧
    cmTheta b d + conj (cmTheta b d) = (b : ℂ) ∧ cmTheta b d * conj (cmTheta b d) = (a : ℂ) * (c : ℂ)

def CmStable : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d), 4 * (a : ℤ) * c = b ^ 2 + d →
    ∀ m n : ℤ, MulStable (cmPair a b d ha hd) ((m : ℂ) + (n : ℂ) * cmTheta b d)

def CmNorm : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d), 4 * (a : ℤ) * c = b ^ 2 + d → ∀ m n : ℤ,
    Complex.normSq ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d) = (a : ℝ) * (cmForm a b c m n : ℝ) ∧
    herm (cmPair a b d ha hd) ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d)
        ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d)
      = ((2 * (cmForm a b c m n : ℝ) / Real.sqrt d : ℝ) : ℂ) ∧
    ((m, n) ≠ (0, 0) → 1 ≤ cmForm a b c m n)

def CmAltE : Prop :=
  ∀ (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (m n m' n' : ℤ),
    altE (cmPair a b d ha hd) ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d)
      ((m' : ℂ) * (a : ℂ) + (n' : ℂ) * cmTheta b d) = ((n * m' - m * n' : ℤ) : ℝ)

def CmTheta0 : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d), 4 * (a : ℤ) * c = b ^ 2 + d → Odd a →
    d % 8 = 7 → ∀ (m n : ℤ) (z : ℂ),
      th0 (cmPair a b d ha hd) ((a : ℂ) / 2) (z + ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d))
        = (-1 : ℂ) ^ (cmForm a b c m n).natAbs
          * Complex.exp ((Real.pi : ℂ) * herm (cmPair a b d ha hd) z
                ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d)
              + (Real.pi : ℂ) * herm (cmPair a b d ha hd) ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d)
                ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d) / 2)
          * th0 (cmPair a b d ha hd) ((a : ℂ) / 2) z

def CMQuasiPeriodConst : Prop :=
  ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), MulStable L α → α.im ≠ 0 → IsKerReps L α S →
    s2 L = (∑ P ∈ S, L.weierstrassP P) / (α * (α - conj α))

end Formalism.L2.Th1.F
