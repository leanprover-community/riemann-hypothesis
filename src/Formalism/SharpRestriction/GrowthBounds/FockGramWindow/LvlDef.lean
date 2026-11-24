module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestPlusOf
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset Formalism.GM Formalism.MainNotions.G.SymmetricFormBlocks

abbrev setZ {N : ℕ} (G : M.BlockData N) (z : ℕ) : M.BlockData N := ⟨G.LL, G.T, G.uPos, G.B, z⟩

def lgN (p A r : ℕ) : ℕ := Nat.log p (8 * A + r) + 1

def x0N (p A r N t : ℕ) : ℕ := ((t + 1) * (r + 1) + ((N + 1) * r + (t + 1) * 2)) * lgN p A r

def JN {N : ℕ} (G : M.BlockData N) (jp : ℕ) : ℕ := min (G.LL.deg G.uPos - jp) (G.B - jp)

def WinLvl : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (G : M.BlockData N), G.BlockOK →
    ∀ (j : Fin G.T.t → ℕ) (jp : ℕ), G.LevelOK j jp → ∀ (A : ℕ), 1 ≤ A → (∀ x, G.LL.deg x ≤ 2 * A) → G.B ≤ 2 * A →
    (∀ i, G.T.z i ≤ 2 * A) →
    ∀ (n₁ : ℕ) (f : Fin n₁ → MvPolynomial (M.BVar N r G.T.t) ℚ_[p]),
      (∀ a, f a ∈ Ljj p (r := r) G j jp) → LinearIndependent ℤ_[p] f →
      (∀ a b, a ≠ b → bePhi p (r := r) G j jp (f a) (f b) = 0) →
      ∀ D : ℤ, (∀ a, bePhi p (r := r) G j jp (f a) (f a) ≠ 0 ∧ (bePhi p (r := r) G j jp (f a) (f a)).valuation ≤ D) →
      ∀ (z0 W h : ℕ) (k : ℤ), 0 ≤ k → 0 < W → W ≤ p ^ h → JN G jp + 1 ≤ p ^ h →
        (∑ i ∈ Finset.range W, (M.bad p (bejj p (r := r) (setZ G (z0 + i)) j jp)
            (Submodule.span ℤ_[p] (Set.range f)) k : ℝ)) ≤
          (W : ℝ) * ((n₁ : ℝ) * ((JN G jp : ℝ) / W +
            (((x0N p A r N G.T.t : ℝ) + D + lgN p A r) + (JN G jp : ℝ) * h / W) / ((k : ℝ) + 1)))

end Formalism.MainNotions.G.GramWindowAlt

end
