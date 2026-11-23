module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

def OtherFactorFormula.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock), 2 ≤ f → 1 ≤ r → 1 ≤ a →
    ∃ C₀ : ℚ, C₀ ≠ 0 ∧
      fibreDegree f r a c =
        C₀ * (f * (r * a)).factorial / ((r * a).factorial : ℚ) ^ f *
          (numStandardTable (rectangle r a) : ℚ) ^ f ∧
      ∀ Q : ℕ → Fin f → RootRing f (r + a),
        IsPowerSumDecomposition f (r + a) (restPolynomial f r a c) Q →
        ∀ (k : ℕ) (hk2 : 2 ≤ k) (hkN : k ≤ r + a) (τ τ' : Fin f), τ' ≠ τ →
          ∃ S : MvPolynomial (Fin (r + a)) ℚ,
            powerSumHom (r + a) S =
              ∑ nu ∈ partitionsOf r k,
                C ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) *
                  aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) ∧
            restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) τ') =
              C₀ * k * (f * (r * a) + 1).factorial /
                  (((r * a + k).factorial : ℚ) * ((r * a - (k - 1)).factorial : ℚ) *
                    ((r * a).factorial : ℚ) ^ (f - 2)) *
                (numStandardTable (rectangle r a) : ℚ) ^ (f - 2) *
                symmetricGroupCharacter (rectangle r a)
                  ((k - 1) :: List.replicate (r * a - (k - 1)) 1) *
                AddMonoidAlgebra.coeff S (Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1)

def SchurSignCoefficient.Statement : Prop :=
  ∀ (N r k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) (nu : Fin r → ℕ) (s : ℚ), (s = 1 ∨ s = -1) →
    Antitone nu → ∑ i, nu i = k →
    ∃ S : MvPolynomial (Fin N) ℚ,
      powerSumHom N S = aeval (fun i : Fin N => C s * X i) (schur (Fin N) nu) ∧
      AddMonoidAlgebra.coeff S (Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1) =
        s ^ k * if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
          (-1 : ℚ) ^ ((Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card) / k
        else 0

def HookTableauCount.Statement : Prop :=
  ∀ r k l : ℕ, l < k → l < r → numStandardTable (hookShape r k l) = Nat.choose (k - 1) l

def RectangleTablePos.Statement : Prop :=
  ∀ r a : ℕ, 0 < numStandardTable (rectangle r a)

def HookSumBound.Statement : Prop :=
  ∀ (r a k : ℕ) (b : (Fin r → ℕ) → ℚ), 1 ≤ k →
    (∀ nu ∈ partitionsOf r k, |b nu| ≤ numStandardTable (fun i => a + nu i)) →
    ∑ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1), |b nu| ≤
      (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) * numStandardTable (rectangle r a)

end

end RestTerms

end GroundTheory.Heights₂.Heights
