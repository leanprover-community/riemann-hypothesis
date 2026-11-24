module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignatureFrame
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

@[expose] public section

open MeasureTheory Matrix Finset Formalism.BasicNotions Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.IndefiniteRowSideFullHecke.SignatureFrame
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Published

def DiscreteSeriesFormalDegree : Prop :=
  ∀ (c : CDHaar) (n P Q : ℕ) (ε : Fin n → Bool) (F : SignFrame ε P Q) (lam : Fin n → ℝ),
    (StrictAnti lam ∧ ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),

      ((CompleteSpace H ∧ Nontrivial H ∧ IsURepOn (UJset ε) π ∧ IsIrredOn (UJset ε) π ∧ IsSqIntOn ε π) ∧

        HasInfChar ε (fun a => (lam a : ℂ)) π ∧

        (∃! S : Submodule ℂ H, IsKTypeOf ε π (lam + rhoN ε - rhoC ε) S) ∧

        ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε π μ S →
          ∃ k : Fin n → Fin n → ℕ, (∀ a b, k a b ≠ 0 → a < b) ∧
            μ = (lam + rhoN ε - rhoC ε) + ∑ a, ∑ b, (k a b : ℝ) • root a b) ∧

      IsFdeg (cdMeasure c F) π
        ((∏ a : Fin n, ∏ b ∈ Ioi a, (lam a - lam b)) /
          ∏ a : Fin n, ∏ b ∈ Ioi a, (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)))

end GlobalTheory.Published
