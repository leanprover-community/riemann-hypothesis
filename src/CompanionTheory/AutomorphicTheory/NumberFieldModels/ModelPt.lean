module

public import CompanionTheory.AutomorphicTheory.JacobiDiagonalBounds.TieRad
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.MainStatements.NFTie

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

def NFModelPt : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), P.OK → MA.IsModelLevel P (MA.DQ P) L →
    ∀ l0 : ℕ, 1 ≤ l0 → l0 ≤ P.k → ∀ w : List C.Letter, KB.CutWord P l0 w → ∀ (a : Wd.Ix (Fin w.length)) (s : ℕ),
      ∃ (m : ℕ) (b : Fin m → MA.A P (MA.DQ P)) (u : Fin m → List (MA.A P (MA.DQ P))) (C : ℝ), 0 ≤ C ∧
        (∀ j, b j ∈ Submonoid.closure (MA.bddSet P L)) ∧
        (∀ j, (u j).length = w.length ∧ ∀ x ∈ u j, x ∈ MA.hatSet P L) ∧
        ∀ f g : M.Ty P → MA.SmQ P.r P.TT,
          (∀ ρ q, MA.evQ P (g ρ) q = ((MA.Gq P q ^ s : ℝ) : ℂ) * MA.evQ P (f ρ) q) → ∀ q : MA.Qp P.r P.TT,
          ∑ ρ, ‖MA.evQ P (MA.actA P (Formalism.FourierDecayAlt.P.NormalFormRelations.gM P l0 L (D.positionted w) a) g ρ) q‖ ^ 2 ≤
            C * MA.Gq P q ^ (2 * s) * (Complex.normSq ((∏ l, q.1.1 l) * q.1.2))⁻¹ ^ w.length *
              ∑ j, ∑ ρ, ‖MA.evQ P (MA.actA P (b j * (u j).prod) f ρ) q‖ ^ 2

end

end Formalism.MainStatements.NFTie
