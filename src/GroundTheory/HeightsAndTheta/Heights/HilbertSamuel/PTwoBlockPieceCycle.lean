module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockPieceCycle
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockPieceIndex
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockModuleFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockModuleCycle
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsModulePieceHilbert
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.LengthLocQuotEqZero

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem TwoBlockPieceCycle.proof (hA : TwoBlockPieceIndex.Statement) (hF : TwoBlockModuleFinite.Statement)
    (hH : ModulePieceHilbert.Statement) (hC : TwoBlockModuleCycle.Statement) : TwoBlockPieceCycle.Statement := by
  intro D Ω _ _ κ _ x B c l hX hx hB hsp hl
  obtain ⟨hm₁, hm₂, hle, ⟨N, hN, hNJ⟩, hdim⟩ := hF D Ω κ x B c l hX hx hB hsp hl
  obtain ⟨a₀, C, h⟩ := hH (Fin 2) (FinTwoTypeFamily κ) _ _ N D hm₁ hm₂ hle hN hNJ hdim (fun _ => 1)
  refine ⟨a₀, C, fun a b ha hb => ?_⟩
  have h1 := h ![a, b] (fun k => by fin_cases k <;> simpa)
  have e1 : (![a, b] + fun _ => 1 : Fin 2 → ℕ) = ![a + 1, b + 1] := by
    funext k
    fin_cases k <;> rfl
  have e2 : (fun (_ : Fin D) (k : Fin 2) => ((![a, b] k : ℕ) : ℤ)) = fun _ => ![(a : ℤ), (b : ℤ)] := by
    funext _ k
    fin_cases k <;> rfl
  have e3 : ((∑ k, ![a, b] k : ℕ) : ℝ) = (a + b : ℝ) := by
    simp [Fin.sum_univ_two]
  rw [e1, e2, hC D Ω κ x B c l hX hx hB hsp hl, e3] at h1
  rw [hA D Ω κ x B c l hX hx hB hsp hl a b]
  exact h1

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
