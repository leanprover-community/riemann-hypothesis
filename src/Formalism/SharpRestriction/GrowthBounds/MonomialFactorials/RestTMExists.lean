module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestTMHypOf
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem restTM_of (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (D : Formalism.BasicNotions.D7) (hM : ∀ XM : flipOneThree.InstM, ModelLatticeRank D XM) (hF : RestFree C0 CE1 CE2 X)
    (hS : RestTMSize C0 CE1 CE2 X) (hE : RestTMEps C0 CE1 CE2 X 1) : RestTM C0 CE1 CE2 X 1 :=
  restTM_of_rests D hM hF (restTMHyp_of hH hS) hE

theorem restTM_exists : ∃ CM : ℝ, 1 ≤ CM ∧ ∀ (_D : Formalism.BasicNotions.D7) (C0 CE1 CE2 CYb Cde Ck CD Cb Cc : ℝ) (X : flipOneThree.Inst),
    flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X → RestFree C0 CE1 CE2 X → RestTMSize C0 CE1 CE2 X →
      RestTMEps C0 CE1 CE2 X CM → RestTM C0 CE1 CE2 X CM := by
  exact ⟨1, le_rfl, fun D C0 CE1 CE2 CYb Cde Ck CD Cb Cc X hH hF hS hE =>
    restTM_of C0 CE1 CE2 X hH D (alternative_mean_value_theorem D) hF hS hE⟩

end Formalism.MainNotions.G.SymmetricFormBlocks

end
