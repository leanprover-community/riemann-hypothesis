module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.OntoAllOf
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

@[expose] public section

noncomputable section

open AlgebraicGeometry

namespace CrystallineSemistableComparison.Onto

open HT

def HTBij : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
    ∃ P : HTPre l K, ∀ M : Model l K, M.Sm → (∀ n, P.Inj M n) ∧ (∀ d, M.Conn d → P.Top M d) ∧
      ∀ d, SmoothOfRelativeDimension d M.p → ∀ n, Surj P M n ∧
        Module.finrank ℚ_[l] (M.V n) = ∑ a ∈ Finset.range (n + 1), Module.finrank K (Hdg M.q a n)

theorem htBij_of_parts (h : Parts) (hR : HodgeTateDimensionEquality) (hH : HodgeTateMapExists) (hS : SqEx3) (hD : DiagEt3) (hF : EtFin) : HTBij := by
  intro l _ K _
  obtain ⟨P, hP⟩ := hH l K
  refine ⟨P, fun M hM => ⟨(hP M hM).1, (hP M hM).2, fun d hd n => ?_⟩⟩
  have hs : Surj P M n := ontoAll_of h hS hD hF l K P (fun N hN => (hP N hN).1) M d hM hd n
  exact ⟨hs, hR l K P M n hM (hF l K M hM n) ((hP M hM).1 n) hs⟩

end CrystallineSemistableComparison.Onto

end
