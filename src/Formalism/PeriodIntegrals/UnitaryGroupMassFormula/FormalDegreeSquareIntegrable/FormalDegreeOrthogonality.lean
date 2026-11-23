module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeSquareIntegrable.FormalDegreeFromOrthogonality
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PIW.HCFdeg

open MeasureTheory PI.UpqRep
open scoped InnerProductSpace

lemma umat_mem {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : umat g ∈ UJset ε := g.2

def repOf {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : IsCRepOn (UJset ε) σ) :
    UJ ε →* (H →L[ℂ] H) where
  toFun g := σ (umat g)
  map_one' := h.1
  map_mul' g g' := h.2 _ (umat_mem g) _ (umat_mem g')

lemma irr_repOf {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : IsCRepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) : Irr (repOf ε σ h) := by
  intro S hS hst
  refine hI S hS ?_
  intro g hg v hv
  obtain ⟨x, rfl⟩ : g ∈ Set.range (coeMatrixAlt ε) := by rw [range_coeMatrix]; exact hg
  exact hst x v hv

theorem formal_degree_orthogonality : FormalDegreeFromOrthogonality := by
  intro hOrth hUni n ε H _ _ _ _ σ hU hI hSq
  haveI := (hUni n ε).1
  haveI := (hUni n ε).2
  obtain ⟨d, hd, h⟩ := hOrth (UJ ε) (muG ε) H (repOf ε σ hU.1)
    (fun g v => hU.2.1 _ (umat_mem g) v)
    (fun v => (hU.2.2 v).comp_continuous (continuous_coeMatrix ε) umat_mem)
    (irr_repOf ε σ hU.1 hI) (fun v w => hSq v w)
  exact ⟨d, hd, fun v w v' w' => h v w v' w'⟩

end PIW.HCFdeg
