module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DSymmHypsInhabited
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PRVComponents
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockC
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockD
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockE
public import Formalism.RealPlaceAnalysis.StatementKT
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFPrimeA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockB

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem lowFock_exists (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ N} (hE : IsGlRep E)
    {lam : Fin n → ℝ} (hlam : StrictAnti lam) {V : Submodule ℂ N} (hV : IsKIrrHW ε E (lowK ε lam) V) :
    ∃ x ∈ tensFock (n := n) V, x ∈ physicalSubspace ε ∧ x ≠ 0 ∧
      IsKHWVec ε (diagE ε (eT E) cpT cmT) (lam - rhoC ε + rhoHol ε) x := by
  have hK : Formalism.REAL.KRel ε E := fun a b c d _ _ => hE a b c d
  set S0 := lowerWedgeAlt ε
  have hw : ∀ a, (lfMat ε a a).mulVec (Pi.single S0 (1 : ℂ)) =
      (((rhoHol ε - rhoN ε) a : ℝ) : ℂ) • Pi.single S0 1 :=
    fun a => lfMat_mulVec_single ε a a S0 _ (lowerWedge_weight ε a)
  have hl : ∀ a b, b < a → ε a = ε b → (lfMat ε a b).mulVec (Pi.single S0 (1 : ℂ)) = 0 := by
    intro a b hba he
    have h0 : sgE ε cpFock cmFock a b (fockBasis n S0.1) = (0 : ℂ) • fockBasis n S0.1 := by
      rw [zero_smul]; exact lowerWedge_killed_by_lowering ε hba he
    simpa using lfMat_mulVec_single ε a b S0 0 h0
  have hne : (Pi.single S0 (1 : ℂ) : LfIdx ε → ℂ) ≠ 0 := by
    intro h
    have := congrFun h S0
    simp at this
  obtain ⟨x, hxV, hx0, hxw, hxh⟩ :=
    HW.parthasarathy_tensor_matrix ε hK hV (lfMat_kRel ε) (fun a b h => lfMat_conjTranspose ε h) hne hw hl
      (lf_dom hlam hK hV)
  have hwt : lowK ε lam + (rhoHol ε - rhoN ε) = lam - rhoC ε + rhoHol ε := by
    funext a
    simp only [lowK, Pi.add_apply, Pi.sub_apply]
    ring
  refine ⟨lfLift ε x, lfLift_mem_tensFock ε hxV, lfLift_mem_physSub ε x, lfLift_ne_zero ε hx0, ?_⟩
  rw [← hwt]
  exact lfLift_isKHWVec ε hxw hxh

end ReciprocityTheory.ChartRestriction.DS
