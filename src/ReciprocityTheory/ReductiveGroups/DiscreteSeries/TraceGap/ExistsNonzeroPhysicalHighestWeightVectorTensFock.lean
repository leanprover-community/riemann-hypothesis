module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.BlockAnti
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.WeylPos
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockC
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockD
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockE
public import Formalism.RealPlaceAnalysis.StatementKT
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockB

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

theorem lf_dom_block {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : BlockAnti ε lam) :
    ∀ a b : Fin n, a < b → ε a = ε b →
      (lowK ε lam + (rhoHol ε - rhoN ε)) b ≤ (lowK ε lam + (rhoHol ε - rhoN ε)) a := by
  have key : ∀ d : ℕ, ∀ a b : Fin n, b.val - a.val = d → a < b → ε a = ε b →
      rhoC ε a - rhoC ε b ≤ lam a - lam b := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro a b hd hab he
      by_cases hc : ∃ c, a < c ∧ c < b ∧ ε c = ε a
      · obtain ⟨c, hac, hcb, hce⟩ := hc
        have hac' := Fin.lt_def.mp hac
        have hcb' := Fin.lt_def.mp hcb
        have e1 := ih (c.val - a.val) (by omega) a c rfl hac hce.symm
        have e2 := ih (b.val - c.val) (by omega) c b rfl hcb (hce.trans he)
        linarith
      · simp only [not_exists, not_and] at hc
        have h1 := HW.rhoC_consec ε hab he hc
        have h2 := hlam a b hab he
        linarith
  intro a b hab he
  have e := key _ a b rfl hab he
  have hh := lf_rhoHol_eq ε he
  simp only [lowK, Pi.add_apply, Pi.sub_apply]
  linarith

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem exists_nonzero_physical_highestWeight_vector_tensFock (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ N} (hE : IsGlRep E)
    {lam : Fin n → ℝ} (hlam : BlockAnti ε lam) {V : Submodule ℂ N} (hV : IsKIrrHW ε E (lowK ε lam) V) :
    ∃ x ∈ tensFock (n := n) V, x ∈ physicalSubspace ε ∧ x ≠ 0 ∧
      IsKHWVec ε (diagE ε (eT E) cpT cmT) (lam - rhoC ε + rhoHol ε) x := by
  classical
  have hF : Formalism.REAL.KRel ε E := fun a b c d _ _ => hE a b c d
  obtain ⟨x, hxV, hx0, hxw, hxh⟩ := HW.parthasarathy_tensor_matrix ε hF hV (lfMat_kRel ε)
    (fun a b h => lfMat_conjTranspose ε h) (ν := rhoHol ε - rhoN ε) (f := Pi.single (lowerWedgeAlt ε) 1)
    (fun h => by simpa using congrFun h (lowerWedgeAlt ε))
    (fun a => lfMat_mulVec_single ε a a (lowerWedgeAlt ε) _ (lowerWedge_weight ε a))
    (fun a b hba he => by
      simpa using lfMat_mulVec_single ε a b (lowerWedgeAlt ε) 0 (by rw [lowerWedge_killed_by_lowering ε hba he, zero_smul]))
    (lf_dom_block hlam)
  refine ⟨lfLift ε x, lfLift_mem_tensFock ε hxV, lfLift_mem_physSub ε x, lfLift_ne_zero ε hx0, ?_⟩
  have hμ : lam - rhoC ε + rhoHol ε = lowK ε lam + (rhoHol ε - rhoN ε) := by
    unfold lowK; abel
  rw [hμ]
  exact lfLift_isKHWVec ε hxw hxh

end ReciprocityTheory.ChartRestriction.DS.TRGap
