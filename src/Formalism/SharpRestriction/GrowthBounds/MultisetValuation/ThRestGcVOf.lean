module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaRestSExpVOf
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.AllPlacesOfRestrictions
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ExpansionAllPlacesOfPlace
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF Gser)

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

theorem th_GtV_eq (j : ℕ) (v : X.Pl) (c c' : K0 p) :
    ea_GtV X j v c c' = ren (Sum.map (Sigma.mk v) (Sigma.mk v))
      (Gt p (Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) c c') := by
  unfold ea_GtV Gt
  rw [th_ren_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [th_ren_ren]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem th_restGcV_of (hG : RestGc p) : ea_RestGcV X := by
  intro c hc j v K' _ _ vp hvp μ hμ0 hμ
  have hs := X.std v
  obtain ⟨u, hu, V, hV, heq⟩ := hG hs.five_le c hc (X.G.P.n' v) (NN X.G.P.m X.t j)
    (NN X.G.P.m X.t (j + 1)) hs.two_le hs.even (X.om v) K' vp hvp μ hμ0 hμ
  let ρ : Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) → X.ZA j := fun z => ⟨v, z⟩
  refine ⟨u, hu, ren ρ V, th_IntR_ren ρ hV, ?_⟩
  have hT : MvPowerSeries.HasSubst (tOf vp μ (X.coordZA K' j)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero
      (th_tOf_const vp μ hμ0 _ (coordZA_const X K' j))
  have hT' : MvPowerSeries.HasSubst
      (tOf vp μ (coordZ (r0 := NN X.G.P.m X.t j) (r1 := NN X.G.P.m X.t (j + 1)) (X.om v) K' 1)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero
      (th_tOf_const vp μ hμ0 _ (coordZ_const (X.om v) K' 1))
  have hg : MvPowerSeries.constantCoeff
      (-(MvPowerSeries.map (algebraMap (K0 p) K'))
        (Gt p (Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)))
          (wK p c) (wK p ((sigW p) c)))) = 0 := by
    simp [th_Gt_const]
  have hh : MvPowerSeries.constantCoeff
      (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * hhS p K' u :
        MvPowerSeries (Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) K')) = 0 := by
    simp [hhS_const]
  have hfun : (fun k => tOf vp μ (X.coordZA K' j) (Sum.map (Sigma.mk v) (Sigma.mk v) k)) =
      fun k => ren ρ (tOf vp μ (coordZ (X.om v) K' 1) k) := by
    funext k
    simp only [tOf]
    rw [th_coordZA_eq, th_ren_psubst ρ (coordZ_const (X.om v) K' 1 k)]
  rw [th_GtV_eq, th_map_ren, ← th_ren_neg, ← th_ren_expK _ hg, th_subst_ren _ hT, hfun,
    ← th_ren_subst ρ hT', heq, th_ren_mul, th_ren_expK ρ hh, th_ren_neg, th_ren_mul, th_ren_C,
    th_hhA_eq]

end Formalism.MainNotions.FormalGroupSystem.Pf
