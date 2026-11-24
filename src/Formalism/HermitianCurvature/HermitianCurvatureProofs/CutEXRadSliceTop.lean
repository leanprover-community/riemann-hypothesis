module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadJFExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient
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

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem radial_slice_top : CutEX.RadSliceTop := by
  intro Wp Wq _ _ _ _ _ _ P p G hG h hh
  have hc : P.r - P.r = P.r - D.ptSize h := by rw [hh.2]
  have hcpt : KB.CptCoef (p.T.bs P.r) (D.castF hc (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) := by
    cases P with
    | mk k r T T' u u' =>
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0
        exact PBE.slice_level_zero_compact_support k 0 Wp Wq p.T G hG.1 (Nat.zero_le _) [] h hc hh (fun x => x.elim0)
      · exact PBE.slice_pos_cpt k r Wp Wq p.T G hG.1 r le_rfl h0 [] h hc hh (fun x => x.elim0)
  obtain ⟨R, hR⟩ := hcpt.2.1
  have hJ : P5.JFOK (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z'
      (D.castF hc (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) := by
    refine ⟨fun A m => JFxG.cptInCC_G hcpt.1 (PBE.isCompact_gN_le _ _ R) (fun g hg hgC => ?_) A m, hcpt.2.2⟩
    by_contra hne
    exact hgC (hR g hg hne)
  obtain ⟨Φ, hΦ⟩ := P5.radJFExists Wp Wq (JC.parLev P P.r) _ _ _ _ (p.T.bs P.r) _
    (JCTx5.isPlace_lev P p.T ⟨P.r, Nat.lt_succ_self _⟩ p.hP) rfl rfl rfl rfl hJ
  exact ⟨Φ, hΦ⟩

end Formalism.FourierDecayAlt.P
