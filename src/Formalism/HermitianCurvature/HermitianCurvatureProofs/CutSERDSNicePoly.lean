module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpRGrp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDCCLower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatPolyOK
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPolyProp
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

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_nice_polynomial : RDSNicePoly := by
  intro k r Wp Wq _ _ _ _ _ _ D o κ Θ hΘ F hF
  obtain ⟨-, hGl, -⟩ := CutMP.polynomial_decay_admissible k r Wp Wq o κ Θ hΘ
  have hG : CutMP.GlobCoef Θ (κ : ℝ) := hGl κ le_rfl
  have hκ : (0 : ℝ) ≤ κ := Nat.cast_nonneg κ
  obtain ⟨ε, hε, hFck, hFcc, hFs⟩ := hF
  have hO : IsOpen {g : B.Mat k r | Gf k r D.z D.z' g < ε} := isOpen_lt (Gf_cont _ _) continuous_const
  have hz : ∀ g ∈ B.GV k r, g ∈ {g : B.Mat k r | Gf k r D.z D.z' g < ε} → F g = 0 := by
    intro g hg hgO
    by_contra hne
    exact absurd hgO (not_lt.2 (hFs g hg hne))
  refine ⟨⟨ε, hε, ?_, ?_, ?_⟩, ⟨ε, hε, ?_, ?_, ?_⟩⟩
  · exact (CutMP.class_lower_decay_holds k r Wp Wq Θ κ 0 hκ hG F hFck (fun m => hFcc _ m)).1
  · intro A' m'
    have h := (CutMP.class_lower_decay_holds k r Wp Wq Θ κ (A' + κ) hκ hG F hFck (fun m => hFcc _ m)).2 m'
    rwa [add_sub_cancel_right] at h
  · intro g hg hne
    by_contra hlt
    exact hne (rdsp_opApply_vanish Θ hO hz g hg (not_le.1 hlt))
  · exact (rdsp_opAdj_cc Θ κ hG F hFck 0 (fun m => hFcc _ m)).1
  · intro A' m'
    exact (rdsp_opAdj_cc Θ κ hG F hFck A' (fun m => hFcc _ m)).2 m'
  · intro g hg hne
    by_contra hlt
    exact hne (rdsp_opAdj_vanish Θ hO hz g hg (not_le.1 hlt))

end Formalism.FourierDecayAlt.P.CutSE
