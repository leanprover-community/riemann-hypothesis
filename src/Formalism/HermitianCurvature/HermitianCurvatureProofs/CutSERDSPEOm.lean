module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPair
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

private theorem continuousAt_w1_of_ne_zero (k r : ℕ) (l : Fin r) {c : ℂ} (hc : c ≠ 0) :
    ContinuousAt (w1 k r l) c := by
  refine continuousAt_pi.2 fun p => continuousAt_pi.2 fun q => ?_
  show ContinuousAt (fun c => w1 k r l c p q) c
  simp only [w1]
  split_ifs
  · exact continuousAt_id
  · exact (continuous_star.continuousAt).inv₀ (star_ne_zero.mpr hc)
  · exact continuousAt_const
  · exact continuousAt_const
private theorem continuousAt_wCell_fst_of_mem_OmX (k r : ℕ) (x : (Fin r → ℂ) × Mx k r) (hx : x.1 ∈ OmX r)
    (i : Fin (r + 1)) : ContinuousAt (fun y : (Fin r → ℂ) × Mx k r => wCell k r i y.1) x := by
  induction i using Fin.induction with
  | zero =>
    simp only [Formalism.FourierDecayAlt.P.Qx6.wCell_zero]
    exact continuousAt_const
  | succ l ih =>
    simp only [Formalism.FourierDecayAlt.P.Qx6.wCell_succ]
    refine ih.mul ?_
    have hf : ContinuousAt (fun y : (Fin r → ℂ) × Mx k r => y.1 l) x := by fun_prop
    exact (continuousAt_w1_of_ne_zero k r l (hx l)).comp (f := fun y : (Fin r → ℂ) × Mx k r => y.1 l) hf

theorem spectral_pairing_big_cell : RDSPEOm := by
  intro k r Wp Wq _ _ _ _ _ _ D
  have hmem : ∀ x ∈ DomR k r D.z D.z', eR k r x ∈ JF.Om k r D.z D.z' := by
    intro x hx
    refine ⟨?_, ?_⟩
    · exact Formalism.FourierDecayAlt.P.TLB.wCell_gv (Pa := M.Par.mk k r 0 0 0 0) D hx
    · exact Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus D.z_mem D.z'_mem hx.1 hx.2.1 hx.2.2
  refine ⟨hmem, ?_, ?_⟩
  · intro x hx
    refine ContinuousAt.continuousWithinAt ?_
    exact (continuousAt_wCell_fst_of_mem_OmX k r x hx.1 (Fin.last r)).mul continuous_snd.continuousAt
  · intro g hg
    exact ⟨hg.1, hg.2.2⟩

end Formalism.FourierDecayAlt.P.CutSE
