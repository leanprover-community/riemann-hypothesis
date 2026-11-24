module

public import Formalism.HermitianCurvature.HerGenC
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMainCpt
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
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

theorem blockGrowthBound_apx_cutF (hA : P5.ThmPActualCpt) {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (nn χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ) (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hχ : C6.IsCut0 χ)
    (hF : B.CkOn ⊤ (B.GV P.k P.r) F) (hnn : ∀ y, 0 < nn y) :
    ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn (apx (D.cutF p.T.base χ F ε) n) Y K N := fun _ hε n =>
  block_growth_bound_of_compact_coefCpt hA p nn _ Y K N Cb hCb (cptCoef_apx P p.T.base hχ hF hε n) hnn



end

end Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination

namespace Formalism.FourierDecayAlt.P.CutBPEq.CompactFormNormalFormDomination

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination MeasureTheory
open scoped ENNReal

noncomputable section


end

end Formalism.FourierDecayAlt.P.CutBPEq.CompactFormNormalFormDomination
