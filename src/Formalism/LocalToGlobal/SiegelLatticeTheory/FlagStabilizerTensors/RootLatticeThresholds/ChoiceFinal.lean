module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.L2RightTranslationThm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.L2SGConstSmul
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.L2SGPhiOfNeZeroAndLtInfty
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBLGapPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBLReproPf
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf

theorem wuBesselOfLoc_all {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) : WuBesselOfLoc C :=
  Formalism.L2.SG.Pf.WuBL.wuBesselOfLoc Formalism.L2.SG.Pf.WuBL.reproduction_translation Formalism.L2.SG.Pf.WuBL.l2RightTranslation_thm
    Formalism.L2.SG.Pf.WuBL.parameter_gap_of_hypothesis C

theorem goodSRest_of_loc {D : D7} {X : HidaSetting D} {θ : ℝ} {C : Choice X θ} (hLF : LocFactor C) (hB : WuBessel C)
    (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hsm : v0Of C τ ∈ smoothVecs (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ))
    (hT : Formalism.BasicNotions.dsigTie D) : GoodSRest hB u u' τ :=
  Formalism.L2.SG.Pf.GoodS.goodSRest_of hB u u' τ hsm (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty C hLF hB u τ)
    (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty C hLF hB u' τ) hT

end Formalism.L2.SG.Pf
