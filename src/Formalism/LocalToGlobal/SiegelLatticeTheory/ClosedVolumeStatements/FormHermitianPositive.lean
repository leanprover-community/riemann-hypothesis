module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AdmNPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictK
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TermsAtPtFinite
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermOp Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Closed

section Cols

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Lat.Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}

theorem TermK_holds (cs : ColSys X u what₂) (cs' : ColSys X u' rows') : TermK F0 F0' cs cs' :=
  Formalism.L2.SG.Pf.termK X cs cs'

theorem AdmN_holds (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (hTF : FrameTie X u u' F0 F0') :
    AdmN F0 F0' cs cs' :=
  adm_norm_of_fixed_frames cs cs' hTF (TermK_holds cs cs') (_root_.Formalism.L2.SG.Pf.modGAt X)

theorem AdmPar_holds (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (hTF : FrameTie X u u' F0 F0') :
    AdmPar F0 F0' cs cs' :=
  adm_parity_of_norm cs cs' (TermK_holds cs cs') (AdmN_holds cs cs' hTF)

end Cols

end Formalism.L2.SG.Closed
