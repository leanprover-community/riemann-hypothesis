module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.VolPin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def VolPinGC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), PrimeHyp D u (Tu D u') → ∀ (t : TT Y u u'),
    t.relevant → t.toTerm.generic → t.G ≠ 0 →
    ∀ w : Point D.host.E (D.R.rS + 1), t.toTerm.atPt w → ∀ μR : Measure X.B.I.Ginf, IsPinnedR t w μR →
    ∀ K : Set X.B.I.Ginf, MeasurableSet K →
      (∀ r ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, ∃! s, s ∈ Formalism.L2.SG.TermOp.ROinf t ∧ s * r ∈ K) →
    ∀ (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D),
      Formalism.L2.SG.PairVal.NormRep t.toTerm w F' L U →
      (μR K).toReal = Formalism.L2.SG.PairVal.volIdx D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M t.toTerm w F' L

def VolumeOddGeneric : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ i, 3 ≤ D.host.g i) → PrimeHyp D u (Tu D u') →
    ∀ (t : TT Y u u'), t.relevant → t.toTerm.generic → t.G ≠ 0 →
    ∀ w : Point D.host.E (D.R.rS + 1), t.toTerm.atPt w → ∀ μR : Measure X.B.I.Ginf, IsPinnedR t w μR →
    ∀ K : Set X.B.I.Ginf, MeasurableSet K →
      (∀ r ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, ∃! s, s ∈ Formalism.L2.SG.TermOp.ROinf t ∧ s * r ∈ K) →
    ∀ (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D),
      Formalism.L2.SG.PairVal.NormRep t.toTerm w F' L U →
      (μR K).toReal = Formalism.L2.SG.PairVal.volIdx D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M t.toTerm w F' L

end Formalism.L2.SG.VolPin
