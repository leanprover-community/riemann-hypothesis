module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetKey
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DistinctWordsDistinctParameters
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
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

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

theorem roinf_eq_nocol {D : D7} {X : HidaSetting D} (Y : Full X) {u : D.what₂.Word} (ρ : (Y.cs u).Cl)
    (t : GTerm X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u)) (hl : t.lam = (Y.cs u).lamOf ρ)
    (hl' : t.lam' = (Y.cs u).lamOf ρ) (hγ : t.lin ∈ NLam ((Y.cs u).lamOf ρ) (lf D (X.Fu u))) :
    ROinf t = Formalism.L2.SG.TermOp.KExpCut.NOcol (X.Fu u) (Y.cs u) ρ := by
  ext y
  unfold ROinf ROset Formalism.L2.SG.TermOp.KExpCut.NOcol
  rw [hl, hl']
  constructor
  · rintro ⟨x, n, hx, hy, hn, -⟩
    exact ⟨x, n, hx, hy, hn⟩
  · rintro ⟨x, n, hx, hy, hn⟩
    refine ⟨x, n, hx, hy, hn, ?_⟩
    let H := NLamSub ((Y.cs u).lamOf ρ) (lf D (X.Fu u))
    exact H.mul_mem (H.mul_mem (H.inv_mem hγ) hn) hγ

theorem idMeetVolC_of (hK : IdMeetKeyC) (hV : VolColC) : IdMeetVolC := by
  intro D X Y u hN hF ρ t ht hm
  obtain ⟨-, hlin⟩ := hK D X Y u hN ρ ρ t ht hm
  have hR := roinf_eq_nocol Y ρ t hm.1.symm hm.2.1.symm hlin
  have hex : ∃ Ω, Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROinf t) Ω := hF t
  unfold FundOf
  rw [dite_eq_left hex]
  apply hV D X Y u ρ
  rw [← hR]
  exact hex.choose_spec

end Formalism.L2.SG.Pf.IdMeet
