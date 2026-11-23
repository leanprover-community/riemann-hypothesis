module

public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WeightUpdateAtPlace
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.FrobeniusSqIterateTeichmuller
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

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

abbrev sysC {p : ℕ} [Fact p.Prime] (G : GAtP p) (Fl : Fills G) (Lv : Levels Fl) (Ch : Chain Lv)
    (std : ∀ v, Std p (G.P.n' v) G.P.m Fl.t Fl.mm Fl.c G.P.r (Fl.TT v) (Fl.a v) (Fl.b v) (G.P.lam0 v) (Fl.w v))
    (hfin : ∀ j c, (Lv.lev j c).FinClasses) (h0 : (p : G.O) ≠ 0) : Sys p :=
  sysOf G Fl Lv Ch std hfin h0 fun v => omOf p (G.P.n' v) (G.P.setting v).even (G.P.setting v).two_le

end Formalism.L2.G.Pend
