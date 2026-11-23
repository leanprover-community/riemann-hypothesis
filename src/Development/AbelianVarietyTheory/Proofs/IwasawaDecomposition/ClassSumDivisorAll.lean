module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoTies

theorem twAllAt_tr {D : D7} (N : ∀ u, Submodule (NumberField.RingOfIntegers D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)
    {x : NChoice D} {y : ThData D} (H : DQ.TwAllAt D x y) : DQ.TwAllAt (setDiv D N h) (nchTr N h x) (xdTr N h y) := by
  obtain ⟨hc, N0, S, H⟩ := H
  refine ⟨hc, N0, S, fun w hw => ⟨(H w hw).1, fun a ha => ?_⟩⟩
  obtain ⟨h1, h2, h3, ⟨e, h4, h4', h4''⟩, h5, h6⟩ := (H w hw).2 a ha
  exact ⟨h1, h2, h3, ⟨e, h4, h4', fun s hs => (sLen_tr N h _ s _ _ _).trans_le (h4'' s hs)⟩, h5, h6⟩

theorem twAll_pt {K : Ctx} (β : BPt K) : DQ.TwAllAt β.D β.O.ex.nch β.O.ex.xd := twAllAt_tr (nPrime β.p.L) β.p.ht β.twAll


end GlobalTheory.GeoTies
