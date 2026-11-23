module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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

namespace Formalism.L2.Col

open Formalism.BasicNotions NumberField

structure ColRows (R : Ranks) where

  LL : Type
  [instLL : Field LL]
  embLL : LL →+* ℂ
  places : Rows.Places LL

  Tau : Type
  [instTau : Fintype Tau]
  card_Tau : Fintype.card Tau = R.f

  Word : Type

attribute [instance] ColRows.instLL ColRows.instTau

structure ColRec where

  R : Ranks

  host : Host R

  sp : @Spaces R host.F host.E _ _ _ _ host.cmStar _

  what₂ : ColRows R

  eTau : what₂.Tau ≃ (R.Psi)
  [wordFin : Fintype what₂.Word]

  u₀ : what₂.Word

  hcW : what₂.Word → what₂.Tau → HCParam R

  mem : ∀ u : what₂.Word, Member R what₂.Tau (hcW u)
  [nfLL : NumberField what₂.LL]
  [starLL : StarRing what₂.LL]

  embE : host.E →+* what₂.LL

  cOf : what₂.Word → host.E

  clsLat : letI := host.cmStar; ∀ u i, (mem u).C.cls i → Submodule (𝓞 host.E) (sp.X i).V

  fm : ∀ u, MemberForms what₂.LL what₂.embLL what₂.places what₂.Tau (hcW u) (mem u).C (mem u).A (mem u).P

attribute [instance] ColRec.wordFin ColRec.nfLL ColRec.starLL

end Formalism.L2.Col

namespace Formalism.BasicNotions

end Formalism.BasicNotions

end
