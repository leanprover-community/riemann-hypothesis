module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsEtaleFirstChernUntwisted
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.HT

open CH

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

structure EtP (e : E.EtFam l K) : Prop where
  good : e.Good
  one : ∀ (M : Model l K) (n : ℕ), e M n 0 (GlobalTheory.EtC.one (l ^ n) M.spc) = CH.oneH (AcrEl M.P n)
  one_ex : ∀ M : Model l K, ∃ v : M.T 0, ∀ k, v.lev k = GlobalTheory.EtC.one (l ^ k) M.spc
  first_chern_class_exists : ∀ (M : Model l K) (D : E.LineData M.X) (r : E.Roots l), ∃ v, IsEtaleFirstChernUntwisted r D v
  c1 : ∀ (M : Model l K) (D : E.LineData M.X) (r : E.Roots l) (v : M.T 2), IsEtaleFirstChernUntwisted r D v →
    ∀ (C : Type 1) [Category.{0} C] (G : C ⥤ El M.P) (Λ : E.Lift G D) (n : ℕ),
      ∃ (z : Cn (G ⋙ modF (AcrEl M.P n)) 2) (hz : d _ 2 z = 0), Λ.IsCoc n (E.tCo G n 2 z) ∧
        (cx _).cls z hz = (Mor.restrict (modF (AcrEl M.P n)) G).pull 2 (e M n 2 (v.lev n))

end CrystallineSemistableComparison.HT
