module

public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCutHoc
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut.SumCut

def LeafChainsSum : Prop := ∀ (R : Type) [CommRing R] (A : Type) (E : A → Spc) (c : Cofan E), Nonempty (IsColimit c) →
  Nonempty (IsColimit (Cofan.mk ((chains R).obj c.pt) fun a => (chains R).map (c.inj a)))

def LeafHKSum : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (A : Type) (K : A → Cx R) (c : Cofan K),
  Nonempty (IsColimit c) → ∀ n : ℤ, Function.Bijective fun (x : HK R c.pt F n) (a : A) => HK.pull R (c.inj a) F n x

end LateralTheory.CohomologicalPurity.TubeCut.SumCut

namespace LateralTheory.CohomologicalPurity.TubeCut
open SumCut

theorem LeafSum_of (hc : LeafChainsSum) (hk : LeafHKSum) : LeafSum := by
  intro R _ F A E c hc' n
  exact hk R F A (fun a => (chains R).obj (E a)) _ (hc R A E c hc') n

end LateralTheory.CohomologicalPurity.TubeCut
