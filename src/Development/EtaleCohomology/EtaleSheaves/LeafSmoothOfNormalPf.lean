module

public import Development.EtaleCohomology.EtaleSheaves.LeafModelCurveCut
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafSmoothOfNormalPf

def LeafStalkSmoothClosed : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω)
  [IsIntegral C], LocallyOfFiniteType c → (∀ y : C, IsIntegrallyClosed (C.presheaf.stalk y)) →
    topologicalKrullDim C = 1 → ∀ y : C, y ≠ genericPoint C → (c.stalkMap y).hom.FormallySmooth

def LeafRelDimOne : Prop := ∀ (Ω : Type) [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω),
  IsIntegral C → Smooth c → topologicalKrullDim C = 1 → SmoothOfRelativeDimension 1 c

theorem smooth_of_stalks (Ω : Type) [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω) [LocallyOfFiniteType c]
    (h : ∀ y : C, (c.stalkMap y).hom.FormallySmooth) : Smooth c := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  exact top_le_iff.mp fun y _ => h y

theorem stalk_smooth_all (hA : LeafStalkSmoothClosed) (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}}
    (c : C ⟶ Sp Ω) (hC : IsIntegral C) (hc : LocallyOfFiniteType c)
    (hn : ∀ y : C, IsIntegrallyClosed (C.presheaf.stalk y)) (hd : topologicalKrullDim C = 1) (y : C) :
    (c.stalkMap y).hom.FormallySmooth := by
  by_cases hy : y = genericPoint C
  · subst hy
    exact c.genericPoint_mem_smoothLocus_of_perfectField
  · exact hA Ω c hc hn hd y hy

theorem LeafSmoothOfNormal_of (hA : LeafStalkSmoothClosed) (hB : LeafRelDimOne) :
    LateralTheory.E.LeafModelCurveCut.LeafSmoothOfNormal := by
  intro Ω _ _ C c hC hc hn hd
  have hs : Smooth c := smooth_of_stalks Ω c (stalk_smooth_all hA Ω c hC hc hn hd)
  exact hB Ω c hC hs hd

end LateralTheory.E.LeafSmoothOfNormalPf
