module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.PointDetect0Pf

def EtSep : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) (s : Sec F X),
  (∀ x : X, ∃ (U : Scheme.{0}) (g : U ⟶ X), Etale g ∧ x ∈ Set.range g.base ∧ Sec.res g s = 0) → s = 0

theorem etSep : EtSep := by
  intro R _ F X s h
  choose U g hE hx h0 using h
  have hR : Presieve.ofArrows U g ∈ Scheme.precoverage @Etale X := by
    exact (Scheme.ofArrows_mem_precoverage_iff @Etale).2 ⟨fun x => ⟨x, hx x⟩, hE⟩
  have hT : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) := by
    have := (Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology F.obj (forget _)).1 F.property
    exact (isSheaf_iff_isSheaf_of_type _ _).1 this
  apply (hT.isSheafFor_of_mem_precoverage hR).isSeparatedFor.ext
  rintro Y f ⟨x⟩
  change Sec.res (g x) s = (F.obj.map (g x).op).hom 0
  rw [h0 x, map_zero]

end LateralTheory.E.PointDetect0Pf
