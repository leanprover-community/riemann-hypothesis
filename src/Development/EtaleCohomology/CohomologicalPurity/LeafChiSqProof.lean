module

public import Development.EtaleCohomology.CohomologicalPurity.LeafExcOfEqvPfSq
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem dblPO (A : Arrow Spc) : IsPushout A.hom A.hom (dbl.inl A) (dbl.inr A) :=
  IsPushout.of_hasPushout A.hom A.hom

theorem mmPO {P' P : Arrow Spc} (φ : P' ⟶ P) : IsPushout P'.hom (P'.hom ≫ φ.right) (ii φ) (jj φ) :=
  IsPushout.of_hasPushout P'.hom (P'.hom ≫ φ.right)

theorem LeafChiSq_of : LeafChiSq := by
  intro P' P φ
  have s2 : IsPushout ((P'.hom ≫ φ.right) ≫ jj φ) P'.hom (dbl.inr (QQ φ)) (ii φ ≫ dbl.inl (QQ φ)) :=
    IsPushout.paste_horiz (mmPO φ).flip (dblPO (QQ φ)).flip
  have c : IsPushout P'.hom (P'.hom ≫ (chi φ).right) (dbl.inl P' ≫ dbl.map (chi φ)) (dbl.inr (QQ φ)) := by
    have e1 : P'.hom ≫ (chi φ).right = (P'.hom ≫ φ.right) ≫ jj φ := ij_cond φ
    have e2 : dbl.inl P' ≫ dbl.map (chi φ) = ii φ ≫ dbl.inl (QQ φ) := dinl_map (chi φ)
    rw [e1, e2]; exact s2.flip
  exact IsPushout.of_top c (dbl.inr_map (chi φ)) (dblPO P')
end LateralTheory.CohomologicalPurity.TubeCut
