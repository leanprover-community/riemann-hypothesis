module

public import Development.EtaleCohomology.EtaleSheaves.EtaleSpreading.EtSpreads
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
open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.SpreadPf.Cut

def FP : MorphismProperty CommRingCat.{0} := fun _ _ f => f.hom.FinitePresentation

def FPSpreads : Prop := MorphismProperty.PreIndSpreads.{0} FP

def EtStage : Prop := ∀ {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}} {c : Cocone D}
  (_ : IsColimit c) (j : J) {T' T : CommRingCat.{0}} (f' : D.obj j ⟶ T') (f : c.pt ⟶ T) (g : T' ⟶ T),
  FP f' → IsPushout (c.ι.app j) f' f g → Et f →
  ∃ (k : J) (T'' : CommRingCat.{0}) (f'' : D.obj k ⟶ T'') (g'' : T'' ⟶ T),
    IsPushout (c.ι.app k) f'' f g'' ∧ Et f''

theorem EtSpreads_of (hF : FPSpreads) (hS : EtStage) : LateralTheory.E.SpreadPf.EtSpreads where
  exists_isPushout {J} _ _ {D} {c} hc {T} f hf := by
    have hfp : FP f := by
      change f.hom.FinitePresentation
      let := f.hom.toAlgebra
      have h : Algebra.Etale c.pt T := hf
      exact h.finitePresentation
    obtain ⟨j, T', f', g, hP, hf'⟩ := hF.exists_isPushout hc f hfp
    exact hS hc j f' f g hf' hP hf

theorem Spread_of (hF : FPSpreads) (hS : EtStage) : LateralTheory.E.DescendPf.Spread :=
  LateralTheory.E.SpreadPf.Spread_of (EtSpreads_of hF hS)

end LateralTheory.E.SpreadPf.Cut
