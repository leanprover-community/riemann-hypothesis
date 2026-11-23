module

public import Development.EtaleCohomology.EtaleSheaves.RelNormPfGlue
public import Development.EtaleCohomology.EtaleSheaves.RelNormPfAff
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.RelNormPf

theorem closedAt_comp {X N T : Scheme.{0}} (c' : X ⟶ N) (k' : N ⟶ T) (V : T.Opens)
    (h : ClosedAt c' (k' ⁻¹ᵁ V)) (hs : Function.Surjective (k'.app V)) : ClosedAt (c' ≫ k') V := by
  intro b hb
  obtain ⟨p, hm, hp⟩ := hb
  obtain ⟨a', ha'⟩ := h b ⟨p.map (k'.app V).hom, hm.map _, (Polynomial.eval₂_map (p := p) (k'.app V).hom (c'.app (k' ⁻¹ᵁ V)).hom b).trans hp⟩
  obtain ⟨a, rfl⟩ := hs a'
  exact ⟨a, ha'⟩

theorem normClosed : NormClosed := by
  intro Z S g _ _ _ V hV
  have H : g = g.toNormalization.toNormalization ≫
      (g.toNormalization.fromNormalization ≫ g.fromNormalization) := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization,
      Scheme.Hom.toNormalization_fromNormalization]
  let h := g.normalizationDesc _ _ H
  have e1 : g.toNormalization ≫ h = g.toNormalization.toNormalization :=
    g.toNormalization_normalizationDesc _ _ H
  have e2 : h ≫ g.toNormalization.fromNormalization ≫ g.fromNormalization = g.fromNormalization :=
    g.normalizationDesc_comp _ _ H
  have i1 : h ≫ g.toNormalization.fromNormalization = 𝟙 _ :=
    Scheme.Hom.normalization.hom_ext g _ _ g.fromNormalization
      (by rw [reassoc_of% e1, Scheme.Hom.toNormalization_fromNormalization, Category.comp_id])
      (by rw [Category.assoc, e2]) (Category.id_comp _)
  have i2 : g.toNormalization.fromNormalization ≫ h = 𝟙 _ :=
    Scheme.Hom.normalization.hom_ext g.toNormalization _ _ g.toNormalization.fromNormalization
      (by rw [Scheme.Hom.toNormalization_fromNormalization_assoc, e1, Category.comp_id])
      (by rw [Category.assoc, i1, Category.comp_id]) (Category.id_comp _)
  have : IsIso g.toNormalization.fromNormalization := ⟨h, i2, i1⟩
  have e := g.toNormalization.toNormalization_fromNormalization
  rw [← e]
  exact closedAt_comp _ _ V (closedAt_preimage _ V hV)
    (ConcreteCategory.bijective_of_isIso (g.toNormalization.fromNormalization.app V)).2

theorem RelNorm_of : LateralTheory.E.SteinPf.RelNorm := RelNorm_of_closed normClosed

end LateralTheory.E.RelNormPf
