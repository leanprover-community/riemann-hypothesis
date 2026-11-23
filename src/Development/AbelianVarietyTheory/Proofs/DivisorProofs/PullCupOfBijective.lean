module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace GlobalTheory.PullbackCupProduct

open GlobalTheory.CatCoh

universe u v u' v' u'' v''

theorem pull_cup_of_bijective {R R' : Type} [CommRing R] [CommRing R']
    {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
    {σ : R →+* R'} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
    {F'' : C'' ⥤ CommAlgCat.{0} R'} (m : CoefMap σ F F'') (n : CoefMap (RingHom.id R') F' F'')
    (h1 : Function.Bijective n.pull1) (h2 : Function.Bijective n.pull2) (a b : H1 F) :
    (LinearEquiv.ofBijective n.pull2 h2).symm (m.pull2 (cup F a b)) =
      cup F' ((LinearEquiv.ofBijective n.pull1 h1).symm (m.pull1 a))
        ((LinearEquiv.ofBijective n.pull1 h1).symm (m.pull1 b)) := by
  have back : ∀ x, n.pull1 ((LinearEquiv.ofBijective n.pull1 h1).symm x) = x := fun x =>
    (LinearEquiv.ofBijective n.pull1 h1).apply_symm_apply x
  apply (LinearEquiv.ofBijective n.pull2 h2).injective
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.ofBijective_apply, n.pullCohomologyTwo_cup, back, back, m.pullCohomologyTwo_cup]

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : AlgebraicGeometry.Scheme}
  {s : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R} {s' : X' ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R'} {σ : R →+* R'}
  {φ : X' ⟶ X}

theorem pullHO2_cup (h : φ ≫ s = s' ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) (a b : GlobalTheory.CechDR.HO1 s) :
    GlobalTheory.AbCoh.pullHO2 h (cup _ a b) = cup _ (GlobalTheory.CechDR.pullHO1 h a) (GlobalTheory.CechDR.pullHO1 h b) := by
  unfold GlobalTheory.AbCoh.pullHO2 GlobalTheory.CechDR.pullHO1 GlobalTheory.CechDR.pairResEquivO
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact pull_cup_of_bijective _ _ _ _ a b

theorem main : ∀ (R R' : Type) [inst : CommRing R] [inst_1 : CommRing R'] (X X' : AlgebraicGeometry.Scheme) (s : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (s' : X' ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : CategoryTheory.CategoryStruct.comp φ s = CategoryTheory.CategoryStruct.comp s' (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ)), Function.Surjective (⇑(GlobalTheory.CechDR.pullHO1 h) : GlobalTheory.CechDR.HO1 s → GlobalTheory.CechDR.HO1 s') → GlobalTheory.AbCoh.WedgeO (GlobalTheory.CechDR.OAff s') → Function.Surjective (⇑(GlobalTheory.AbCoh.pullHO2 h) : GlobalTheory.AbCoh.HO2 s → GlobalTheory.AbCoh.HO2 s') := by
  intro R R' _ _ X X' s s' σ φ h hsurj hwedge
  obtain ⟨e, he⟩ := hwedge

  have key : ∀ x, ∀ r : R', ∃ z, GlobalTheory.AbCoh.pullHO2 h z = e (r • x) := by
    intro x
    have hx : x ∈ Submodule.span R' (Set.range (exteriorPower.ιMulti R' 2)) := by
      rw [exteriorPower.ιMulti_span]
      trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      intro r
      obtain ⟨a, ha⟩ := hsurj (r • v 0)
      obtain ⟨b, hb⟩ := hsurj (v 1)
      refine ⟨cup _ a b, ?_⟩
      have hv : r • exteriorPower.ιMulti R' 2 v = exteriorPower.ιMulti R' 2 ![r • v 0, v 1] := by
        have hupd : (![r • v 0, v 1] : Fin 2 → _) = Function.update v 0 (r • v 0) := by
          funext i
          fin_cases i <;> simp
        rw [hupd, AlternatingMap.map_update_smul, Function.update_eq_self]
      rw [pullHO2_cup, ha, hb, hv, he]
    | zero =>
      intro r
      exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro r
      obtain ⟨z₁, h₁⟩ := hx r
      obtain ⟨z₂, h₂⟩ := hy r
      exact ⟨z₁ + z₂, by rw [map_add (f := _), h₁, h₂, smul_add, map_add (f := _)]⟩
    | smul c x _ hx =>
      intro r
      obtain ⟨z, hz⟩ := hx (r * c)
      exact ⟨z, by rw [hz, smul_smul]⟩
  intro y
  obtain ⟨z, hz⟩ := key (e.symm y) 1
  exact ⟨z, by rw [hz, one_smul, LinearEquiv.apply_symm_apply]⟩

end GlobalTheory.PullbackCupProduct
