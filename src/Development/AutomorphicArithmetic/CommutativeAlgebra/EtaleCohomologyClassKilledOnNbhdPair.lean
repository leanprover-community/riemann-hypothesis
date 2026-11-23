module

public import Development.EtaleCohomology.EtaleSheaves.NeighbourhoodKilling
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits

namespace UpperTheory.NaturalityElementwise

variable {J : Type} [SmallCategory J]

private lemma sq_el {A B C D : AddCommGrpCat.{1}} {p : A ⟶ B} {q : B ⟶ D} {r : A ⟶ C} {s : C ⟶ D}
    (h : p ≫ q = r ≫ s) (x : A) : q.hom (p.hom x) = s.hom (r.hom x) := by
  have := congrArg (fun g => g.hom x) h
  simpa using this

private lemma nat_el {F G : J ⥤ AddCommGrpCat.{1}} (η : F ⟶ G) {a b : J} (f : a ⟶ b) (x : F.obj a) :
    (η.app b).hom ((F.map f).hom x) = (G.map f).hom ((η.app a).hom x) :=
  sq_el (η.naturality f) x

private lemma w_el {F : J ⥤ AddCommGrpCat.{1}} (c : Cocone F) {a b : J} (f : a ⟶ b) (x : F.obj a) :
    (c.ι.app b).hom ((F.map f).hom x) = (c.ι.app a).hom x := by
  have := congrArg (fun g => g.hom x) (c.w f)
  simpa using this

private lemma comp_el {F : J ⥤ AddCommGrpCat.{1}} {a b c : J} (f : a ⟶ b) (g : b ⟶ c) (x : F.obj a) :
    (F.map (f ≫ g)).hom x = (F.map g).hom ((F.map f).hom x) := by
  simp

end UpperTheory.NaturalityElementwise

open UpperTheory.NaturalityElementwise in
theorem UpperTheory.etaleCohomology_class_killed_on_nbhd_pair :
    LateralTheory.E.NeighbourhoodKilling.PairFive := by
  intro J _ _ T j x hx

  have h0 : (T.cYm.ι.app j).hom ((T.fg.app j).hom x) = 0 := by
    rw [← sq_el (T.fg_w j) x, hx, map_zero]
  obtain ⟨j1, f1, h1⟩ := T.injYm j _ h0

  have h2 : (T.fg.app j1).hom ((T.Rm.map f1).hom x) = 0 := by
    rw [nat_el T.fg f1 x, h1]
  obtain ⟨w, hw⟩ := T.exR j1 _ h2

  have h3 : T.dlL.hom ((T.cWp.ι.app j1).hom w) = 0 := by
    rw [sq_el (T.dl_w j1) w, hw, w_el T.cR f1 x, hx]
  obtain ⟨y, hy⟩ := T.exWL _ h3
  obtain ⟨j2, y', rfl⟩ := T.surYp y

  let a : j1 ⟶ IsFiltered.max j1 j2 := IsFiltered.leftToMax j1 j2
  let b : j2 ⟶ IsFiltered.max j1 j2 := IsFiltered.rightToMax j1 j2
  have h4 : (T.cWp.ι.app _).hom ((T.Wp.map a).hom w - (T.rs.app _).hom ((T.Yp.map b).hom y')) = 0 := by
    rw [map_sub, w_el T.cWp a w, ← sq_el (T.rs_w _) ((T.Yp.map b).hom y'), w_el T.cYp b y', hy,
      sub_self]
  obtain ⟨j4, c, h5⟩ := T.injWp _ _ h4
  refine ⟨j4, f1 ≫ a ≫ c, ?_⟩
  have h6 : (T.Wp.map c).hom ((T.Wp.map a).hom w)
      = (T.rs.app j4).hom ((T.Yp.map c).hom ((T.Yp.map b).hom y')) := by
    rw [map_sub, sub_eq_zero] at h5
    rw [h5, nat_el T.rs c]
  rw [comp_el, ← hw, comp_el, ← nat_el T.dl a w, ← nat_el T.dl c, h6]
  exact T.cx j4 _
