module

public import Development.EtaleCohomology.EtaleSheaves.CoverCut
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
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut

namespace LateralTheory.E.ProEqvPf

def fm {A : Type} [CommRing A] [IsLocalRing A] {U Y : Scheme.{0}} (u : U ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of A)) :
    pullback (u ≫ g) (cpt A) ⟶ pullback g (cpt A) :=
  pullback.map _ _ _ _ u (𝟙 _) (𝟙 _) (by simp) (by simp)

def Hit (q : ℕ) (i n : ℤ) {A : Type} [CommRing A] [IsLocalRing A] {U Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A))
    (z : Ht q (sch.obj (pullback g (cpt A))) n i) (u : U ⟶ Y) : Prop :=
  ∃ w : Ht q (sch.obj U) n i, pull _ (sch.map (pullback.fst (u ≫ g) (cpt A))) _ _ w = pull _ (sch.map (fm u g)) _ _ z

def PiLocalization₂ : Prop := LateralTheory.E.t_E2Cut.Cont → Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)) (y : Y) {J : Type}
  [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y),
  ClopenSys y D c ι → (∀ j, PB q i ((c.π.app j ≫ ι j) ≫ g)) → ∀ n : ℤ,
  (∀ x : Ht q (sch.obj Y) n i, pull _ (sch.map (pullback.fst g (cpt A))) _ _ x = 0 → ∃ j, pull _ (sch.map (ι j)) _ _ x = 0) ∧
  ∀ z : Ht q (sch.obj (pullback g (cpt A))) n i, ∃ j, Hit q i n g z (ι j)

def Glue : Prop := MV → Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)) (n : ℤ),
  (∀ x : Ht q (sch.obj Y) n i, pull _ (sch.map (pullback.fst g (cpt A))) _ _ x = 0 → ∀ y : Y,
    ∃ (U : Scheme.{0}) (u : U ⟶ Y), IsOpenImmersion u ∧ IsClosedImmersion u ∧ y ∈ Set.range u ∧ pull _ (sch.map u) _ _ x = 0) →
  (∀ z : Ht q (sch.obj (pullback g (cpt A))) n i, ∀ y : Y,
    ∃ (U : Scheme.{0}) (u : U ⟶ Y), IsOpenImmersion u ∧ IsClosedImmersion u ∧ y ∈ Set.range u ∧ Hit q i n g z u) →
  Function.Bijective (pull _ (sch.map (pullback.fst g (cpt A))) (tw q i) n)

theorem ProEqv_of (hC : LateralTheory.E.t_E2Cut.Cont) (hM : MV) (hS : PiLocalization₂) (hG : Glue) : ProEqv := by
  intro H q i A _ _ hq Y _ _ g hY n
  refine hG hM H q i A hq g n (fun x hx y => ?_) (fun z y => ?_)
  · obtain ⟨J, _, _, D, c, ι, hc, hp⟩ := hY y
    obtain ⟨j, hj⟩ := (hS hC H q i A hq g y D c ι hc hp n).1 x hx
    exact ⟨_, ι j, (hc.2.1 j).1, (hc.2.1 j).2.1, (hc.2.1 j).2.2, hj⟩
  · obtain ⟨J, _, _, D, c, ι, hc, hp⟩ := hY y
    obtain ⟨j, hj⟩ := (hS hC H q i A hq g y D c ι hc hp n).2 z
    exact ⟨_, ι j, (hc.2.1 j).1, (hc.2.1 j).2.1, (hc.2.1 j).2.2, hj⟩

end LateralTheory.E.ProEqvPf
