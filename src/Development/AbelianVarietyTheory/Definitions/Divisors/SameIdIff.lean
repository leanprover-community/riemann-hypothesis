module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

variable {S : Scheme.{0}} (A : Over S)

def Same {T U Y : Over S} (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (y : Y ⟶ T) (u : Y ⟶ U) : Prop :=
  LBIso (ev N (fst A Y) (snd A Y ≫ y)) (ev M (fst A Y) (snd A Y ≫ u))

def Inj {U : Over S} (M : LB (A ⊗ U).left) : Prop :=
  ∀ (Y : Over S) (u u' : Y ⟶ U), Same A M M u u' → u = u'

def FibInj {U : Over S} (M : LB (A ⊗ U).left) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (Y : Over S) (_ : Y ⟶ Over.mk s) (u u' : Y ⟶ U),
    Same A M M u u' → u = u'

def ChartAt {U T : Over S} (M : LB (A ⊗ U).left) (N : LB (A ⊗ T).left) : Prop :=
  ∃ W : T.left.Opens, ∀ (Y : Over S) (y : Y ⟶ T), (∃ u : Y ⟶ U, Same A N M y u) ↔ ∀ z, y.left z ∈ W

structure Good (g : ℕ) {X Y : Scheme.{0}} (f : X ⟶ Y) : Prop where
  proper : IsProper f
  smooth : SmoothOfRelativeDimension g f
  conn : GeometricallyConnected f

def FinAff (X : Scheme.{0}) : Prop :=
  ∀ F : Finset X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U

def DimLe (B : Over S) : Prop :=
  ∀ (g : ℕ) (T : Scheme.{0}) (t : T ⟶ S),
    SmoothOfRelativeDimension g (pullback.snd A.hom t) → SmoothOfRelativeDimension g (pullback.snd B.hom t)

variable [GrpObj A]

structure Fam {T : Over S} (N : LB (A ⊗ T).left) : Prop where
  isLB : N.IsLB
  add : IsAdditive N

structure IsChart {U : Over S} (M : LB (A ⊗ U).left) : Prop where
  fam : Fam A M
  inj : Inj A M
  chart : ∀ (T : Over S) (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N

structure Rep {B S' : Over S} (b : B ⟶ S') (P : LB (A ⊗ B).left) : Prop where
  fam : Fam A P
  univ : ∀ (T : Over S) (t : T ⟶ S') (N : LB (A ⊗ T).left), Fam A N →
    ∃! x : T ⟶ B, x ≫ b = t ∧ LBIso N (ev P (fst A T) (snd A T ≫ x))

def HasRep (g : ℕ) (S' : Over S) : Prop :=
  ∃ (B : Over S) (b : B ⟶ S') (P : LB (A ⊗ B).left), Rep A b P ∧ Good g b.left

def HasRepAF (g : ℕ) (S' : Over S) : Prop :=
  ∃ (B : Over S) (b : B ⟶ S') (P : LB (A ⊗ B).left), Rep A b P ∧ Good g b.left ∧ FinAff B.left

def LiftAt (g : ℕ) {B S' : Over S} (b : B ⟶ S') (P : LB (A ⊗ B).left) (x : B.left) : Prop :=
  ∃ (U : Over S) (M : LB (A ⊗ U).left) (j : U ⊗ S' ⟶ B), Fam A M ∧ SmoothOfRelativeDimension g U.hom ∧
    j ≫ b = snd U S' ∧ IsOpenImmersion j.left ∧ x ∈ Set.range j.left ∧ Same A M P (fst U S') j

variable {A}


omit [GrpObj A] in
theorem same_id_iff {T U : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    (u : T ⟶ U) : Same A N M (𝟙 T) u ↔ LBIso N (ev M (fst A T) (snd A T ≫ u)) := by
  rw [Same, ← cls_eq_iff (pull_isLB hN _) (pull_isLB hM _), ← cls_eq_iff hN (pull_isLB hM _), cls_ev hN, evc,
    Category.comp_id, lift_fst_snd, Over.id_left, pull_id]


omit [GrpObj A] in
theorem same_iff {T U Y : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    (y : Y ⟶ T) (u : Y ⟶ U) :
    Same A N M y u ↔ evc hN (fst A Y) (snd A Y ≫ y) = evc hM (fst A Y) (snd A Y ≫ u) :=
  (cls_eq_iff (pull_isLB hN _) (pull_isLB hM _)).symm

end GlobalTheory.DualCon
