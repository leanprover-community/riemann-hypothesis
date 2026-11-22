module

public import Mathlib
public import Formalism.LocalRingCardinality.DataDIV
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffineOpenAndIsPushout
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdjointEndomorphismsCubeLBOfDenseFibres
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic GlobalTheory.VB

namespace GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase

section Surface

variable (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)]

variable {T}

variable {k}

end Surface

section Abelian

variable {S S' : Scheme.{0}} (A : Over S)

def toBase (s : S' ⟶ S) {Y : Over S'} (x : Y ⟶ (Over.pullback s).obj A) :
    Over.mk (Y.hom ≫ s) ⟶ A :=
  Over.homMk (x.left ≫ pullback.fst A.hom s) (by
    have := Over.w x
    simp only [Over.mk_hom, Category.assoc, pullback.condition]
    rw [← this]; simp)

def sqToBase (s : S' ⟶ S) :
    ((Over.pullback s).obj A ⊗ (Over.pullback s).obj A).left ⟶ (A ⊗ A).left :=
  (lift (toBase A s (fst _ _)) (toBase A s (snd _ _))).left

variable [GrpObj A]

def IsPrincipalPol (c : Pic (A ⊗ A).left) : Prop :=
  pull (lift (1 : A ⟶ A) (𝟙 A)).left c = 0 ∧ pull (lift (𝟙 A) (1 : A ⟶ A)).left c = 0 ∧
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ S),
      ∃ (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB),
        Out.RelAmple ((Over.pullback s).obj A) L ∧ Out.KTriv ((Over.pullback s).obj A) L ∧
          pull (sqToBase A s) c = lam (cls L hL) (fst _ _) (snd _ _)

end Abelian

open Formalism.BasicNotions

end GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase
