module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.CurveRootGeometry GlobalTheory.ConjSeq
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrobAdjoint

section Dual

open GlobalTheory.CechPic GlobalTheory.AbLaw

variable {S : Scheme.{0}} {A T Y : Over S} [GrpObj A] {P : LB (A ⊗ A).left}


end Dual

section Down

variable {R R' : Type} [CommRing R] [CommRing R'] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A']
  {σ : R →+* R'} {φ : A'.left ⟶ A.left}

def down (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) {Y : Over (Sp R')} (x : Y ⟶ A') :
    Over.mk (Y.hom ≫ spMap σ) ⟶ A :=
  Over.homMk (x.left ≫ φ) (by simp [m.w])

theorem down_mul (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) {Y : Over (Sp R')} (x y : Y ⟶ A') :
    down m (x * y) = down m x * down m y :=
  Over.OverMorphism.ext (m.mul Y x y (down m x) (down m y) rfl rfl).symm

end Down

section Frob

open GlobalTheory.CechPic GlobalTheory.AbLaw

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0) {A A₁ : Over (Sp R)} [GrpObj A] [GrpObj A₁]
  {π : A₁.left ⟶ A.left}

variable {G : PDivGroup p R} (t : G.TorsionTower A)

theorem absFrob_y (n : ℕ) : spMap ((absFrob hR G).app n).toRingHom ≫ (t.y n).left =
    (t.y n).left ≫ VB.frob A.left p (cast_left p R hR A) := by
  have h := natCast_eq_zero_of_algebra hR (G.A n)
  exact (congrArg (· ≫ (t.y n).left) (frob_sp p _ h (SS.FrobField.cast_zero_sp _ h)).symm).trans
    (VB.frob_naturality p _ (t.y n).left _)

theorem exists_tower (hπ : IsGrpPullback A₁ A (spMap (frobR p R hR)) π) :
    ∃ t₁ : (frobTwist hR G).TorsionTower A₁, ∀ n,
      spMap ((frobProj hR G).app n).toRingHom ≫ (t.y n).left = (t₁.y n).left ≫ π :=
  letI := (frobRing hR).toAlgebra
  ⟨t.baseChange (O' := R) hπ, t.toBase_y (O' := R) hπ⟩

theorem map_eq_verschiebung (t₁ : (frobTwist hR G).TorsionTower A₁)
    (ht : ∀ n, spMap ((frobProj hR G).app n).toRingHom ≫ (t.y n).left = (t₁.y n).left ≫ π)
    (F : A ⟶ A₁) (V : A₁ ⟶ A) [IsMonHom F] [IsMonHom V]
    (hF : F.left ≫ π = VB.frob A.left p (cast_left p R hR A)) (hV : F ≫ V = 𝟙 A ^ p) :
    t₁.map t V = verschiebung hR G := by
  have e : t.map t₁ F = relFrob hR G := frobTwist_hom_ext hR fun n a ↦
    (t₁.semiOf_semiOf t t (s' := SemiHom.ofHom (t.map t₁ F)) (s'' := absFrob hR G) (ψ := F.left) ht
      (fun n ↦ congrArg Over.Hom.left (t.map_y t₁ F n)) (fun n ↦ by rw [hF]; exact absFrob_y hR t n) n a).symm.trans
      ((absFrob_app hR G n a).trans (relFrob_app_frobProj hR n a).symm)
  have : IsMonHom (𝟙 A ^ p) := hV ▸ inferInstance
  refine eq_verschiebung_of_relFrob_comp hR ?_
  rw [← e, ← t.map_comp, t.map_congr t hV, t.map_pow_id]

end Frob

section Pairing

open GlobalTheory.CatCoh GlobalTheory.AbLaw

variable {R R' : Type} [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'} {S S' : Scheme.{0}}
  {κ : DividedPowers I} {t : S ⟶ Sp R} {A B : Over S} [GrpObj A] [GrpObj B]
  {κ' : DividedPowers I'} {t' : S' ⟶ Sp R'} {A' B' : Over S'} [GrpObj A'] [GrpObj B']

end Pairing

end GlobalTheory.FrobAdjoint
