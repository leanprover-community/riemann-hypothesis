module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import Mathlib.Algebra.DualNumber
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace ReciprocityTheory.ChartRestriction.G.Pdiv

open ReciprocityTheory.ChartRestriction.G.Semi

section Points

variable (O : Type) [CommRing O]

abbrev specO (R : Type) [CommRing R] [Algebra O R] : Over (Spec (CommRingCat.of O)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap O R)))

variable {O}

def ptMap {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (φ : R →ₐ[O] R') : specO O R' ⟶ specO O R :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    simp only [Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    exact φ.commutes a)

def dualBC {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (φ : R →ₐ[O] R') : DualNumber R →ₐ[O] DualNumber R' :=
  TrivSqZeroExt.lift ((TrivSqZeroExt.inlAlgHom O R' R').comp φ)
    (((TrivSqZeroExt.inrHom R' R').restrictScalars O).comp φ.toLinearMap)
    (fun x y => by simp)
    (fun r x => by ext <;> simp [mul_comm])
    (fun r x => by ext <;> simp [mul_comm])

def dualScale (a : O) : DualNumber O →ₐ[O] DualNumber O :=
  TrivSqZeroExt.map (a • LinearMap.id)

def unitOf {R : Type} [CommRing R] [Algebra O R] (w : specO O R ⟶ Gm (Spec (CommRingCat.of O))) :
    Rˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom
    (res (fun x _ => show w.left.base x ∈ (⊤ : (Gm (Spec (CommRingCat.of O))).left.Opens)
        from trivial)
      (pullU w.left ⊤ (charUnit (Spec (CommRingCat.of O)) (ULift ℤ) (ULift.up 1))))

end Points

section Tangent

variable {O : Type} [CommRing O] (G : Over (Spec (CommRingCat.of O))) [GrpObj G]

def LieG : Type :=
  {x : specO O (DualNumber O) ⟶ G //
    ptMap (TrivSqZeroExt.fstHom O O O) ≫ x = toUnit (specO O O) ≫ η[G]}

def omega : Submodule O (LieG G → O) where
  carrier := {f | (∀ (x y : LieG G) (h : ptMap (TrivSqZeroExt.fstHom O O O) ≫ (x.1 * y.1) =
        toUnit (specO O O) ≫ η[G]), f ⟨x.1 * y.1, h⟩ = f x + f y) ∧
      (∀ (a : O) (x : LieG G) (h : ptMap (TrivSqZeroExt.fstHom O O O) ≫
        (ptMap (dualScale a) ≫ x.1) = toUnit (specO O O) ≫ η[G]),
        f ⟨ptMap (dualScale a) ≫ x.1, h⟩ = a * f x)}
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    exact ⟨fun x y h => by
        show f _ + g _ = (f x + g x) + (f y + g y)
        rw [hf1 x y h, hg1 x y h]; ring,
      fun a x h => by
        show f _ + g _ = a * (f x + g x)
        rw [hf2 a x h, hg2 a x h]; ring⟩
  zero_mem' := ⟨fun _ _ _ => show (0 : O) = 0 + 0 by simp,
    fun a _ _ => show (0 : O) = a * 0 by simp⟩
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    exact ⟨fun x y h => by
        show c * f _ = c * f x + c * f y
        rw [hf1 x y h]; ring,
      fun a x h => by
        show c * f _ = a * (c * f x)
        rw [hf2 a x h]; ring⟩

def IsCharTors (N : ℕ) (f : torsion G N ⟶ Gm (Spec (CommRingCat.of O))) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of O))) (x y z : T ⟶ torsion G N),
    z ≫ torsion.ι G N = (x ≫ torsion.ι G N) * (y ≫ torsion.ι G N) →
      z ≫ f = (x ≫ f) * (y ≫ f)

variable (p : ℕ)

structure Tv where

  χ : ∀ n : ℕ, torsion G (p ^ n) ⟶ Gm (Spec (CommRingCat.of O))
  isChar : ∀ n, IsCharTors G (p ^ n) (χ n)
  compat : ∀ (n : ℕ) (T : Over (Spec (CommRingCat.of O))) (x : T ⟶ torsion G (p ^ n))
    (y : T ⟶ torsion G (p ^ (n + 1))), x ≫ torsion.ι G (p ^ n) = y ≫ torsion.ι G (p ^ (n + 1)) →
      x ≫ χ n = y ≫ χ (n + 1)

variable {G p}

def IsAl (χ : Tv G p) (f : LieG G → O) : Prop :=
  ∀ (n : ℕ) (R : Type) [CommRing R] [Algebra O R], (p : R) ^ n = 0 →
    ∀ (x : LieG G) (w : specO O (DualNumber R) ⟶ torsion G (p ^ n)),
      w ≫ torsion.ι G (p ^ n) = ptMap (dualBC (Algebra.ofId O R)) ≫ x.1 →
        (unitOf (w ≫ χ.χ n) : DualNumber R) =
          TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (algebraMap O R (f x))

variable (G p)

def htSpan : Submodule O (LieG G → O) :=
  Submodule.span O {f | f ∈ omega G ∧ ∃ χ : Tv G p, IsAl χ f}

end Tangent

section Statements

def HTChar (p : ℕ) {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O]
    [Algebra O C] (G : Over (Spec (CommRingCat.of O))) [GrpObj G] : Prop :=
  ∀ c : O, v (algebraMap O C c) ^ (p - 1) ≤ v (p : C) →
    ∀ f ∈ omega G, c • f ∈ htSpan G p

end Statements

end ReciprocityTheory.ChartRestriction.G.Pdiv
