module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsWeilChar
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.EigenSplit GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel

section AtPoint

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  {Λ : Type} [CommRing Λ] [StarRing Λ]

def IsOpenFiniteFlatSubgroup (G : Over (Sp O)) [GrpObj G] (N : ℕ) {H : Over (Sp O)}
    (j : H ⟶ torsion G N) : Prop :=
  IsOpenImmersion j.left ∧ IsFinite H.hom ∧ Flat H.hom ∧
    (∀ S : Over (Sp O), ∃ z : S ⟶ H, z ≫ j ≫ torsion.ι G N = 1) ∧
    (∀ (S : Over (Sp O)) (x y : S ⟶ H), ∃ z : S ⟶ H,
      z ≫ j ≫ torsion.ι G N = (x ≫ j ≫ torsion.ι G N) * (y ≫ j ≫ torsion.ι G N)) ∧
    (∀ (S : Over (Sp O)) (x : S ⟶ H), ∃ z : S ⟶ H,
      z ≫ j ≫ torsion.ι G N = (x ≫ j ≫ torsion.ι G N)⁻¹)

def IsCharacter (G : Over (Sp O)) [GrpObj G] (N : ℕ) {H : Over (Sp O)} (j : H ⟶ torsion G N)
    (χ : H ⟶ Gm (Sp O)) : Prop :=
  ∀ (S : Over (Sp O)) (x y z : S ⟶ H),
    z ≫ j ≫ torsion.ι G N = (x ≫ j ≫ torsion.ι G N) * (y ≫ j ≫ torsion.ι G N) →
      z ≫ χ = (x ≫ χ) * (y ≫ χ)

omit [Fact p.Prime] in
theorem isNilpotent_dual {R : Type} [CommRing R] {n : ℕ} (h : (p : R) ^ n = 0) :
    IsNilpotent (p : DualNumber R) :=
  ⟨n, by rw [← map_natCast (algebraMap R (DualNumber R)), ← map_pow, h, map_zero]⟩

variable [Algebra ℤ_[p] O] (P : Point p v O Λ)

def alLeft : P.T →ₗ[ℤ_[p]] omega P.Gt := -P.al₀

def LevelReduction : Prop :=
  ∀ (n : ℕ) (H : Over (Sp O)) (j : H ⟶ torsion P.G (p ^ n)),
    IsOpenFiniteFlatSubgroup P.G (p ^ n) j →
    ∀ (t : P.T) (χ : H ⟶ Gm (Sp O)), IsCharacter P.G (p ^ n) j χ →
      (∀ (w : specO O O ⟶ H) (z : Pts P.A.A),
        z.left ≫ P.gen = spMap (algebraMap O C) ≫ (w ≫ j ≫ torsion.ι P.G (p ^ n)).left →
          algebraMap O C (unitOf (w ≫ χ) : O) = (weil P.A (p ^ n) (t.lev n) z : C)) →
      ∀ (R : Type) [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0) (x : LieG P.Gt)
        (w : specO O (DualNumber R) ⟶ H),
        w ≫ j ≫ torsion.ι P.G (p ^ n) =
          P.cmp (DualNumber R) (isNilpotent_dual hR) (ptMap (dualBC (Algebra.ofId O R)) ≫ x.1) →
        (unitOf (w ≫ χ) : DualNumber R) =
          TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (algebraMap O R ((alLeft P t).1 x))


variable [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]

end AtPoint

end GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel
