module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

structure Match (U : PreU I D.toPre A G) (U' : UnifPre I D A G) : Prop where
  gen : U'.gen = U.gen
  LG : U'.LG = U.P.L
  cub : HEq U'.cubG U.P.c
  sym : HEq U'.symG U.P.sym
  gt : U'.gt = U.gt
  w : HEq U'.w U.w

def SameG {L : LB G.left} {k : ℕ} (σ : H0 L k)
    (σ' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => (snd (𝟙_ (Over (Spec (CommRingCat.of R)))) G).left) (fun _ => (k : ℤ)))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of R))) ⊗ G).left) (z : Z) (J), Good L z J →
    sval σ' r z J = sval σ (r ≫ (snd _ G).left) z J

def SameB {D : DegPre R} {k : ℕ} (f : ∀ α, D.SecB k α) (f' : ∀ α, SecBT D (𝟙_ _) k α) : Prop :=
  ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of R))) ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J →
    sval (f' α) r z J = sval (f α) (r ≫ (snd _ D.P.A).left) z J

def PreU.SameK {D : DegPre R} (U : PreU I D A G) {k : ℕ}
    (σ : LB.Sec (LB.LinComb U.P.L.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ))))
    (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) (FractionRing R)))) : Prop :=
  ∀ (Z : Scheme.{0}) (rA : Z ⟶ (TFK (R := R) (FractionRing R) ⊗ A.A).left) (y : Z ⟶ ((Over.pullback (jK R)).obj G).left),
    rA ≫ (snd _ A.A).left = y ≫ U.gen.hom.left → ∀ (z : Z) (JA) (JG), Good A.L z JA → Good U.P.L.L z JG →
      (gw U.wA y z (JG (y ≫ pullback.fst G.hom (jK R))) (fun _ => JA (y ≫ U.gen.hom.left))).val ^ k *
          sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) (FractionRing R)) A.A).left) (ε := fun _ => (k : ℤ)) t rA z JA =
        sval σ y z JG
end GlobalTheory.UU
end
