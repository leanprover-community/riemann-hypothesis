module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FormalOrigin

def iterOp {A : Type} {n : ℕ} (ds : Fin n → A → A) (α : Fin n →₀ ℕ) (f : A) : A :=
  (List.finRange n).foldr (fun i g => (ds i)^[α i] g) f

def taylor {A B : Type} [CommRing A] [CommRing B] [Algebra ℚ B] {n : ℕ} (ev : A →+* B) (ds : Fin n → A → A)
    (f : A) : MvPowerSeries (Fin n) B :=
  fun α => (∏ i, ((α i).factorial : ℚ))⁻¹ • ev (iterOp ds α f)

section Origin
variable {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]

def origin : G.left := (η[G]).left (IsLocalRing.closedPoint R)

def evO : G.left.presheaf.stalk (origin G) →+* R :=
  (Scheme.stalkClosedPointTo (R := CommRingCat.of R) (η[G]).left).hom

def constO : R →+* G.left.presheaf.stalk (origin G) :=
  (G.left.presheaf.germ ⊤ (origin G) trivial).hom.comp
    ((G.hom.appLE ⊤ ⊤ (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
end Origin

def intDer {S A : Type} [CommRing S] [CommRing A] [Algebra S A] (δ : Derivation S A A) : Derivation ℤ A A where
  toFun := δ
  map_add' := map_add δ
  map_smul' m x := by simpa using map_zsmul δ m x
  map_one_eq_zero' := δ.map_one_eq_zero
  leibniz' := δ.leibniz

theorem iterOp_zero {A : Type} {n : ℕ} (ds : Fin n → A → A) (f : A) : iterOp ds 0 f = f := by
  unfold iterOp
  induction (List.finRange n) with
  | nil => rfl
  | cons i l ih => simpa using ih
end GlobalTheory.FormalOrigin
