module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisEquivariantTorsionValuesUltrametric
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.galois_equivariant_torsion_values_ultrametric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → GalEqN n lab → (∀ (j : ℕ) (v : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → Kb R), (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → QkPt D.toPre C ((n ^ j) ^ 2)) (q : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → N.QT ((n ^ j) ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx (n ^ j) (q i)) → IsThetaPt A (n ^ j) (lab ((n ^ j) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p))) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∃ hD : IsPullDeg φ D.toPre D'.toPre, ∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (_ : Algebra (FractionRing R) C) (em : Kb R →ₐ[FractionRing R] C), (∀ r, algebraMap (FractionRing R) C (algebraMap R _ r) = algebraMap (FractionRing W) C (algebraMap W _ (φ r))) ∧ ∀ j : ℕ, ∀ (p : QkPt D.toPre (Kb R) (n ^ j)) (p₁ : QkPt D.toPre C (n ^ j)) (p' : QkPt D'.toPre C (n ^ j)) (x' : TFK (R := W) C ⟶ A'.A), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD C p₁.g p'.g → x'.left ≫ a = spMap em.toRingHom ≫ (lab (n ^ j) p).left → QkToAkU U'.toUnifPre C (n ^ j) p' x' := by
  first | exact @GlobalTheory.Mum.Recog.recognition_core | exact GlobalTheory.Mum.Recog.recognition_core | (intros; apply GlobalTheory.Mum.Recog.recognition_core <;> assumption)
