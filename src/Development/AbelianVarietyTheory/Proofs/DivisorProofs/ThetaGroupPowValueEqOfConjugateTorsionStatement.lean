module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupPowValueEqOfConjugateTorsion
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportSymmetricLiftsThetaGroupTraitImports

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

theorem _root_.GlobalTheory.T.thetaGroup_powValue_eq_of_conjugate_torsion : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) (k : ℤ) (N : ℕ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : ∀ i : ℕ, f ≫ (translT A (θ.pt ^ i)).left = (translT A' (θ'.pt ^ i)).left ≫ f) (hN : θ'.pt ^ N = 1) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J' (hJ : Good L z J) (hJ' : Good L' z J'), val (powGen A L k θ N) (q ≫ f) z J = val (powGen A' L' k θ' N) q z J' := by
  first | exact @GlobalTheory.ThetaPowConj.val_powGen_transport | exact GlobalTheory.ThetaPowConj.val_powGen_transport | (intros; apply GlobalTheory.ThetaPowConj.val_powGen_transport <;> assumption)
