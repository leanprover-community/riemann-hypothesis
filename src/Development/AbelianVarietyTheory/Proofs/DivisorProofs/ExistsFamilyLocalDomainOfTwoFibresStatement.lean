module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFamilyLocalDomainOfTwoFibres
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_family_localDomain_of_twoFibres : ∀ g n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [Field o] [CharZero o] (ζ : oˣ) (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W] (β : o →+* W) (v : (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) → W) (K₀ K₁ : Type) [Field K₀] [IsAlgClosed K₀] [Field K₁] [IsAlgClosed K₁] (i₀ : W →+* K₀) (i₁ : W →+* K₁), (∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁) → ∀ (P₀ : PolAV (Sp K₀)) (P₁ : PolAV (Sp K₁)) (h₀ : P₀.g = g) (h₁ : P₁.g = g) (l₀ : Out.Level P₀ ((n ^ j) ^ 2) (unitOn (Units.map (i₀.comp β).toMonoidHom ζ))) (l₁ : Out.Level P₁ ((n ^ j) ^ 2) (unitOn (Units.map (i₁.comp β).toMonoidHom ζ))), (IsThetaPt P₀ (n ^ j) (levelPoint l₀ h₀) fun a => fnOf (i₀ (v a))) → (IsThetaPt P₁ (n ^ j) (levelPoint l₁ h₁) fun a => fnOf (i₁ (v a))) → ∃ (P : PolAV (Sp W)) (pt : (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) → (baseOver (Sp W) ⟶ P.A)) (φ₀ : P₀.A.left ⟶ P.A.left) (φ₁ : P₁.A.left ⟶ P.A.left), P.g = g ∧ (∀ a, pt a ^ ((n ^ j) ^ 2) = 1) ∧ IsGrpPullback P₀.A P.A (spMap i₀) φ₀ ∧ IsGrpPullback P₁.A P.A (spMap i₁) φ₁ ∧ LBIso P₀.L (P.L.pull φ₀) ∧ LBIso P₁.L (P.L.pull φ₁) ∧ (∀ a, (levelPoint l₀ h₀ a).left ≫ φ₀ = spMap i₀ ≫ (pt a).left) ∧ ∀ a, (levelPoint l₁ h₁ a).left ≫ φ₁ = spMap i₁ ≫ (pt a).left := by
  first | exact @GlobalTheory.MBLow.exists_family_of_two_fibres | exact GlobalTheory.MBLow.exists_family_of_two_fibres | (intros; apply GlobalTheory.MBLow.exists_family_of_two_fibres <;> assumption)
