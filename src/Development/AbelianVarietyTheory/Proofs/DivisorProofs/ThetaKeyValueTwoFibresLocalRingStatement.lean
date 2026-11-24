module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyValueTwoFibresLocalRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaKeyValue_two_fibres_local_ring : ∀ κ : Rule, Rule4 κ → ∀ (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W] [IsIntegrallyClosed W] [CharZero W] (K₀ K₁ : Type) [Field K₀] [CharZero K₀] [Field K₁] [IsAlgClosed K₁] [CharZero K₁] (i₀ : W →+* K₀) (i₁ : W →+* K₁), Function.Injective i₀ → (∀ a, i₁ a ≠ 0 → IsUnit a) → ∀ (P : PolAV (Sp W)) (x₀ : KeyIn K₀) (x₁ : KeyIn K₁) (g : ℕ) (h₀ : x₀.P.g = g) (h₁ : x₁.P.g = g) (m : ℕ), P.g = g → Odd m → 3 ≤ m → ∀ (I : Type) (pt : I → (baseOver (Sp W) ⟶ P.A)) (p₀ : I → (baseOver (Sp K₀) ⟶ x₀.P.A)) (p₁ : I → (baseOver (Sp K₁) ⟶ x₁.P.A)) (φ₀ : x₀.P.A.left ⟶ P.A.left) (φ₁ : x₁.P.A.left ⟶ P.A.left), (∀ a, pt a ^ (m ^ 2) = 1) → IsGrpPullback x₀.P.A P.A (spMap i₀) φ₀ → IsGrpPullback x₁.P.A P.A (spMap i₁) φ₁ → LBIso x₀.P.L (P.L.pull φ₀) → LBIso x₁.P.L (P.L.pull φ₁) → (∀ a, (p₀ a).left ≫ φ₀ = spMap i₀ ≫ (pt a).left) → (∀ a, (p₁ a).left ≫ φ₁ = spMap i₁ ≫ (pt a).left) → (∀ z : baseOver (Sp K₁) ⟶ x₁.P.A, z ^ (m ^ 2) = 1 → ∃ a, p₁ a = z) → ∀ (ϑ : I → W) (J : I → Fin g → W) (k : W), ThJet x₀ h₀ m p₀ (fun a => i₀ (ϑ a)) (fun a j => i₀ (J a j)) → ThJet x₁ h₁ m p₁ (fun a => i₁ (ϑ a)) (fun a j => i₁ (J a j)) → (κ K₀ x₀ : K₀) = i₀ k → (κ K₁ x₁ : K₁) = i₁ k := by
  first | exact @GlobalTheory.MBLow.keyValue_twoFibres | exact GlobalTheory.MBLow.keyValue_twoFibres | (intros; apply GlobalTheory.MBLow.keyValue_twoFibres <;> assumption)
