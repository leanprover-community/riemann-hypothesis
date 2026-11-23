module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorShiftDivMonomial
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.heatOperator_shift_div_monomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ (e : ℕ), 1 ≤ e → ∀ (mu α : P.D.toPre.X) (N : Fin m → ℕ) (σ σ' : P.D.toPre.SecB e α) (σ₁ σ₁u σ₁' σ₁u' : P.D.toPre.SecB e (α + e • mu)), TActs Y h e α σ σ' → ShiftEq P.D.toPre e mu α σ σ₁ 0 σ₁ → ShiftEq P.D.toPre e mu α σ' σ₁' 0 σ₁' → (∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁ x z J = gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ N i)) * sval σ₁u x z J) → (∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁' x z J = gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ N i)) * sval σ₁u' x z J) → ∃ σ₁u'' : P.D.toPre.SecB e (α + e • mu), TActs Y h e (α + e • mu) σ₁u σ₁u'' ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁u'' x z J = sval σ₁u' x z J - gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (2 * (e : ChartRing k m d) * ∑ i, (N i : ChartRing k m d) * q i)) * sval σ₁u x z J := by
  first | exact @GlobalTheory.Heat.heat_div_monomial | exact GlobalTheory.Heat.heat_div_monomial | (intros; apply GlobalTheory.Heat.heat_div_monomial <;> assumption)
