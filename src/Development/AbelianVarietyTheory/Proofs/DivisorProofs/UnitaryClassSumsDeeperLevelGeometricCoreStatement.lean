module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassSumsDeeperLevelGeometricCore
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.unitary_classSums_deeper_level_geometric_core : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra X₁.Ω₁ Ω₂) (_ : FiniteDimensional X₁.Ω₁ Ω₂) (_ : IsGalois X₁.Ω₁ Ω₂), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra; ∀ 𝔷 : Ideal (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.IsMaximal → ∀ ev' : Φ.Y → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) →+* PadicAlgCl p, (∀ y a, ev' y (algebraMap (X₁.M.Z.presheaf.stalk z₁) (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) a) = Φ.ev y a) → (∀ y b, ‖ev' y b‖ ≤ 1) → (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) → ∃ (k : ∀ y, Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y) (Q : Type) (F : (Fin 1 → Φ.X y₀) → Q → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂)), k y₀ = LinearEquiv.refl (𝓞 E) (Φ.X y₀) ∧ (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → F c κ = F c' κ) ∧ (∀ y c κ (μ : Fin 1 → Φ.X y), (∀ u, CongMod N (μ u) (k y (c u))) → (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → qW !![(1 : ℤ)] (Φ.β y) μ ≤ qW !![(1 : ℤ)] (Φ.β y) μ') → ‖ev' y (F c κ)‖ ≤ Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β y) μ) / 2)) ∧ (∀ y (μ : Fin 1 → Φ.X y), (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → μ' ≠ μ → qW !![(1 : ℤ)] (Φ.β y) μ < qW !![(1 : ℤ)] (Φ.β y) μ') → ∃ c κ, (∀ u, CongMod N (μ u) (k y (c u))) ∧ ‖ev' y (F c κ)‖ = Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β y) μ) / 2)) ∧ ∀ σ : (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[(X₁.M.Z.presheaf.stalk z₁)] (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y₀, (N : ℤ) ∣ LinearMap.det (γ.toLinearMap.restrictScalars ℤ) - 1 ∧ (∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x) ∧ ∀ c κ, σ (F c κ) = F (fun u => γ (c u)) κ := by
  first | exact @GlobalTheory.UPoinc.UCore.classSums_core | exact GlobalTheory.UPoinc.UCore.classSums_core | (intros; apply GlobalTheory.UPoinc.UCore.classSums_core <;> assumption)
