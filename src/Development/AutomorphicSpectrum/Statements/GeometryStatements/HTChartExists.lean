module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasValues
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsCompactUnitaryPointsAtPlaceFstMemCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
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

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField

def IsHTChartOf {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] {E : Type} [Field E] [NumberField E]
    {c : E ≃+* E} {p n N : ℕ} {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module R Ω] [IsScalarTower R K Ω]
    (D : HT.HTChart R K c p n N Ω) {T : Type} [CommGroup T] (Γ : QFGroup R T) {S : Scheme.{0}} {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} (i : Γ.G.left ⟶ G.left) {L : Type} [AddCommGroup L] [Module R L]
    (M : LieModel G x L) (ρ : 𝓞 E →+* Module.End R L) (j : Module.Dual R L →ₗ[R] Ω)
    (π : Multiplicative (Fin N → 𝓞 E) →* T) (ζ : Rˣ) : Prop :=
  D.om = LinearMap.range j ∧
  (∀ a w, D.ρΩ a (j w) = j (w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))) ∧
  ∀ y, ∃ (χ : T →* Rˣ) (w : Module.Dual R L), (∀ z, χ (π (Multiplicative.ofAdd z)) = ζ ^ (D.e y z).val) ∧
    D.h y = j w ∧ Γ.IsHT i M (p ^ n) χ w

def HTChartExists : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] [CharZero R] [Field K]
    [Algebra R K] [IsFractionRing R K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (p n N : ℕ) [Fact p.Prime]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G]
    (x : Spec (CommRingCat.of R) ⟶ S) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x (p ^ n) i → Smooth G.hom →
    ∀ (act : 𝓞 E → (G ⟶ G)), (∀ a, IsMonHom (act a)) →
    ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (ρ : 𝓞 E →+* Module.End R L), M.IsActOf act ρ →
    ∀ (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module R Ω] [IsScalarTower R K Ω] (j : Module.Dual R L →ₗ[R] Ω),
      IsBaseChange K j →
    ∀ (π : Multiplicative (Fin N → 𝓞 E) →* T), Function.Surjective π →
      (∀ y, π (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = (p ^ n) • y') →
      (∀ (a : 𝓞 E) y, (Γ.pt (π (Multiplicative.ofAdd (a • y)))).left ≫ i =
        (Γ.pt (π (Multiplicative.ofAdd y))).left ≫ i ≫ (act a).left) →
    ∀ (ζ : Rˣ), ζ ^ (p ^ n) = 1 →
    ∀ (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ n)), (∀ y, e y y = 0) →
      (∀ (a : 𝓞 E) (y z : Fin N → 𝓞 E), e (a • y) z = e y (RingOfIntegers.mapRingEquiv c a • z)) →
      (∀ φ : (Fin N → 𝓞 E) →+ ZMod (p ^ n), ∃ y, e y = φ) → (∀ y, e y = 0 → ∃ y', y = (p ^ n) • y') →
    ∃ D : HT.HTChart R K c p n N Ω, D.e = e ∧ IsHTChartOf D Γ i M ρ j π ζ

end GlobalTheory.CompanionTheory.Ar.BT
