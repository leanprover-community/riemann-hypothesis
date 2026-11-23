module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NonemptyEquivOfCardHom
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDualToInvariantDifferentials
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.exists_dual_to_invariant_differentials : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L), ∃ θ : Module.Dual R L →ₗ[R] omega (Γ.btOrder ⊤), (Function.Surjective θ ∧ ∀ (f : augIdeal (Γ.btOrder ⊤)) (w : Module.Dual R L), θ w = (augIdeal (Γ.btOrder ⊤)).toCotangent f ↔ Γ.IsDerAtOne i M N (f.1.1 : T → R) w) ∧ (∀ w, θ w = 0 ↔ ∃ u, w = N • u) ∧ ∀ (χ : T →* Rˣ) (w : Module.Dual R L), Γ.IsHT i M N χ w → θ w = dlogChar (Γ.btOrder ⊤) χ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.omega_isDerAtOne | exact GlobalTheory.CompanionTheory.Ar.BT.omega_isDerAtOne | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.omega_isDerAtOne <;> assumption)
