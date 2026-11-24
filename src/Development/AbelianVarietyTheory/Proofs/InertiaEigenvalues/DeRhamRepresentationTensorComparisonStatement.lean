module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamRepresentationTensorComparison
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.de_rham_representation_tensor_comparison : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V₀ : Type) [AddCommGroup V₀] [Module ↥LL.1 V₀] [Module ℚ_[l] V₀] [IsScalarTower ℚ_[l] ↥LL.1 V₀] [FiniteDimensional ↥LL.1 V₀] (ρ₀ : Representation ↥LL.1 ↥(GK K) V₀) (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (V₂ : Type) [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂] [FiniteDimensional ↥LL.1 V₂] (ρ₂ : Representation ↥LL.1 ↥(GK K) V₂) (ι : V₀ →ₗ[↥LL.1] V₁) (π : V₁ →ₗ[↥LL.1] V₂), (∀ g x, ι (ρ₀ g x) = ρ₁ g (ι x)) → (∀ g x, π (ρ₁ g x) = ρ₂ g (π x)) → Function.Injective ι → Function.Surjective π → LinearMap.range ι = LinearMap.ker π → IsDR (P.PD K) ρ₁ → IsDR (P.PD K) ρ₀ ∧ IsDR (P.PD K) ρ₂ ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), finrank ↥LL.1 ↥(FildR (P.PD K) ρ₁ τ a) = finrank ↥LL.1 ↥(FildR (P.PD K) ρ₀ τ a) + finrank ↥LL.1 ↥(FildR (P.PD K) ρ₂ τ a) ∧ multV (P.PD K) ρ₁ τ a = multV (P.PD K) ρ₀ τ a + multV (P.PD K) ρ₂ τ a ∧ (IsJumpV (P.PD K) ρ₁ τ a ↔ IsJumpV (P.PD K) ρ₀ τ a ∨ IsJumpV (P.PD K) ρ₂ τ a) := by
  first | exact @GlobalTheory.Per.ExactMult.exact_hodge_add | exact GlobalTheory.Per.ExactMult.exact_hodge_add | (intros; apply GlobalTheory.Per.ExactMult.exact_hodge_add <;> assumption)
