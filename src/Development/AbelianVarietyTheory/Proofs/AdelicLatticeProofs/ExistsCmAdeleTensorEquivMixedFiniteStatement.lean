module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCmAdeleTensorEquivMixedFinite
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_cm_adele_tensor_equiv_mixed_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) → letI : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E); ∃ Φ : AdeleRing (𝓞 F) F ⊗[F] E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E), (∀ x : E, Φ (1 ⊗ₜ[F] x) = (mixedEmbedding E x, algebraMap E _ x)) ∧ (∀ y, Algebra.TensorProduct.map (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (AlgHom.id F E) y ∈ AddSubgroup.closure {y : FiniteAdeleRing (𝓞 F) F ⊗[F] E | ∃ a ∈ {a : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F}, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (ε : AdeleRing (𝓞 F) F), ε.1 = 0 → ε.2 v = 1 → (∀ v', v' ≠ v → ε.2 v' = 0) → (Φ (ε ⊗ₜ[F] 1)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (ε ⊗ₜ[F] 1)).2 P = if P.under (𝓞 F) = v then 1 else 0) ∧ Continuous Φ.symm ∧ ∀ x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)ˣ, (x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)).2 = 1 → (∀ w, ((x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)).1.2 w).im = 0) → ∃ a : (AdeleRing (𝓞 F) F)ˣ, Φ ((a : AdeleRing (𝓞 F) F) ⊗ₜ[F] 1) = x := by
  first | exact @GlobalTheory.AdeleCM.exists_adele_tensor_equiv | exact GlobalTheory.AdeleCM.exists_adele_tensor_equiv | (intros; apply GlobalTheory.AdeleCM.exists_adele_tensor_equiv <;> assumption)
