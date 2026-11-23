module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.Dil

def dilHomeo {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (M : ℕ) (u : Aˣ) :
    (Fin 1 → Fin M → A) ≃ₜ (Fin 1 → Fin M → A) where
  toFun X p k := (u : A) * X p k
  invFun X p k := ((u⁻¹ : Aˣ) : A) * X p k
  left_inv X := by
    funext p k
    simp
  right_inv X := by
    funext p k
    simp
  continuous_toFun := continuous_pi fun p => continuous_pi fun k =>
    continuous_const.mul ((continuous_apply k).comp (continuous_apply p))
  continuous_invFun := continuous_pi fun p => continuous_pi fun k =>
    continuous_const.mul ((continuous_apply k).comp (continuous_apply p))

theorem linearIndependent_dil {A : Type} [CommRing A] {M : ℕ} (u : Aˣ) (X : Fin 1 → Fin M → A)
    (hX : LinearIndependent A X) :
    LinearIndependent A (fun (p : Fin 1) (k : Fin M) => (u : A) * X p k) := by
  rw [Fintype.linearIndependent_iff] at hX ⊢
  intro g hg i
  have h0 : ∑ i, (g i * (u : A)) • X i = 0 := by
    funext k
    have := congrFun hg k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h1 := hX (fun i => g i * (u : A)) h0 i
  exact (Units.mul_left_eq_zero u).1 h1

theorem dil_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (v : HeightOneSpectrum (𝓞 F)) (u : (Fv F v ⊗[F] E)ˣ) (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsCompact P → IsOpen P → P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} → IsCompact ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P) ∧ IsOpen ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P) ∧ (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} := by
  intro F E _ _ _ _ _ σ _ M v u P hc ho hP
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := TopK.isTopRing (Fv F v)
  refine ⟨hc.image (dilHomeo M u).continuous, (dilHomeo M u).isOpenMap _ ho, ?_⟩
  rintro _ ⟨X, hX, rfl⟩
  exact linearIndependent_dil u X (hP hX)

end GlobalTheory.CompanionTheory.WeilSiegel.Free.Dil
