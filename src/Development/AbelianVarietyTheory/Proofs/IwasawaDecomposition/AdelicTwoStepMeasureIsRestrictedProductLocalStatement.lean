module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicTwoStepMeasureIsRestrictedProductLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.adelicTwoStepMeasure_isRestrictedProduct_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (ν : Measure (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)) (mi : Measure (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E)) (ν' : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (mi' : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (mv' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (N : Measure (Fin 2 → Fin (M + 1) → AF F ⊗[F] E)) (Ni : Measure (Fin 2 → Fin (M + 1) → Ainf F ⊗[F] E)) (Nv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 2 → Fin (M + 1) → Fv F v ⊗[F] E)), StepData σ J x a B J' → IsProd b ν mi mv → IsProd b ν' mi' mv' → OnOrbit (Ainf F) σ J x mi → (∀ v, OnOrbit (Fv F v) σ J x (mv v)) → IsInvTup (Ainf F) σ J' mi' → (∀ v, IsInvTup (Fv F v) σ J' (mv' v)) → TwoStep (Ainf F) σ J x B mi mi' Ni → (∀ v, TwoStep (Fv F v) σ J x B (mv v) (mv' v) (Nv v)) → TwoStep (AF F) σ J x B ν ν' N → IsProd b N Ni Nv := by
  first | exact @GlobalTheory.GaugeEx.TsProd.twoStep_isProd | exact GlobalTheory.GaugeEx.TsProd.twoStep_isProd | (intros; apply GlobalTheory.GaugeEx.TsProd.twoStep_isProd <;> assumption)
