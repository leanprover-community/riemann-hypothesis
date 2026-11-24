module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExtendLin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeChartDualActionCompat
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

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.hodge_chart_dual_action_compat : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Li : Type) [AddCommGroup Li] [Module K Li] (D : HTChart A K c p R N (Module.Dual K Li)) (ρ : 𝓞 E →+* Module.End K Li), (∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a)) → ∀ (σ : E →+* K) (m : ℕ), Module.Projective A (D.omHT σ) → (∀ y ∈ D.omHT σ, ∃ x : Fin N → A, ∃ y' ∈ D.omHT σ, y = D.q σ x + ((p : A) ^ m) • y') → ∃ Rr : (Fin N → K) →ₗ[K] Li, (∀ k, Rr (Pi.single k 1) ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) 1 (algebraMap A K).range) ∧ ∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) 1 (algebraMap A K).range, ∃ e' ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) 1 (algebraMap A K).range, Rr (fun l => D.h (Pi.single l 1) e) = e + ((p : K) ^ m) • e' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.HTL.exists_retraction_mod | exact GlobalTheory.CompanionTheory.Ar.Flat.HTL.exists_retraction_mod | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.HTL.exists_retraction_mod <;> assumption)
