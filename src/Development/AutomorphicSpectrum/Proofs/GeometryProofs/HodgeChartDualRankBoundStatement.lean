module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeChartDualRankBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.T.hodge_chart_exists_seqHyp_gram_congr_mod_pow : ∀ (o Ω Li : Type) [CommRing o] [Field Ω] [CharZero Ω] [Algebra o Ω] (R : Subalgebra o Ω) [IsNoetherianRing R] [IsFractionRing R Ω] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (_ : ∀ x, c (c x) = x) (p Rr N r s m : ℕ) [Fact p.Prime] [AddCommGroup Li] [Module Ω Li] (D : HT.HTChart R Ω c p Rr N (Module.Dual Ω Li)) (ρ : 𝓞 E →+* Module.End Ω Li), (∀ (a : 𝓞 E) (w : Module.Dual Ω Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a)) → ∀ (σ : E →+* Ω) (i₀ : Module.Dual R (D.omHT (σ.comp c.toRingHom)) →ₗ[R] (Fin N → R)), D.ExactMod σ m i₀ → D.IsDualMap σ 1 m i₀ → Module.Projective R (D.omHT σ) → ∀ (v : Fin r → Li) (v' : Fin s → Li), LinearIndependent Ω v → Submodule.span Ω (Set.range v) = HT.eigSp ρ σ → LinearIndependent Ω v' → Submodule.span Ω (Set.range v') = HT.eigSp ρ (σ.comp c.toRingHom) → ∀ (W : AddSubgroup (Fin r → Ω)) (W' : AddSubgroup (Fin s → Ω)), (∀ a, a ∈ W ↔ ∀ u ∈ D.om', u (∑ k, a k • v k) ∈ R) → (∀ a, a ∈ W' ↔ ∀ u ∈ D.om', u (∑ k, a k • v' k) ∈ R) → ∀ w : Ω, w ∈ R → (∃ u ∈ R, (p : Ω) ^ m = w * u) → ∃ i : (Fin r → Ω) →ₗ[Ω] (Fin N → Ω), SeqHyp R w W (dotDual R W') i (Fintype.linearCombination Ω fun (n : Fin N) (k : Fin s) => D.h (Pi.single n 1) (v' k)) ∧ ∀ a ∈ W, ∀ j, ∃ z ∈ R, ∑ l, i a l * D.gram σ 1 l j = D.h (Pi.single j 1) (∑ k, a k • v k) + (p : Ω) ^ m * z := by
  exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqPure.seqHyp_chart
