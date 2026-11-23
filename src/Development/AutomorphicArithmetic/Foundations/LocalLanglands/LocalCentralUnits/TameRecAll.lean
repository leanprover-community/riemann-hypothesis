module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AutomorphicArithmetic.WhittakerHecke.LocalArtinInertiaValuationOfUniformizerPrime
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Zero.LLC.tameRecAll :
    ∀ (M Ω : Type) [Field M] [NumberField M] [Field Ω] [Algebra M Ω] [IsAlgClosure M Ω] (g : ℕ) [Fact g.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 M)) (h : IsPlaceOver A v), ((g : ℕ) : 𝓞 M) ∈ v.asIdeal → ((g : ℕ) : 𝓞 M) ∉ v.asIdeal ^ 2 → ∀ a : Weil h →* (v.adicCompletion M)ˣ, IsLocalArtin h a → ∀ π : Ω, π ^ (normV v - 1) = (g : Ω) → ∀ (t : Ine (F := M) A) (x : 𝓞 M), Valued.v ((a (ineIncl h t) : v.adicCompletion M) - algebraMap M (v.adicCompletion M) (x : M)) < 1 → A.valuation ((t : G M Ω) π / π - algebraMap M Ω (x : M)) < 1 :=
  UpperTheory.localArtin_inertia_valuation_of_uniformizer_prime
