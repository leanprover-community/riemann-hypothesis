module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardEqCardKerMulCardRange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisCohomologyLocalGlobalDualStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatCardDualEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoitouTateEulerCharacteristicStatement
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.PoitouTateCount

theorem card_sha2_mul_card_local_h2 : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), ∀ (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), LocalFiniteness → 0 < r → (∀ v : S, IsPlaceOver (Av v) v.1) → NineTermExact S Av μ j ρ hρ → Finite (H2 ρ) → Finite (H0 (twDual μ ρ)) → Nat.card (Sha2 ρ (locFam S Av) (continuous_locFam S Av)) * Nat.card (∀ v : S, H2 (ρ.comp (locFam S Av v))) = Nat.card (H2 ρ) * Nat.card (H0 (twDual μ ρ)) := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S Av μ ρ hρ j hLF hr hAv hNine hH2 hH0
  obtain ⟨_δ₁, _δ₂, -, -, -, -, -, -, -, hex, hsurj⟩ := hNine
  haveI : ∀ v : S, Finite (H2 (ρ.comp (locFam S Av v))) := fun v =>
    (GlobalTheory.T.finite_local_cohomology_at_places_of_localFiniteness F Ω l r M S Av μ ρ hρ hLF hr hAv v).2.2
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : Nat.Prime l).ne_zero⟩
  have hsha : Sha2 ρ (locFam S Av) (continuous_locFam S Av) = LinearMap.ker (loc2 S Av ρ) :=
    (GlobalTheory.T.poitou_tate_euler_characteristic F Ω l r M S Av μ ρ hρ).2.2
  have h1 := GlobalTheory.CompanionTheory.Counting.card_eq_card_ker_mul_card_range (ZMod (l ^ r)) _ _ (loc2 S Av ρ)
  have h2 := GlobalTheory.CompanionTheory.Counting.card_eq_card_ker_mul_card_range (ZMod (l ^ r)) _ _ (tr2 S Av μ j ρ)
  have hker : LinearMap.ker (tr2 S Av μ j ρ) = LinearMap.range (loc2 S Av ρ) := LinearMap.exact_iff.mp hex
  have htop : LinearMap.range (tr2 S Av μ j ρ) = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have htopc : Nat.card ↥(⊤ : Submodule (ZMod (l ^ r)) (Module.Dual (ZMod (l ^ r)) ↥(H0 (twDual μ ρ)))) =
      Nat.card (Module.Dual (ZMod (l ^ r)) ↥(H0 (twDual μ ρ))) :=
    Nat.card_congr Submodule.topEquiv.toEquiv
  have hD := GlobalTheory.CompanionTheory.ZModDual.nat_card_dual_eq (l ^ r) ↥(H0 (twDual μ ρ))
  rw [hsha, h2, hker, htop, htopc, hD, h1]
  ring

end GlobalTheory.CompanionTheory.PoitouTateCount
