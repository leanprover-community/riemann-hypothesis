module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.Duality

theorem pi_perpCond_eq_annihilator_sumPair : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), ∀ (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), (∀ v, Function.Injective (j v)) → ∀ L : LocCond ρ (locFam S Av), Submodule.pi Set.univ (perpCond μ ρ (locFam S Av) (fun v => hρ.comp' (continuous_locFam S Av v)) L) = ⨅ x ∈ Submodule.pi Set.univ L, LinearMap.ker ((sumPair S Av μ j ρ hρ).flip x) := by
  classical
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S Av μ ρ hρ j hj L
  ext y
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies, forall_const, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.flip_apply, ReciprocityTheory.Gal.perpCond, PositivityTheory.S2pt.sumPair, Finset.sum_apply,
    LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply, LinearMap.proj_apply]
  constructor
  · intro h x hx
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [h v (x v) (hx v), map_zero]
  · intro h v x0 hx0
    apply hj v
    rw [map_zero]
    have hs := h (Pi.single v x0) (fun w => by
      by_cases hw : w = v
      · subst hw
        simpa using hx0
      · simp [Pi.single_eq_of_ne hw])
    rw [Finset.sum_eq_single v] at hs
    · simpa using hs
    · intro w _ hw
      simp [Pi.single_eq_of_ne hw]
    · simp

end GlobalTheory.CompanionTheory.Duality
