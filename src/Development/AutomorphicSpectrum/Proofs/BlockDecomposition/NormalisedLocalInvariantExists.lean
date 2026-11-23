module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBrauerRootsUnityEquivStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInvariantCupKummerStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInvariantCupUniformizerStatement
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.LocalInvariant

theorem exists_bijective_isNormalised :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ)
      [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) →
      ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v →
      ∃ f : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r),
        Function.Bijective f ∧ IsNormalised ζ A v f := by
  intro F Ω _ _ _ _ _ l _ r hr ζ hζ A v hA
  obtain ⟨e⟩ := GlobalTheory.T.local_brauer_roots_unity_equiv F Ω l r hr A v hA
  by_cases hN : IsNormalised ζ A v (e : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
  · exact ⟨e, e.bijective, hN⟩
  · simp only [IsNormalised, not_forall] at hN
    obtain ⟨ϖ, y, κ, χ, z, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := hN
    have hgen := GlobalTheory.T.local_invariant_cup_uniformizer F Ω l r hr ζ hζ A v hA ϖ y κ χ z h1 h2 h3 h4 h5 h6 h7 h8
    set c : H2 (muLoc F l r A) := Submodule.Quotient.mk z with hc

    obtain ⟨a, ha⟩ : ∃ a : ZMod (l ^ r), a * e c = 1 := by
      have hmem : e.symm 1 ∈ Submodule.span (ZMod (l ^ r)) {c} := by
        rw [hgen]; trivial
      obtain ⟨a, hac⟩ := Submodule.mem_span_singleton.1 hmem
      refine ⟨a, ?_⟩
      have := congrArg e hac
      simpa using this
    have ha' : e c * a = 1 := by rw [mul_comm]; exact ha
    refine ⟨a • (e : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), ⟨?_, ?_⟩, ?_⟩
    · intro x x' hxx
      have hxx' : a * e x = a * e x' := by simpa using hxx
      apply e.injective
      calc e x = e c * (a * e x) := by rw [← mul_assoc, ha', one_mul]
        _ = e c * (a * e x') := by rw [hxx']
        _ = e x' := by rw [← mul_assoc, ha', one_mul]
    · intro t
      refine ⟨e.symm (e c * t), ?_⟩
      simp [← mul_assoc, ha]
    · intro ϖ' y' κ' χ' z' g1 g2 g3 g4 g5 g6 g7 g8
      have hz := GlobalTheory.T.local_invariant_cup_kummer F Ω l r hr ζ hζ A v hA ϖ y κ χ z h1 h2 h3 h4 h5 h6 h7 h8
        ϖ' y' κ' χ' z' g1 g2 g3 g4 g5 g6 g7 g8
      rw [← hz]
      simpa using ha

end GlobalTheory.CompanionTheory.LocalInvariant
