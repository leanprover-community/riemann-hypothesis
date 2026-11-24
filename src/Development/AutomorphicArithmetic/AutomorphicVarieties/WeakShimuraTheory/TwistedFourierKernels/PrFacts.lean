module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ConjPlace
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistTwD

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5 GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.H5.prFacts :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} (V : s.Lev), Topology.IsQuotientMap V.pr ∧ (∀ g : G L Ω, ∃ g' : G L Ω, resP L Ω g' = s.c * resP L Ω g * s.c⁻¹ ∧ V.frame.conj (V.pr g) = V.pr g') ∧ ∀ H : Subgroup (G L Ω), H.Normal → IsClosed (H : Set (G L Ω)) → (∀ g g' : G L Ω, resP L Ω g' = s.c * resP L Ω g * s.c⁻¹ → g ∈ H → g' ∈ H) → (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → Ine (F := L) A ≤ H) → V.pr.ker ≤ H := by
  intro l _ L Ω _ _ _ _ _ _ s V
  refine ⟨(phiKer V).2.1, ?_, ?_⟩
  · intro g
    have hin : s.c * resP L Ω g * s.c⁻¹ ∈ (resP L Ω).range := by
      rw [← V.hη]
      have h1 : V.η (toGS Ω V.S' (resP L Ω g)) = 1 := (V.hη _).mpr ⟨g, rfl⟩
      simp only [map_mul, map_inv, h1, mul_one, mul_inv_cancel]
    obtain ⟨g', hg'⟩ := hin
    refine ⟨g', hg', ?_⟩
    have e1 : toGS Ω V.S' (s.c * resP L Ω g * s.c⁻¹) =
        toGS Ω V.S' s.c * ((V.pr g : V.η.ker) : GS Ω V.S') * (toGS Ω V.S' s.c)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      all_goals rfl
    apply Subtype.ext
    show toGS Ω V.S' s.c * ((V.pr g : V.η.ker) : GS Ω V.S') * (toGS Ω V.S' s.c)⁻¹ =
      ((V.pr g' : V.η.ker) : GS Ω V.S')
    rw [← e1, ← hg']
    all_goals rfl
  · intro H _ hcl _ hine
    apply (phiKer V).2.2 H hcl
    intro A v hAv hv
    apply hine A
    intro hlt
    apply hv
    apply V.sub
    have hmem := (hAv (l : 𝓞 (Lp L))).mp (by simpa using hlt)
    exact Or.inl (by simpa using hmem)
