module

public import Formalism.ConjugateSelfDual.Statement
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
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommuteInvLeft
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeD
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.GalN.V

private theorem val_le_one {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (A : ValuationSubring Ω) (x : 𝓞 K) : A.valuation (algebraMap K Ω (x : K)) ≤ 1 := by
  have hi : IsIntegral ℤ (algebraMap K Ω (x : K)) := (x.2 : IsIntegral ℤ (x : K)).map (IsScalarTower.toAlgHom ℤ K Ω)
  have hA : IsIntegral A (algebraMap K Ω (x : K)) := hi.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hA
  rw [A.valuation_le_one_iff, ← hy]
  exact y.2

private theorem exists_place {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω]
    [Algebra F Ω] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A w) :
    ∃ v : HeightOneSpectrum (𝓞 K), IsPlaceOver A v := by
  let I : Ideal (𝓞 K) :=
    { carrier := {x | A.valuation (algebraMap K Ω (x : K)) < 1}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        have e : algebraMap K Ω ((a + b : 𝓞 K) : K) = algebraMap K Ω (a : K) + algebraMap K Ω (b : K) := by
          simp
        rw [e]
        exact Valuation.map_add_lt _ ha hb
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        have e : algebraMap K Ω ((c • a : 𝓞 K) : K) = algebraMap K Ω (c : K) * algebraMap K Ω (a : K) := by
          simp
        rw [e, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_le_one A c)) ha }
  have hmem : ∀ x : 𝓞 K, x ∈ I ↔ A.valuation (algebraMap K Ω (x : K)) < 1 := fun _ => Iff.rfl
  have hprime : I.IsPrime := by
    refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
    · have := (hmem 1).1 (h ▸ Submodule.mem_top)
      simp at this
    · rw [hmem] at hab
      by_contra hcon
      push_neg at hcon
      obtain ⟨h1, h2⟩ := hcon
      rw [hmem, not_lt] at h1 h2
      have e1 := le_antisymm (val_le_one A a) h1
      have e2 := le_antisymm (val_le_one A b) h2
      have e : algebraMap K Ω ((a * b : 𝓞 K) : K) = algebraMap K Ω (a : K) * algebraMap K Ω (b : K) := by
        simp
      rw [e, map_mul, e1, e2] at hab
      simp at hab
  have hne : I ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    intro hI
    have h1 : A.valuation (algebraMap F Ω (x : F)) < 1 := (hA x).2 hx
    have h2 : algebraMap (𝓞 F) (𝓞 K) x ∈ I := by
      rw [hmem]
      rw [IsScalarTower.algebraMap_apply F K Ω] at h1
      exact h1
    rw [hI, Ideal.mem_bot] at h2
    exact hx0 (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K) (by simpa using h2))
  exact ⟨⟨I, hprime, hne⟩, fun x => (hmem x).symm⟩
