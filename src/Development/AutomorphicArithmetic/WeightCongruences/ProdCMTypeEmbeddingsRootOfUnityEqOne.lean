module

public import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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

open NumberField Formalism.BasicNotions

theorem UpperTheory.prod_CMType_embeddings_root_of_unity_eq_one :
    ∀ (R : Ranks) (H : Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ),
      (∀ σ : H.E →+* ℂ, ∃! i, σ = φ i ∨ σ = ComplexEmbedding.conjugate (φ i)) → (∀ i j, φ i H.sqd = φ j H.sqd) →
      ∀ z : H.E, (∃ m : ℕ, 0 < m ∧ z ^ m = 1) → ∏ i, φ i z = 1 := by
  intro R H I _ φ hu hs z hz
  haveI : IsGalois ℚ H.E := H.galois
  obtain ⟨i₀, -, -⟩ := hu H.φ₀
  have hfix : ∀ g : R.Psi, H.sigmaOf (g : R.GG) H.sqd = H.sqd := fun g => by
    refine (H.galE_mem_Psi_iff _).1 ?_
    have h : H.galE (H.sigmaOf (g : R.GG)) = g := H.gal.apply_symm_apply _
    rw [h]; exact g.2
  have hex : ∀ i, ∃ g : R.Psi, ∀ x, φ i₀ (H.sigmaOf (g : R.GG) x) = φ i x := fun i => by
    obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) (K := H.E) (φ i₀) (φ i)
      (Subsingleton.elim _ _)
    have h1 : ∀ x, φ i₀ (σ.symm x) = φ i x := fun x => RingHom.congr_fun hσ x
    have h2 : σ.symm H.sqd = H.sqd := (φ i₀).injective ((h1 _).trans (hs i i₀))
    refine ⟨⟨H.galE σ.symm, (H.galE_mem_Psi_iff _).2 h2⟩, fun x => ?_⟩
    have h : H.sigmaOf (H.galE σ.symm) = σ.symm := H.gal.symm_apply_apply _
    show φ i₀ (H.sigmaOf (H.galE σ.symm) x) = _
    rw [h, h1]
  choose f hf using hex
  have hinj : Function.Injective f := fun i j hij => by
    have h : φ i = φ j := RingHom.ext fun x => by rw [← hf i, ← hf j, hij]
    exact (hu (φ i)).unique (Or.inl rfl) (Or.inl h)
  have hsurj : Function.Surjective f := fun g => by
    obtain ⟨i, hi, -⟩ := hu ((φ i₀).comp (H.sigmaOf (g : R.GG) : H.E →+* H.E))
    rcases hi with hi | hi
    · refine ⟨i, Subtype.ext (H.gal.symm.injective ?_)⟩
      refine AlgEquiv.ext fun x => (φ i₀).injective ?_
      exact (hf i x).trans (RingHom.congr_fun hi x).symm
    · exfalso
      have h1 : φ i₀ (H.sigmaOf (g : R.GG) H.sqd) = (starRingEnd ℂ) (φ i H.sqd) := RingHom.congr_fun hi H.sqd
      have hc : H.conj H.sqd = -H.sqd := H.conj_sqd
      have h2 : φ i (H.conj H.sqd) = (starRingEnd ℂ) (φ i H.sqd) := H.conjE_apply (φ i) H.sqd
      rw [hfix, ← h2, hc, map_neg, hs i₀ i] at h1
      have h3 : φ i H.sqd = 0 := by linear_combination h1 / 2
      exact H.sqd_ne_zero ((map_eq_zero (φ i)).1 h3)
  have h1 := UpperTheory.Mu.prod_emb H (Equiv.ofBijective f ⟨hinj, hsurj⟩) hz
  have h2 : H.φ₀ (∏ i, H.sigmaOf (f i : R.GG) z) = H.φ₀ 1 := by
    rw [map_prod, map_one]; exact h1
  have h3 := congrArg (φ i₀) (H.φ₀.injective h2)
  rw [map_prod, map_one] at h3
  rw [← h3]
  exact Finset.prod_congr rfl fun i _ => (hf i z).symm
