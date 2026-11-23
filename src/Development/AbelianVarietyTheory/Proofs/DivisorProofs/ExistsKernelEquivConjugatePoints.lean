module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.ConjPoint

lemma IsConj.mem_lattice_iff {L L' : PeriodPair} {σ : ℂ ≃+* ℂ} {t t' : ℂ}
    (h : IsConj L L' σ t t') : t ∈ L.lattice ↔ t' ∈ L'.lattice := by
  rcases h with h | h
  · exact iff_of_true h.1 h.2
  · exact iff_of_false h.1 h.2.1

theorem exists_equiv_kerReps_isConj :
    ∀ (L : PeriodPair) (σ : ℂ ≃+* ℂ) (α : ℂ) (S S' : Finset ℂ), L.g₂ = σ L.g₂ → L.g₃ = σ L.g₃ →
      MulStable L α → IsKerReps L α S → IsKerReps L (σ α) S' →
      ∃ e : S ≃ S', ∀ t : S, GlobalTheory.ConjPoint.IsConj L L σ (t : ℂ) (e t : ℂ) := by
  intro L σ α S S' h₂ h₃ hα hS hS'
  obtain ⟨s, -, hc⟩ := exists_conjEquiv h₂ h₃
  have hf : ∀ t : S, ∃ t' : S', IsConj L L σ (t : ℂ) (t' : ℂ) := by
    intro t
    obtain ⟨u, hu⟩ := latticePoint_surjective L (s (latticePoint L t))
    have h := (hc _ _).2 hu.symm
    obtain ⟨P, hP, hd⟩ := hS'.2.2 u ((IsConj.mul h₂ h₃ hα h).mem_lattice_iff.1 (hS.1 t t.2).1)
      (fun hm ↦ (hS.1 t t.2).2 (h.mem_lattice_iff.2 hm))
    exact ⟨⟨P, hP⟩, (hc _ _).2 (hu.symm.trans ((latticePoint_eq_iff L).2 hd))⟩
  choose f hf using hf
  refine ⟨Equiv.ofBijective f ⟨fun a b hab ↦ ?_, fun t' ↦ ?_⟩, hf⟩
  · have ha := (hc _ _).1 (hf a)
    have hb := (hc _ _).1 (hf b)
    rw [hab, ← hb] at ha
    exact Subtype.ext (hS.2.1 _ a.2 _ b.2 ((latticePoint_eq_iff L).1 (s.injective ha)))
  · obtain ⟨Q, hQ⟩ := s.surjective (latticePoint L t')
    obtain ⟨u, rfl⟩ := latticePoint_surjective L Q
    have h := (hc _ _).2 hQ
    obtain ⟨P, hP, hd⟩ := hS.2.2 u ((IsConj.mul h₂ h₃ hα h).mem_lattice_iff.2 (hS'.1 t' t'.2).1)
      (fun hm ↦ (hS'.1 t' t'.2).2 (h.mem_lattice_iff.1 hm))
    refine ⟨⟨P, hP⟩, Subtype.ext (hS'.2.1 _ (f _).2 _ t'.2 ((latticePoint_eq_iff L).1 ?_))⟩
    rw [← (hc _ _).1 (hf ⟨P, hP⟩), ← hQ, (latticePoint_eq_iff L).2 hd]

end GlobalTheory.ConjPoint
