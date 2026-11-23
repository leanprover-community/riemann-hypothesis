module

public import GroundTheory.AutomorphicForms.QuadraticConj
public import Mathlib.NumberTheory.NumberField.CMField
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open NumberField GroundTheory.Automorphic

section Datum

variable (F E : Type*) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [_root_.NumberField.IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]


include F in
theorem isCMField : IsCMField E := IsCMField.ofCMExtension F E

noncomputable def complexConjOver : E ≃ₐ[F] E :=
  haveI := isCMField F E
  AlgEquiv.ofRingEquiv (f := (IsCMField.complexConj E).toRingEquiv) fun x => by
    have h : ((CMExtension.equivMaximalRealSubfield F E x : maximalRealSubfield E) : E) =
        algebraMap F E x := CMExtension.equivMaximalRealSubfield_apply F E x
    rw [← h]
    exact IsCMField.complexConj_apply_eq_self E _

theorem complexConjOver_apply (x : E) :
    (haveI := isCMField F E;
      complexConjOver F E x = IsCMField.complexConj E x) := rfl

variable {F E}

theorem exists_not_mem_range : ∃ x : E, x ∉ Set.range (algebraMap F E) := by
  by_contra hall
  push Not at hall
  have hsurj : Function.Surjective (Algebra.linearMap F E) := fun x => hall x
  have h1 := LinearMap.finrank_range_le (Algebra.linearMap F E)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    Algebra.IsQuadraticExtension.finrank_eq_two] at h1
  omega

theorem mem_range_of_conj_eq {x : E} (hx : conj F E x = x) :
    x ∈ Set.range (algebraMap F E) := by
  refine ⟨Algebra.trace F E x / 2, ?_⟩
  have h2 := add_conj (F := F) x
  rw [hx] at h2
  rw [map_div₀, ← h2, map_ofNat]
  field_simp
  ring

variable (F E)

theorem conj_ne_one : conj F E ≠ 1 := by
  intro h
  obtain ⟨x, hx⟩ := exists_not_mem_range (F := F) (E := E)
  exact hx (mem_range_of_conj_eq (by rw [h]; rfl))

theorem conj_eq_complexConj (x : E) :
    (haveI := isCMField F E;
      conj F E x = IsCMField.complexConj E x) := by
  haveI := isCMField F E
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  have hσ : complexConjOver F E ≠ 1 := by
    intro h
    apply IsCMField.complexConj_ne_one E
    ext y
    have := congrArg (fun g : E ≃ₐ[F] E => g y) h
    simpa [complexConjOver_apply] using this
  have huniq := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  have := huniq.unique (conj_ne_one F E) hσ
  rw [this, complexConjOver_apply]

theorem embedding_conj (φ : E →+* ℂ) (x : E) : φ (conj F E x) = starRingEnd ℂ (φ x) := by
  haveI := isCMField F E
  rw [conj_eq_complexConj, IsCMField.complexEmbedding_complexConj]

variable {F E}

variable (F E)


end Datum

end GroundTheory.Heights₂.Theta
