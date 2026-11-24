module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Formalism.PieriBlockIdeals.CapelliCentralEnveloping
import Formalism.PieriBlockIdeals.LemmaWFromLattice
import Formalism.PieriBlockIdeals.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

namespace GlobalTheory

theorem rank_residue_succ_of_adjoin
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (ϖ : O)
    (Ac As : Matrix (Fin n) (Fin n) O) (x : Fin n → O) :
    Irreducible ϖ → (∀ y : Fin n → O, ∃ u, Ac *ᵥ u = fun a => ϖ * y a) →
    (∀ w, ∃ u c, As *ᵥ w = Ac *ᵥ u + fun a => c * x a) → (∃ w, As *ᵥ w = x) →
    (∀ u, ∃ w, As *ᵥ w = Ac *ᵥ u) → (¬ ∃ u, Ac *ᵥ u = x) →
    (As.map (residue O)).rank = (Ac.map (residue O)).rank + 1 := by
  intro hϖ h1 h2 h3 h4 h5
  set bar := residue O with hbar
  have hmap : ∀ (A : Matrix (Fin n) (Fin n) O) (v : Fin n → O),
      (A.map bar) *ᵥ (bar ∘ v) = bar ∘ (A *ᵥ v) := by
    intro A v; funext i; exact (RingHom.map_mulVec bar A v i).symm
  have hlift : ∀ z : Fin n → ResidueField O, ∃ v : Fin n → O, bar ∘ v = z := by
    intro z
    refine ⟨fun i => (residue_surjective (z i)).choose, ?_⟩
    funext i; exact (residue_surjective (z i)).choose_spec
  set V := LinearMap.range (As.map bar).mulVecLin
  set Wc := LinearMap.range (Ac.map bar).mulVecLin
  set xb : Fin n → ResidueField O := bar ∘ x
  have hV : V = Wc ⊔ Submodule.span (ResidueField O) {xb} := by
    apply le_antisymm
    · rintro v ⟨z, rfl⟩
      obtain ⟨w, rfl⟩ := hlift z
      obtain ⟨u, c, hc⟩ := h2 w
      rw [Matrix.mulVecLin_apply, hmap, hc]
      have : bar ∘ (Ac *ᵥ u + fun a => c * x a) = (Ac.map bar) *ᵥ (bar ∘ u) + bar c • xb := by
        rw [hmap]; funext i; simp [xb]
      rw [this]
      exact Submodule.add_mem_sup ⟨bar ∘ u, rfl⟩
        (Submodule.smul_mem _ _ (Submodule.subset_span rfl))
    · apply sup_le
      · rintro v ⟨z, rfl⟩
        obtain ⟨u, rfl⟩ := hlift z
        obtain ⟨w, hw⟩ := h4 u
        refine ⟨bar ∘ w, ?_⟩
        rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hmap, hmap, hw]
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        obtain ⟨w, hw⟩ := h3
        exact ⟨bar ∘ w, by rw [Matrix.mulVecLin_apply, hmap, hw]⟩
  have hxb : xb ∉ Wc := by
    rintro ⟨z, hz⟩
    obtain ⟨u, rfl⟩ := hlift z
    rw [Matrix.mulVecLin_apply, hmap] at hz
    have hmem : ∀ a, (x - Ac *ᵥ u) a ∈ Ideal.span {ϖ} := by
      intro a
      rw [← hϖ.maximalIdeal_eq, ← residue_eq_zero_iff]
      have := congrFun hz a
      simp only [Function.comp_apply, xb] at this
      rw [Pi.sub_apply, map_sub, ← hbar, this, sub_self]
    choose y hy using fun a => Ideal.mem_span_singleton'.1 (hmem a)
    obtain ⟨u', hu'⟩ := h1 y
    apply h5
    refine ⟨u + u', ?_⟩
    rw [Matrix.mulVec_add, hu']
    funext a
    have := hy a
    simp only [Pi.sub_apply] at this
    simp only [Pi.add_apply]
    rw [mul_comm, this]; ring
  have hxb0 : xb ≠ 0 := by
    intro h; exact hxb (h ▸ Wc.zero_mem)
  have hinf : Wc ⊓ Submodule.span (ResidueField O) {xb} = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvW, hvs⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hvs
    by_cases hc : c = 0
    · simp [hc]
    · exact absurd (by simpa [hc] using Wc.smul_mem c⁻¹ hvW) hxb
  have key := Submodule.finrank_sup_add_finrank_inf_eq Wc (Submodule.span (ResidueField O) {xb})
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hxb0, ← hV] at key
  rw [← Matrix.finrank_range_mulVecLin (As.map bar), ← Matrix.finrank_range_mulVecLin (Ac.map bar)]
  exact key

end GlobalTheory
