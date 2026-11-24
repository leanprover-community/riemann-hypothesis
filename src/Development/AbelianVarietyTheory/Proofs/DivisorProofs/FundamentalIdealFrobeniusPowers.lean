module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData

namespace GlobalTheory.SmGL.CuspSpan

theorem blk_two_apply {α β n : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (c : α ⊕ β ≃ n) (s : α ⊕ β) : GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two c) (c s) = s.isRight := by
  rcases s with p | q
  · rw [← GlobalTheory.SmGL.two_false, GlobalTheory.SmGL.blk_apply]; rfl
  · rw [← GlobalTheory.SmGL.two_true, GlobalTheory.SmGL.blk_apply]; rfl

theorem mem_span_unip (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : GlobalTheory.SmGL.IsCuspidal π) (a b : ℕ)
    (e : Fin N ≃ Fin a ⊕ Fin b) (ha : 0 < a) (hb : 0 < b)
    (u : (Fin a → Fin b → k) → GL (Fin N) k)
    (hu : ∀ X, (u X : Matrix (Fin N) (Fin N) k) =
      Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) (w : V) :
    w ∈ Submodule.span ℂ {x | ∃ (Y : Fin a → Fin b → k) (y : V), x = π (u Y) y - y} := by
  have h : a + b = N := by
    have := Fintype.card_congr e
    simpa using this.symm
  have H := ((GlobalTheory.SmGL.CuspMax.isCuspidal_iff_maximal k N V π).1 hπ).2 a b h ha hb
  have H' : Subsingleton (Jacquet π (unipRad k (GlobalTheory.SmGL.two e.symm))) := by
    refine GlobalTheory.SmGL.CuspMax.subsingleton_jacquet_of_perm π (e.trans (stdSum h)) (fun i j hij => ?_) H
    have h1 : ∀ i, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two (stdSum h)) ((e.trans (stdSum h)) i) = (e i).isRight :=
      fun i => blk_two_apply (stdSum h) (e i)
    have h2 : ∀ i, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two e.symm) i = (e i).isRight := fun i => by
      have := blk_two_apply e.symm (e i)
      rwa [Equiv.symm_apply_apply] at this
    rw [h1, h1] at hij
    rw [h2, h2]
    exact hij
  have htop : twKer π (unipRad k (GlobalTheory.SmGL.two e.symm)) 1 = ⊤ :=
    Submodule.Quotient.subsingleton_iff.1 H'
  have hw : w ∈ twKer π (unipRad k (GlobalTheory.SmGL.two e.symm)) 1 := htop ▸ Submodule.mem_top
  refine (Submodule.span_le.2 ?_) hw
  rintro _ ⟨n, v, rfl⟩
  refine Submodule.subset_span ⟨fun p q => (n : GL (Fin N) k) (e.symm (Sum.inl p)) (e.symm (Sum.inr q)),
    v, ?_⟩
  have hn : (n : GL (Fin N) k) = u (fun p q => (n : GL (Fin N) k) (e.symm (Sum.inl p)) (e.symm (Sum.inr q))) := by
    have hent := GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries.1 n.2
    have h2 : ∀ i, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two e.symm) i = (e i).isRight := fun i => by
      have := blk_two_apply e.symm (e i)
      rwa [Equiv.symm_apply_apply] at this
    ext i j
    rw [hu, Matrix.reindex_apply, Matrix.submatrix_apply]
    simp only [Equiv.symm_symm]
    obtain ⟨s, rfl⟩ := e.symm.surjective i
    obtain ⟨t, rfl⟩ := e.symm.surjective j
    simp only [Equiv.apply_symm_apply]
    rcases s with p | p <;> rcases t with q | q
    · rw [hent _ _ (by rw [h2, h2]; simp), Matrix.fromBlocks_apply₁₁]
      simp [Matrix.one_apply]
    · rw [Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
    · rw [hent _ _ (by rw [h2, h2]; simp), Matrix.fromBlocks_apply₂₁]
      simp [Matrix.one_apply]
    · rw [hent _ _ (by rw [h2, h2]; simp), Matrix.fromBlocks_apply₂₂]
      simp [Matrix.one_apply]
  rw [← hn]
  simp

end GlobalTheory.SmGL.CuspSpan
