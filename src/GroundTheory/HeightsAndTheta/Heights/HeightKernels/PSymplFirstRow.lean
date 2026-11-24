module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplFirstRow

theorem intVec_ne_zero {ι : Type*} {v : ι → ℤ} (hv : v ≠ 0) : intVec v ≠ 0 := by
  intro h
  apply hv
  funext i
  have := congrFun h i
  simpa [intVec] using this

end PSymplFirstRow

theorem SymplFirstRow.proof (h1 : SymplMinExists.Statement) (h2 : SymplMinBound.Statement)
    (h3 : SymplOrbit.Statement) (h4 : SymplShortPrim.Statement) (h5 : SymplGramMem.Statement) :
    SymplFirstRow.Statement := by
  intro n G hG hpd
  obtain ⟨ρsq, hleast⟩ := h1 (Fin (n + 1) ⊕ Fin (n + 1)) G hpd
  have hdet : G.det = 1 := SymplecticGroup.det_eq_one hG
  have hbound := h2 (Fin (n + 1) ⊕ Fin (n + 1)) G hpd hdet ρsq hleast
  obtain ⟨v, hv0, hvρ⟩ := hleast.1
  refine ⟨ρsq, hleast, ?_, ?_, ?_⟩
  · rw [hvρ]
    have := hpd.dotProduct_mulVec_pos (PSymplFirstRow.intVec_ne_zero hv0)
    simpa [qf] using this
  · simp only [Fintype.card_sum, Fintype.card_fin] at hbound
    push_cast at hbound
    linarith
  · have hmin : ∀ u : Fin (n + 1) ⊕ Fin (n + 1) → ℤ, u ≠ 0 →
        qf G (intVec v) ≤ qf G (intVec u) := by
      intro u hu
      rw [← hvρ]
      exact hleast.2 ⟨u, hu, rfl⟩
    obtain ⟨P, hP, m, hm⟩ := h3 n v
    have hrow : ∃ P' ∈ symplecticGroup (Fin (n + 1)) ℤ, P' (Sum.inl 0) = v := by
      rcases h4 _ G hpd v (P (Sum.inl 0)) m hm hv0 hmin with h | h
      · exact ⟨P, hP, by rw [hm, h, one_smul]⟩
      · refine ⟨-P, SymplecticGroup.neg_mem hP, ?_⟩
        rw [hm, h, neg_one_smul]
        rfl
    obtain ⟨P', hP', hP'v⟩ := hrow
    refine ⟨P', hP', ?_⟩
    rw [(h5 (n + 1) P' G hP' hG hpd).2.2.2 (Sum.inl 0), hP'v, hvρ]

end GroundTheory.Heights₂.Heights
