module

import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.JuxtSwap
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.JuxtDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistInjectiveStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nu_nu_nat (x : IrrGL (k := k)) (a b : ℕ) : (x.nu (a : ℂ)).nu (b : ℂ) = x.nu ((a + b : ℕ) : ℂ) := by
  rw [IrrGL.nu_nu, Nat.cast_add]

theorem not_linked_single (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (ρ : IrrGL (k := k)) (hρ : ρ.IsCusp) (n j : ℕ)
    (hj : j + 2 ≤ n) :
    ¬ (Segment.single (ρ.nu (n : ℂ)) (hρ.nu _)).Linked (Segment.single (ρ.nu (j : ℂ)) (hρ.nu _)) := by
  apply CompanionTheory.Exh.not_linked_single <;> assumption

theorem mem_tail_decW (Δ : Segment k) (x : IrrGL (k := k)) (hx : x ∈ (decW Δ).tail) :
    ∃ j : ℕ, j + 2 ≤ Δ.len ∧ x = Δ.first.nu (j : ℂ) := by
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hx
  have hm' : m + 1 < Δ.len := by
    have := hm
    simp [decW] at this
    omega
  refine ⟨Δ.len - (m + 2), by omega, ?_⟩
  simp only [List.getElem_tail, decW, List.getElem_ofFn, Segment.term, Fin.val_rev]

theorem move_past (hS : SwapP k) (σ ρ : IrrGL (k := k)) (hρ : ρ.IsCusp) :
    ∀ (Q P : List (IrrGL (k := k))), (∀ q ∈ Q, ∃ hq : q.IsCusp, ¬ (Segment.single ρ hρ).Linked (Segment.single q hq)) →
      EmbL σ (P ++ ρ :: Q) → EmbL σ (P ++ Q ++ [ρ]) := by
  apply CompanionTheory.Exh.move_past <;> assumption

theorem emb_move_end (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hS : SwapP k) (σ : IrrGL (k := k)) (Δ : Segment k)
    (P Q : List (IrrGL (k := k))) (h1 : decW Δ = P ++ Q) (hP : P ≠ []) (he : EmbL σ (P ++ nxt Δ :: Q)) :
    EmbL σ (decW Δ ++ [nxt Δ]) := by
  obtain ⟨p, P', rfl⟩ := List.exists_cons_of_ne_nil hP
  rw [h1]
  refine move_past hS σ (nxt Δ) (Δ.isCusp_first.nu _) Q (p :: P') ?_ he
  intro q hq
  have hq' : q ∈ (decW Δ).tail := by rw [h1]; simp [hq]
  obtain ⟨j, hj, rfl⟩ := mem_tail_decW Δ q hq'
  exact ⟨Δ.isCusp_first.nu _, not_linked_single hA Δ.first Δ.isCusp_first Δ.len j (by omega)⟩

end PositivityTheory.Exh

end
