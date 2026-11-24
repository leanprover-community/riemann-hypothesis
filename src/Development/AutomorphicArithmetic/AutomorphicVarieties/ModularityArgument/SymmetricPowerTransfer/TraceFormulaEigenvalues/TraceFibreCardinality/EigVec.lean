module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace UpperTheory.V.Z.Sym.Tf

private lemma exists_ker_of_pow {M : Type} [AddCommGroup M] [Module ℂ M] (N : Module.End ℂ M) (W : Submodule ℂ M)
    (hW : ∀ w ∈ W, N w ∈ W) : ∀ (k : ℕ) (v : M), v ∈ W → v ≠ 0 → (N ^ k) v = 0 → ∃ w ∈ W, w ≠ 0 ∧ N w = 0 := by
  intro k
  induction k with
  | zero => intro v _ hv h; exact absurd (by simpa using h) hv
  | succ k ih =>
    intro v hvW hv h
    by_cases h0 : N v = 0
    · exact ⟨v, hvW, hv, h0⟩
    · exact ih (N v) (hW v hvW) h0 (by rw [pow_succ] at h; exact h)

theorem eigVec : EigVec := by
  intro Λ M _ _ _ u hc χ
  constructor
  · intro h
    set E : Submodule ℂ M := ⨅ a, (u a).maxGenEigenspace (χ a) with hE
    let S : Set (Submodule ℂ M) := {W | W ≠ ⊥ ∧ W ≤ E ∧ ∀ b, ∀ w ∈ W, u b w ∈ W}
    have hS : S.Nonempty := by
      refine ⟨E, h, le_rfl, fun b w hw => ?_⟩
      rw [hE, Submodule.mem_iInf] at hw ⊢
      intro a
      exact Module.End.mapsTo_maxGenEigenspace_of_comm (hc a b) (χ a) (hw a)
    obtain ⟨W, ⟨hW0, hWE, hWs⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ M)).has_min S hS
    obtain ⟨v, hvW, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    refine ⟨v, hv, fun a => ?_⟩
    have key : W ⊓ (u a).eigenspace (χ a) ∈ S := by
      refine ⟨?_, inf_le_left.trans hWE, fun b w hw => ⟨hWs b w hw.1, ?_⟩⟩
      · have hva : v ∈ (u a).maxGenEigenspace (χ a) := by
          have := hWE hvW
          rw [hE, Submodule.mem_iInf] at this
          exact this a
        obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hva
        obtain ⟨w, hwW, hw, hN⟩ := exists_ker_of_pow (u a - χ a • (1 : Module.End ℂ M)) W
          (fun w hw => by
            simpa using W.sub_mem (hWs a w hw) (W.smul_mem (χ a) hw)) k v hvW hv hk
        refine (Submodule.ne_bot_iff _).2 ⟨w, ⟨hwW, ?_⟩, hw⟩
        refine Module.End.mem_eigenspace_iff.2 ?_
        simpa [sub_eq_zero] using hN
      · have h2 := Module.End.mem_eigenspace_iff.1 hw.2
        refine Module.End.mem_eigenspace_iff.2 ?_
        have h3 : u a (u b w) = u b (u a w) := congrArg (fun f : Module.End ℂ M => f w) (hc a b).eq
        rw [h3, h2, map_smul]
    have heq : W ⊓ (u a).eigenspace (χ a) = W := by
      by_contra hne
      exact hmin _ key (lt_of_le_of_ne inf_le_left hne)
    rw [← heq] at hvW
    exact Module.End.mem_eigenspace_iff.1 hvW.2
  · rintro ⟨v, hv, h⟩
    refine (Submodule.ne_bot_iff _).2 ⟨v, ?_, hv⟩
    rw [Submodule.mem_iInf]
    intro a
    exact (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, by simp [h a]⟩

end UpperTheory.V.Z.Sym.Tf
