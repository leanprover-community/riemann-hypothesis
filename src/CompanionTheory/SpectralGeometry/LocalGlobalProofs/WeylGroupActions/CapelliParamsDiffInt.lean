module

public import Formalism.HermitianCurvature.CapelliDeterminantAndBranching
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CommonEigenvectors
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HighestWeightPolynomials
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cut_BPEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.GapLie

theorem capelli_params_diff_int : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (m : Fin n → ℂ), GlRel E → (∀ w v, qdet E w v = Qr.cpol m w • v) → ∀ i j, ∃ N : ℤ, m i - m j = (N : ℂ) := by
  intro V _ _ _ _ n E m hE hq
  obtain ⟨ν, v, -, hv0, hw, -⟩ := Formalism.FourierDecayAlt.P.exists_singular_maximal_vector V n E hE ⊤
    (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
  have hc := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.hw_cpol (m := m) hE (Qr.mem_CapSp.2 fun w => hq w v) hv0 hw
  have hroot : ∀ i, ∃ a : Fin n, m i = ν a - ((a : ℕ) : ℂ) := by
    intro i
    have h1 := hc (-m i)
    unfold Qr.cpol at h1
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by ring)] at h1
    obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 h1.symm
    exact ⟨a, by linear_combination -ha⟩
  have hdom : ∀ a b : Fin n, ∃ N : ℤ, ν a - ν b = (N : ℂ) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · obtain ⟨N, hN⟩ := Formalism.FourierDecayAlt.P.singular_dominant V n E ν v hE hw hv0 a b h
      exact ⟨N, by simpa using hN⟩
    · exact ⟨0, by simp [h]⟩
    · obtain ⟨N, hN⟩ := Formalism.FourierDecayAlt.P.singular_dominant V n E ν v hE hw hv0 b a h
      refine ⟨-N, ?_⟩
      push_cast
      linear_combination -hN
  intro i j
  obtain ⟨a, ha⟩ := hroot i
  obtain ⟨b, hb⟩ := hroot j
  obtain ⟨N, hN⟩ := hdom a b
  refine ⟨N - (a : ℕ) + (b : ℕ), ?_⟩
  push_cast
  linear_combination ha - hb + hN

end GlobalTheory.CompanionTheory.GapLie
