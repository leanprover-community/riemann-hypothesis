module

public import Formalism.HermitianCurvature.CapelliDeterminantAndBranching
public import Development.AbelianVarietyTheory.Definitions.Jets.Imports
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirEigenspaceIrreducibleStandardStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarProjectionSplitCasimirRaisingLastStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerExtremeNeZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IrreducibleCapelliModules
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
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

namespace GlobalTheory.WigSh

theorem exists_splitCasimir_std (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) :
    ∃ Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), ∀ y b, Om y b = ∑ c, E c b (y c) := by
  refine ⟨(WithLp.linearEquiv 2 ℂ (Fin (n + 1) → V)).symm.toLinearMap ∘ₗ
    (LinearMap.pi fun b => ∑ c, E c b ∘ₗ LinearMap.proj c) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Fin (n + 1) → V)).toLinearMap, ?_⟩
  intro y b
  simp [LinearMap.sum_apply]

theorem pieri_step_raise : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ j, L j ≠ L l + 1) → ∃ S : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), Stab Et S ∧ S ≠ ⊥ ∧ (∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ S → Stab Et S' → S' = ⊥ ∨ S' = S) ∧ S ≤ CapSp Et (shf β (Function.update L l (L l + 1))) ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → S.starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wP L M l : ℂ) • v := by
  intro V _ _ _ n E Et β L l hyp hadj hEt hL
  obtain ⟨Om, hOm⟩ := exists_splitCasimir_std V n E
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.splitCasimir_eigenspace_irreducible_standard_alt V n E Et Om β L l hyp hadj hEt hOm
  have h4 := GlobalTheory.T.starProjection_splitCasimir_raising_last V n E Et Om β L l hyp hadj hEt hOm
  refine ⟨_, h1, ?_, h2, h3, h4⟩
  intro hbot
  have hbox : Box L (fun j : Fin n => L j.castSucc) := fun j =>
    ⟨hyp.anti (Fin.castSucc_lt_succ), le_rfl⟩
  have hne := (Formalism.FourierDecayAlt.P.branching_decomposition V n E β L hyp).1 _ hbox
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have h5 := h4 _ v hv
  have hw := (wigner_extreme_ne_zero n L l hyp.anti).1 hL
  have hmem := Submodule.starProjection_apply_mem (Module.End.eigenspace Om (β + L l + 0))
    (PiLp.single 2 (Fin.last n) v)
  have hz : (Module.End.eigenspace Om (β + L l + 0)).starProjection
      (PiLp.single 2 (Fin.last n) v) = 0 := (Submodule.eq_bot_iff _).1 hbot _ hmem
  rw [hz] at h5
  have h6 : ((wP L (fun j : Fin n => L j.castSucc) l : ℝ) : ℂ) • v = 0 := by
    rw [← h5]; rfl
  rcases smul_eq_zero.1 h6 with h | h
  · exact hw (by exact_mod_cast h)
  · exact hv0 h

end GlobalTheory.WigSh
