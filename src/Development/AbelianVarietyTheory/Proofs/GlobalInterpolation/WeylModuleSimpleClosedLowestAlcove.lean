module

public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HighestWeightVectorMemOfLtStableDualWeylStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsRowOperatorStableDualWeylAndGLSubmodulesStatement
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem natW_alcove_bound (p : ℕ) (N : ℕ) (lam : DomWeight N)
    (hl : ∀ i j : Fin N, i < j → lam.w i - lam.w j + ((j : ℕ) - (i : ℕ) : ℤ) ≤ (p : ℤ)) :
    ∀ h : 0 < N, lam.natW ⟨N - 1, by omega⟩ = 0 ∧ lam.natW ⟨0, h⟩ + (N - 1) ≤ p := by
  intro h
  obtain ⟨_, h2, h3⟩ := factNatW N lam
  refine ⟨h3 h, ?_⟩
  have e0 := h2 ⟨0, h⟩
  have e1 := h2 ⟨N - 1, by omega⟩
  rw [h3 h] at e1
  by_cases hN1 : N = 1
  · subst hN1
    have : (⟨0, h⟩ : Fin 1) = ⟨1 - 1, by omega⟩ := rfl
    rw [this, h3 h]
    omega
  · have hlt : (⟨0, h⟩ : Fin N) < ⟨N - 1, by omega⟩ := Fin.mk_lt_mk.mpr (by omega)
    have := hl _ _ hlt
    simp only at this
    have hc : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by omega
    push_cast at this
    omega

theorem inducedSimpleLowestAlcove : GlobalTheory.Published.InducedSimpleLowestAlcove := by
  intro p hp k _ _ N lam hl
  have hN := factNatW N lam
  have hne : nablaSq k N lam ≠ ⊥ := by
    intro h
    have hm : hw k le_rfl lam.natW ∈ nablaSq k N lam := hwMem k N N le_rfl _ hN.1
    rw [h, Submodule.mem_bot] at hm
    exact hwNe k N N le_rfl _ hm
  refine ⟨hne, fun M hM hG => ?_⟩
  by_contra hc
  push_neg at hc
  have key := GlobalTheory.T.highestWeightVector_mem_of_lt_stable_dualWeyl p hp k N lam.natW hN.1 (natW_alcove_bound p N lam hl)
  have good := GlobalTheory.T.isRowOperatorStable_dualWeyl_and_GLSubmodules k N lam
  have h1 := (key ⊥ M (good_top_bot k N N).2 (good.2 M hG) (bot_lt_iff_ne_bot.2 hc.1) hM).1
  have h2 := (key M (nablaSq k N lam) (good.2 M hG) good.1 (lt_of_le_of_ne hM hc.2) le_rfl).2
  exact h2 h1

end GlobalTheory.Alc
