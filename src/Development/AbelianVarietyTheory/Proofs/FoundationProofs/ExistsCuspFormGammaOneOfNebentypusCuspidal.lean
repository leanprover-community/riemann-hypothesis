module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
public import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem cuspForm_of_chiInv : ∀ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < N →
    CuspAll k G → ChiInv k N N χ G → ∃ f : CuspForm (Gamma1 N) k, ⇑f = G := by
  intro N k χ G _ hC hχ
  refine ⟨{ toFun := G
            slash_action_eq' := fun A hA => ?_
            holo' := hC.1
            zero_at_cusps' := fun {c} hc => hC.2 c (hc.mono ?_) }, rfl⟩
  · obtain ⟨A, hA, rfl⟩ := hA
    have hA0 : A ∈ Gamma0 N := Gamma1_in_Gamma0 N hA
    have h11 : ((mat A 1 1 : ℤ) : ZMod N) = 1 := ((Gamma1_mem N A).1 hA).2.1
    have := hχ A hA0
    rw [h11, map_one, one_smul, ModularForm.SL_slash] at this
    exact this
  · rintro _ ⟨γ, -, rfl⟩; exact ⟨γ, rfl⟩
end GlobalTheory.HeckeFamilyMatrices
