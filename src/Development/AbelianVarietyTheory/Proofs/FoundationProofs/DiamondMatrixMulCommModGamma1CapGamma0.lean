module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

namespace GlobalTheory.KZ

theorem isDiam_mul_comm_mod_Gam (N l d d' : ℕ) (σ σ' : SL(2, ℤ)) (h : IsDiam N l d σ) (h' : IsDiam N l d' σ') :
    ∃ g : SL(2, ℤ), g ∈ Gam N l ∧ σ' * σ = g * (σ * σ') := by
  obtain ⟨⟨h0, h1⟩, -⟩ := h
  obtain ⟨⟨h0', h1'⟩, -⟩ := h'
  refine ⟨σ' * σ * (σ * σ')⁻¹, ⟨?_, ?_⟩, by group⟩
  · set a : CongruenceSubgroup.Gamma0 N := ⟨σ, h0⟩ with ha
    set b : CongruenceSubgroup.Gamma0 N := ⟨σ', h0'⟩ with hb
    have hu : (CongruenceSubgroup.Gamma0Map N).toHomUnits (b * a * (a * b)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul,
        mul_comm ((CongruenceSubgroup.Gamma0Map N).toHomUnits b), mul_inv_cancel]
    have h3 : b * a * (a * b)⁻¹ ∈ CongruenceSubgroup.Gamma1' N := by
      rw [CongruenceSubgroup.Gamma1_mem', ← MonoidHom.coe_toHomUnits, hu, Units.val_one]
    exact (CongruenceSubgroup.Gamma1_mem N _).2 ((CongruenceSubgroup.Gamma1_to_Gamma0_mem _).1 h3)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1' h1) (Subgroup.inv_mem _ (Subgroup.mul_mem _ h1 h1'))

end GlobalTheory.KZ
