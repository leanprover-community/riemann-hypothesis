module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1InterGamma0ModularFormHasSumQExpansionStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem eq_of_coef_eq : ∀ (N l : ℕ) (k : ℤ), 0 < N → ∀ f g : ModularForm (GlobalTheory.Hk.lev N l) k,
    (∀ n, GlobalTheory.Hk.coef ⇑f n = GlobalTheory.Hk.coef ⇑g n) → f = g := by
  intro N l k hN f g h
  ext τ
  have hf := GlobalTheory.T.gamma1InterGamma0_modularForm_hasSum_qExpansion N l k hN f τ
  have hg := GlobalTheory.T.gamma1InterGamma0_modularForm_hasSum_qExpansion N l k hN g τ
  simp_rw [h] at hf
  exact hf.unique hg

end GlobalTheory.Hk
