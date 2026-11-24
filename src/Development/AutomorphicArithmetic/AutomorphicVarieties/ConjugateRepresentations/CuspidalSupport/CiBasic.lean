module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing in
private theorem one_mem_centerU (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    UniversalEnvelopingAlgebra.ι ℝ (UpperTheory.V.Cm.lieEq E a (oneL E a)) ∈ (isExpLieAlgebra E a).centerU := by
  refine Subalgebra.mem_center_iff.2 fun u => ?_
  induction u using GroundTheory.Automorphic.AutomorphicForm.UEnv.induction with
  | halg r => exact Algebra.commutes r _
  | hι Y =>
    have h : ⁅Y, UpperTheory.V.Cm.lieEq E a (oneL E a)⁆ = 0 := by
      refine Subtype.ext ?_
      rw [LieSubalgebra.coe_bracket, UpperTheory.V.Cm.lieEq_oneL, Ring.lie_def, mul_one, one_mul, sub_self]
      rfl
    rw [← sub_eq_zero, ← Ring.lie_def, ← LieHom.map_lie, h, map_zero]
  | hmul x y hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  | hadd x y hx hy => rw [add_mul, mul_add, hx, hy]

private theorem scalar_of_mem_Zalg {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (m : (E →+* ℂ) → Multiset ℂ) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∃ c : ℂ, ∀ φ ∈ CI a m, z φ = c • φ := by
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨t, u, rfl⟩ := hz
    exact ⟨_, fun φ hφ => (mem_CI.1 hφ).2 t u⟩
  | algebraMap r => exact ⟨r, fun φ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨c + d, fun φ hφ => by rw [LinearMap.add_apply, hc φ hφ, hd φ hφ, add_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨d * c, fun φ hφ => by rw [Module.End.mul_apply, hd φ hφ, map_smul, hc φ hφ, mul_smul]⟩

theorem UpperTheory.V.Cj.S.ciBasic :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.CiBasic := by
  intro hc E _ _ _ a m
  refine ⟨fun o φ hφ => mem_CI.2 ⟨UpperTheory.V.Cm.isCuspForm_act o (mem_CI.1 hφ).1, fun t u => ?_⟩, ?_⟩
  · have h := LinearMap.congr_fun ((hc E a t u).2.1 o).eq φ
    rw [Module.End.mul_apply, Module.End.mul_apply, (mem_CI.1 hφ).2 t u, map_smul] at h
    exact h
  · rw [← UpperTheory.V.Cm.uTC_ι]
    exact scalar_of_mem_Zalg m (UpperTheory.V.Cm.uTC_mem_Zalg (one_mem_centerU E a))
