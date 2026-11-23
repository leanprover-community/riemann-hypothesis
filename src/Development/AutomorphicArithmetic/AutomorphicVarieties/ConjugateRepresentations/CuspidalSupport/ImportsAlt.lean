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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.step :
    UpperTheory.V.Cj.S.PairEig → UpperTheory.V.Cj.S.SliceBdd → UpperTheory.V.Cj.S.Iwa → UpperTheory.V.Cj.S.CtCap → UpperTheory.V.Cj.S.CtSat → UpperTheory.V.Cj.S.CapRel → UpperTheory.V.Cj.S.HkRel → UpperTheory.V.Cj.S.CapArith → UpperTheory.V.Cj.S.SatArith → UpperTheory.V.Cj.S.Step := by
  intro hPair hSlice hIwa hCtCap hCtSat hCapRel hHkRel hCapA hSatA E _ _ _ r s φ₀ m B h₀ hne₀
  obtain ⟨φ, hφ, hne⟩ := hIwa E r s φ₀ m B h₀ hne₀
  obtain ⟨S₁, S₂, hS₁, hS₂, hs₁, hs₂⟩ := hSlice E r s φ hφ.aut
  obtain ⟨ψ, hψ, hNI, hcap⟩ := hCtCap E (r + s) r φ hφ.aut
  rw [← hψ] at hne hs₁ hs₂
  have hψ0 : ψ ≠ 0 := by
    rintro rfl
    obtain ⟨x, y, h⟩ := hne
    exact h rfl
  obtain ⟨φ₁, φ₂, m₁, m₂, B₁, B₂, h₁, h₂, hc, hs⟩ := hPair E r s (res ψ.1) S₁ S₂ hS₁ hS₂ hne hs₁ hs₂
  refine ⟨φ₁, φ₂, m₁, m₂, B₁, B₂, h₁, h₂, fun t => ?_, fun ν ν' hν hν' => ?_⟩
  · refine hCapA (m t) (m₁ t) (m₂ t) _ _ fun u => ?_
    have e1 : u + ((-((s : ℝ) / 2) : ℝ) : ℂ) = u - (s : ℂ) / 2 := by push_cast; ring
    have e2 : u + (((r : ℝ) / 2 : ℝ) : ℂ) = u + (r : ℂ) / 2 := by push_cast; ring
    rw [e1, e2]
    refine hc t _ _ _ _ (hCapRel E r s ψ hNI t u) fun x y => ?_
    rw [hcap t u, (hφ.cap t).2 u, hψ]
    simp only [res, constantTerm, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact MeasureTheory.integral_const_mul _ _
  · filter_upwards [hφ.sat, h₁.sat, h₂.sat, hs] with w hw hw₁ hw₂ hw₃
    have hv := hCtSat E (r + s) r φ ψ hφ.aut hψ hψ0 w (B w) hw
    obtain ⟨ϖ, hu⟩ := exists_isUnifV w
    refine hSatA (qV E w) r s (qV_ne_zero w) (B w) (B₁ w) (B₂ w) hw.2.2.1 hw₁.2.2.1 hw₂.2.2.1 (fun j hj => ?_) _ _ ?_ ?_
    · obtain ⟨G, hG, hsum⟩ := hHkRel E r s ψ hNI w hv.2.1 ϖ hu j hj
      refine hw₃ ϖ hu _ G _ hG fun x y => ?_
      rw [hsum x y]
      have : tOp (r + s) w hu j ψ = satEig (qV E w) (r + s) (B w) j • ψ := hv.2.2.2 ϖ hu j hj
      rw [this]
      rfl
    · rw [hν.2.1 w]
      congr 1
      push_cast; ring
    · rw [hν'.2.1 w]
      congr 1
      push_cast; ring
