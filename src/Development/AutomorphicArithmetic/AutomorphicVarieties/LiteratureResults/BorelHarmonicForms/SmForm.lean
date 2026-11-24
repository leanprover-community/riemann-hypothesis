module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.TformAdj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.smForm :
    UpperTheory.V.Lit.Bor.SmForm := by
  intro E _ _ _ a Ξ r H G hH hG X x hx y hy
  set c : ℂ := ((2 * r * ell E a (toL X.1) : ℝ) : ℂ) with hc
  have hcc : starRingEnd ℂ c = c := Complex.conj_ofReal _
  obtain ⟨h1, h2⟩ := UpperTheory.V.Lit.Bor.tformAdj (Sm E a) Ξ.d H (sqSub E a r) G (Ξ.dmat (toL X.1)) (Ξ.dmat (toL X.1))
    (lie E a (toL X.1)) (-lie E a (toL X.1) - c • 1)
  have hX : star X.1 = X.1 := X.2
  have e1 := h1 (by have := hG.adj X.1; rwa [hX] at this) x y
  have e2 := h2 (fun φ hφ ψ hψ => by
    have := hH.skew (toL X.1) φ hφ ψ hψ
    simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_neg,
      LinearMap.map_smulₛₗ, hcc, smul_eq_mul]
    rw [← hc] at this
    linear_combination this) x hx y hy
  have e3 : smLie Ξ (toL X.1) y = smA Ξ (toL X.1) y + smB Ξ (toL X.1) y := by
    simp [smB]
  have e4 : smAdj Ξ r (toL X.1) x = smB Ξ (toL X.1) x +
      (-lie E a (toL X.1) - c • (1 : Module.End ℂ (Sm E a))).rTensor _ x := by
    rw [smAdj, adj_apply, smA_apply, LinearMap.rTensor_sub, LinearMap.rTensor_neg, LinearMap.rTensor_smul,
      Module.End.one_eq_id, LinearMap.rTensor_id, ← algebraMap_smul ℂ (2 * r * ell E a (toL X.1)) x]
    simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [show algebraMap ℝ ℂ (2 * r * ell E a (toL X.1)) = c from rfl]
    abel
  rw [e3, e4, map_add (f := _), map_add (f := _), LinearMap.add_apply, smA_apply, smB_apply, e1, e2, add_comm]
