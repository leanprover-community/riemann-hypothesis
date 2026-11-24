module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.EigOfQuot
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.IsOrdProjZeroOfIsNilpotent
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.quotOfEig :
    ∀ {K Y ι : Type*} [Field K] [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y] (A : ι → Module.End K Y), (∀ i j, Commute (A i) (A j)) → ∀ (x : ι → K) (y : Y), y ≠ 0 → (∀ i, A i y = x i • y) → ∃ φ : Module.Dual K Y, φ ≠ 0 ∧ ∀ i z, φ (A i z) = x i * φ z := by
  intro K Y ι _ _ _ _ A hA x y hy hAy
  have hc : ∀ i j, Commute (A i).dualMap (A j).dualMap := by
    intro i j
    show (A i).dualMap * (A j).dualMap = (A j).dualMap * (A i).dualMap
    refine LinearMap.ext fun ψ => LinearMap.ext fun z => ?_
    have h := LinearMap.congr_fun (hA j i).eq z
    simp only [Module.End.mul_apply] at h
    simp only [Module.End.mul_apply, LinearMap.dualMap_apply]
    rw [h]
  have hne : Module.Dual.eval K Y y ≠ 0 := by
    intro h0
    apply hy
    refine (Module.forall_dual_apply_eq_zero_iff K y).mp ?_
    intro ψ
    exact LinearMap.congr_fun h0 ψ
  obtain ⟨ψ, hψ, hψA⟩ := eigOfQuot (fun i => (A i).dualMap) hc x (Module.Dual.eval K Y y) hne (by
    intro i ψ
    simp [LinearMap.dualMap_apply, hAy])
  refine ⟨ψ, hψ, fun i z => ?_⟩
  have := LinearMap.congr_fun (hψA i) z
  simpa [LinearMap.dualMap_apply] using this
