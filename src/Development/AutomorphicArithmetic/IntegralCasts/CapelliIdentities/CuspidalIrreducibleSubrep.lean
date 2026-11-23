module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
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

noncomputable def UpperTheory.Reformulated.B.CuspidalIrreducibleSubrep.ev :
    {I : Type} →
      [Fintype I] →
        {W : I → Type} →
          [inst : (i : I) → AddCommGroup (W i)] →
            [inst_1 : (i : I) → _root_.Module ℂ (W i)] →
              ((i : I) → Module.Dual ℂ (W i)) → (PiTensorProduct ℂ fun (i : I) ↦ W i) →ₗ[ℂ] ℂ :=
    fun {I : Type} [Fintype I] {W : I → Type} [(i : I) → AddCommGroup (W i)] [(i : I) → _root_.Module ℂ (W i)]
        (f : (i : I) → Module.Dual ℂ (W i)) ↦
      (PiTensorProduct.lift : ((∀ i, W i) →ₘₗ[ℂ] ℂ) → (PiTensorProduct ℂ fun (i : I) ↦ W i) →ₗ[ℂ] ℂ)
        ((MultilinearMap.mkPiAlgebra ℂ I ℂ).compLinearMap f)

theorem UpperTheory.Reformulated.B.CuspidalIrreducibleSubrep.ev_tprod :
    ∀ {I : Type} [inst : Fintype I] [dI : DecidableEq I] {W : I → Type} [inst_1 : (i : I) → AddCommGroup (W i)]
      [inst_2 : (i : I) → _root_.Module ℂ (W i)] (f : (i : I) → Module.Dual ℂ (W i)) (m : (i : I) → W i),
      (UpperTheory.Reformulated.B.CuspidalIrreducibleSubrep.ev f : (PiTensorProduct ℂ fun (i : I) ↦ W i) → ℂ)
          ((PiTensorProduct.tprod ℂ : ((i : I) → W i) → PiTensorProduct ℂ fun (i : I) ↦ W i) m) =
        ∏ i : I, (f i : W i → ℂ) (m i) := by
  intro I _ _ W _ _ f m
  simp [UpperTheory.Reformulated.B.CuspidalIrreducibleSubrep.ev]
