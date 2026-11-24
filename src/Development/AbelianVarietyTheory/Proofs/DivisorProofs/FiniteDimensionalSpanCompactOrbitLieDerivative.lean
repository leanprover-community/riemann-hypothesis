module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
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
import Mathlib.RingTheory.Finiteness.Lattice
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

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep.KFin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem cptRep_lie (k : Kinf E a) (X : Lie E a) (ψ : Sm E a) :
    cptRep E a k (lie E a X ψ) =
      lie E a (toL ((Unitary.toUnits k).val * Matrix.of X * (Unitary.toUnits k)⁻¹.val)) (cptRep E a k ψ) := by
  set y : GL (Fin a) (Cinf E) := Unitary.toUnits k with hy
  set Z : Lie E a := toL (y.val * Matrix.of X * y⁻¹.val) with hZ
  refine Subtype.ext (funext fun g => ?_)
  change lieD X ψ.1 (g * infGL E a y) = lieD Z (fun x => ψ.1 (x * infGL E a y)) g
  rw [← chart_val (lieD X ψ.1) g y, chart_lieD ψ.2 X g (val_mem_invSet y), lieD, chart_rt_inf]
  have e1 : rmul (toL y.val) (oneL E a) = toL y.val := one_mul (Matrix.of (toL y.val))
  rw [fderiv_comp _ (by rw [e1]; exact (contDiffAt_chart ψ.2 g (val_mem_invSet y)).differentiableAt (by simp))
    (rmul (toL y.val)).differentiableAt, ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, e1]
  congr 1
  change (y.val : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of X = (y.val * Matrix.of X * y⁻¹.val) * (y.val : Matrix (Fin a) (Fin a) (Cinf E))
  rw [mul_assoc, Units.inv_mul, mul_one]

theorem kfin_lie (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Lie E a) (φ : Sm E a)
    (hφ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k (lie E a X φ))) := by
  set V := Submodule.span ℂ (Set.range fun k => cptRep E a k φ)
  let b := Module.finBasis ℝ (Lie E a)
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, V.map (lie E a (b i))) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  rw [SetLike.mem_coe]
  change cptRep E a k (lie E a X φ) ∈ _

  rw [cptRep_lie, ← b.sum_repr (toL _), map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul, LinearMap.smul_apply]
  exact Submodule.smul_of_tower_mem _ _ (Submodule.mem_iSup_of_mem i
    (Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, rfl⟩)))

end GlobalTheory.CuspRep.KFin
