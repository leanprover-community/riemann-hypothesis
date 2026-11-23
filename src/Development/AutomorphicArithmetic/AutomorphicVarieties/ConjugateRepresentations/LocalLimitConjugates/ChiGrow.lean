module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
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
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.chiGrow :
    UpperTheory.V.Cj.H.ChiGrow := by
  intro E _ _ _ a χ s _ φ hφ g
  obtain ⟨A, p, hA⟩ := hφ g
  obtain ⟨B, q, hB⟩ := chiDet_growth (a := a) χ⁻¹
  have hback : mulChi a χ⁻¹ (mulChi a χ φ) = φ := by
    rw [← mulChi_mul, mul_inv_cancel, mulChi_one]
  refine ⟨‖((chiDet a χ⁻¹ g : ℂˣ) : ℂ)‖ * (A * B), p + q, fun y => ?_⟩
  have e : φ.1 (g * infGL E a y) = ((chiDet a χ⁻¹ g : ℂˣ) : ℂ) *
      ((mulChi a χ φ).1 (g * infGL E a y) * ((chiDet a χ⁻¹ (infGL E a y) : ℂˣ) : ℂ)) := by
    conv_lhs => rw [← hback, mulChi_apply, map_mul, Units.val_mul]
    ring
  have hprod := mul_le_mul (hA y) (hB y) (norm_nonneg _) ((norm_nonneg _).trans (hA y))
  calc ‖φ.1 (g * infGL E a y)‖
      = ‖((chiDet a χ⁻¹ g : ℂˣ) : ℂ)‖ * (‖(mulChi a χ φ).1 (g * infGL E a y)‖ *
          ‖((chiDet a χ⁻¹ (infGL E a y) : ℂˣ) : ℂ)‖) := by rw [e, norm_mul, norm_mul]
    _ ≤ ‖((chiDet a χ⁻¹ g : ℂˣ) : ℂ)‖ * (A * GlobalTheory.CuspRep.height y ^ p * (B * GlobalTheory.CuspRep.height y ^ q)) :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = _ := by rw [pow_add]; ring
