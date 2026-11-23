module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLatticeGLConjLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermModerateGrowth
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.latCount :
    UpperTheory.V.Cj.H.LatCount := by
  intro E _ _ _ a _ S hS g
  obtain ⟨A, hA⟩ := GlobalTheory.card_latticeGL_conj_le E a
  set c : GL (Fin a) (Cinf E) := GeneralLinearGroup.map (pInf E) g with hc
  set f : GA E a := finGL E a (GeneralLinearGroup.map (pFin E) g) with hf
  obtain ⟨C, hC0, hC⟩ := hA ((fun s => f * s * f⁻¹) '' S) (hS.image (by fun_prop))
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.ConstTermGrowth.height_mul_left_le (E := E) (isCompact_singleton (x := c))
  refine ⟨C * B ^ (2 * A), 2 * A, fun y => ?_⟩
  obtain ⟨hfin, hle⟩ := hC (c * y)
  have hg : g * infGL E a y = infGL E a (c * y) * f := by
    refine ga_ext ?_ ?_
    · simp only [map_mul, hf, pInf_infGL, pInf_finGL, mul_one, hc]
    · simp only [map_mul, hf, pFin_infGL, pFin_finGL, mul_one, one_mul]
  refine ⟨_, hle.trans ?_, ?_⟩
  · have h0 : 0 ≤ GlobalTheory.CuspRep.height (c * y) := zero_le_one.trans (one_le_height _)
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (hB c rfl y) _) hC0
  · rw [hfin.cast_ncard_eq]
    refine Set.encard_le_encard fun γ hγ => ⟨_, hγ, ?_⟩
    rw [hg]
    group
