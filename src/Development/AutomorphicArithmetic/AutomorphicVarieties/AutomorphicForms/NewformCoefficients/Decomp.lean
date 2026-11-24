module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.IntOfIntegers
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.KOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.StrongApp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

open NumberField Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Sd Matrix in
theorem UpperTheory.V.Af.Nf.decomp :
    UpperTheory.V.Af.Nf.Decomp := by
  intro M hM g
  obtain ⟨hK, hA⟩ := UpperTheory.V.Af.Nf.kOpen M hM
  obtain ⟨γ, h, y, u, hu, -, e⟩ := UpperTheory.V.Sd.strongApp ℚ _ hK g
  obtain ⟨r, u', -, hu', rfl⟩ := UpperTheory.V.Af.Nf.ratAd.1 y
  have h1 : aff (Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom r * u') 0 = toF (aff r 0) * aff u' 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [aff, toF, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨γ * aff r 0, (toR (aff r 0))⁻¹ * GeneralLinearGroup.map ev h, aff u' 0 * u,
    mul_mem (hA u' hu' 0 (zero_mem _)) hu, ?_⟩
  rw [e, h1, ← upR_ev, map_mul (ratGL ℚ 2), ratGL_eq (aff r 0), upR_comm (toR _), map_mul upR, map_inv upR, mul_assoc (toF _), map_mul (finGL ℚ 2) (toF _),
    ← mul_assoc (upR _), upR_comm _ (toF _)]
  simp only [mul_assoc, mul_inv_cancel_left]
