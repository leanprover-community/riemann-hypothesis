module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Formalism.FormalDegreeBessel.StatementWR

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.Dec.CuspFrame

theorem one_mem_Kg (I : AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  refine ⟨?_, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
  · simp [AutInst.Kset]
  · simp [AutInst.fmat]

theorem re_fixed (B : RowsAut) : ∀ k ∈ B.I.Kg B.g, (B.R (1, k)).comp B.Re = B.Re := by
  intro k hk
  obtain ⟨h1, hm, hn, -, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  have pm : ∀ a b : B.I.Gf, B.R (1, a * b) = B.R (1, a) * B.R (1, b) := fun a b => by
    have := hm (1, a) (1, b)
    rwa [Prod.mk_mul_mk, mul_one] at this
  have ir : ∀ (a : B.I.Gf) (x z : B.I.L2 B.μf B.fund), ⟪x, B.R (1, a) z⟫_ℂ = ⟪B.R (1, a⁻¹) x, z⟫_ℂ :=
    fun a x z => by
      have hback : B.R (1, a) (B.R (1, a⁻¹) x) = x := by
        have hident : B.R (1, 1) = 1 := h1
        have h := congrArg (fun S : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => S x)
          (pm a a⁻¹)
        simpa [hident, mul_apply_eq_comp] using h.symm
      let U : B.I.L2 B.μf B.fund →ₗᵢ[ℂ] B.I.L2 B.μf B.fund :=
        ⟨(B.R (1, a)).toLinearMap, hn (1, a)⟩
      calc
        ⟪x, B.R (1, a) z⟫_ℂ = ⟪U (B.R (1, a⁻¹) x), U z⟫_ℂ := by
          change ⟪x, B.R (1, a) z⟫_ℂ = ⟪B.R (1, a) (B.R (1, a⁻¹) x), B.R (1, a) z⟫_ℂ
          rw [hback]
        _ = ⟪B.R (1, a⁻¹) x, z⟫_ℂ := U.inner_map_map _ _
  have he : ∀ x, B.e (k * x) = B.e x := fun x => by
    have := B.e_adm.2.2.2.2.2.1 x k hk 1 (one_mem_Kg B.I B.g)
    rwa [mul_one] at this
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply, ir k, B.Re_spec.2, B.Re_spec.2,
    ← MeasureTheory.integral_mul_left_eq_self (fun g => B.e g * ⟪x, B.R (1, g) y⟫_ℂ) k]
  congr 1
  ext g
  rw [he, pm, mul_apply_eq_comp, ir k x]

end GlobalTheory.Dec.CuspFrame
