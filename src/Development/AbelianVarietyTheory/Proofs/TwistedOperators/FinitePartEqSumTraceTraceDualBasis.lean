module

public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistCoords

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem trace_tmul_base {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [CommRing R] [Algebra F R] (r : R) (x : E) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] x) = r * algebraMap F R (Algebra.trace F E x) := by
  have h1 : (r ⊗ₜ[F] x : R ⊗[F] E) = r • ((1 : R) ⊗ₜ[F] x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem repr_eq_trace {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (x : E) (l : ι) :
    Algebra.trace F E
        ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b l * x) = b.repr x l := by
  have h := congrArg (Algebra.traceForm F E
      ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b l)) (b.sum_repr x)

  rw [map_sum] at h
  simp only [map_smul, LinearMap.BilinForm.apply_dualBasis_left, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [Algebra.traceForm_apply] at h
  exact h.symm

theorem coords_gen (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    ∃ (d : ℕ) (c e : Fin d → E), ∀ w : AF F ⊗[F] E,
      Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) w =
        ∑ l, sndA F (Algebra.trace (AF F) (AF F ⊗[F] E) (((1 : AF F) ⊗ₜ[F] c l) * w)) ⊗ₜ[F] e l := by
  classical
  let b := Module.finBasis F E
  refine ⟨_, fun l => (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b l, b, ?_⟩
  intro w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_tmul_base, map_mul,
      AlgHom.commutes, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    simp only [repr_eq_trace]
    conv_lhs => rw [← b.sum_repr x]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, mul_add, ← Finset.sum_add_distrib, TensorProduct.add_tmul]

end GlobalTheory.TwistCoords

namespace GlobalTheory.TwistCoords

theorem finPart_eq_sum_trace :
    ∀ (D : D7), ∃ (d : ℕ) (c e : Fin d → D.host.E), ∀ w : AE D, finPart D w =
      ∑ l, sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) (incA D (c l) * w)) ⊗ₜ[D.host.F] e l := by
  intro D
  obtain ⟨d, c, e, h⟩ := coords_gen D.host.F D.host.E
  exact ⟨d, c, e, fun w => h w⟩

end GlobalTheory.TwistCoords
