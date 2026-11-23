module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyDvdPowOfAevalEqZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsAlt
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero

@[expose] public section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.IntegralFinite

open Matrix

theorem isIntegral_matrix_trace {R F : Type} [CommRing R] [Field F] [Algebra R F] {n : Type}
    [Fintype n] [DecidableEq n] (M : Matrix n n F) (hM : IsIntegral R M) : IsIntegral R M.trace := by
  first
  | exact @_root_.GlobalTheory.TargetStatementAlt.target
  | exact _root_.GlobalTheory.TargetStatementAlt.target
  | (apply _root_.GlobalTheory.TargetStatementAlt.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetStatementAlt.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetStatementAlt.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetStatementAlt.target ..)

variable {K : UQ} (B : InvAlg K)

theorem isIntegral_trace {x : B.A} (hx : IsIntegral K.O x) :
    IsIntegral K.O (Algebra.trace K.E B.A x) := by
  let bs := Module.finBasis K.E B.A
  rw [Algebra.trace_eq_matrix_trace bs]
  exact isIntegral_matrix_trace _ (hx.map ((Algebra.leftMulMatrix bs).restrictScalars K.O))

theorem trace_mem_range {x : B.A} (hx : IsIntegral K.O x) :
    ∃ c : K.O, algebraMap K.O K.E c = Algebra.trace K.E B.A x :=
  IsIntegrallyClosed.isIntegral_iff.mp (isIntegral_trace B hx)

theorem finite_integralClosure :
    ∀ (K : UQ) (B : InvAlg K), B.P.Separable → Module.Finite K.O (integralClosure K.O B.A) := by
  intro K B hsep
  classical
  let bs := Module.finBasis K.E B.A
  haveI : Algebra.IsAlgebraic K.O K.E := IsLocalization.isAlgebraic K.E (nonZeroDivisors K.O)
  haveI : Algebra.IsAlgebraic K.O B.A := Algebra.IsAlgebraic.trans K.O K.E B.A
  obtain ⟨y, hy, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples K.O (Finset.univ.image bs)
  have hy' : algebraMap K.O K.E y ≠ 0 := by
    intro h
    exact hy (IsFractionRing.injective K.O K.E (by rw [h, map_zero]))
  let b := bs.isUnitSMul (w := fun _ => algebraMap K.O K.E y) (fun _ => (Ne.isUnit hy'))
  have hbint : ∀ i, IsIntegral K.O (b i) := by
    intro i
    have h := hint (bs i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    simpa [b, Module.Basis.isUnitSMul_apply, algebraMap_smul] using h
  have hnd : (Algebra.traceForm K.E B.A).Nondegenerate := by
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · exact Centraliser.eq_zero_of_trace_mul B hsep a (fun z => by simpa [Algebra.traceForm_apply] using ha z)
    · exact Centraliser.eq_zero_of_trace_mul B hsep a
        (fun z => by simpa [Algebra.traceForm_apply, mul_comm] using ha z)
  let d := (Algebra.traceForm K.E B.A).dualBasis hnd b
  have hle : Subalgebra.toSubmodule (integralClosure K.O B.A) ≤ Submodule.span K.O (Set.range d) := by
    intro x hx
    have hx' : IsIntegral K.O x := hx
    rw [← d.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := trace_mem_range B (hx'.mul (hbint i))
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, ← hc, algebraMap_smul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨i, rfl⟩)
  haveI : IsNoetherian K.O (Submodule.span K.O (Set.range d)) :=
    isNoetherian_span_of_finite K.O (Set.finite_range d)
  haveI : IsNoetherian K.O (Subalgebra.toSubmodule (integralClosure K.O B.A)) := isNoetherian_of_le hle
  exact Module.IsNoetherian.finite K.O (Subalgebra.toSubmodule (integralClosure K.O B.A))

end GlobalTheory.UnitLemma.IntegralFinite
