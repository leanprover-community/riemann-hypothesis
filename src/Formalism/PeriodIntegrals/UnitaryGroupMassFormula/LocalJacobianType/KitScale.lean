module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitAbs
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem norm_sc (hfin : Module.finrank F E = 2) (x : Fv F v) :
    Algebra.norm (Fv F v) (sc (E := E) v x) = x ^ 2 := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have h1 : sc (E := E) v x = algebraMap (Fv F v) (Fv F v ⊗[F] E) x := by
    simp [PI.LocJacTyp.sc, Algebra.TensorProduct.algebraMap_apply]
  rw [h1, Algebra.norm_algebraMap, Module.finrank_baseChange, hfin]

theorem boxScale {ι : Type} [Fintype ι] (hfin : Module.finrank F E = 2)
    (μ : Measure (ι → Fv F v ⊗[F] E)) [μ.IsAddHaarMeasure] (x : ι → Fv F v) (hx : ∀ i, x i ≠ 0) :
    (μ (Set.univ.pi fun i => {c | sc (E := E) v (x i) * c ∈ OEv (E := E) v})).toReal =
      (μ (Obox (E := E) v ι)).toReal * ∏ i, (absV v (x i) ^ 2)⁻¹ := by
  have hu : ∀ i, IsUnit (sc (E := E) v (x i)) := fun i =>
    (isUnit_iff_ne_zero.2 (hx i)).map (algebraMap (Fv F v) (Fv F v ⊗[F] E))
  rw [BM.box_measure_mul (E := E) v ι μ _ hu]
  simp only [norm_sc v hfin, absV_pow]

end PI.UnitaryGroupMassFormula.LocJacTyp
