module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Development
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def OTop : Prop :=
  IsCompact (OEv (E := E) v) ∧ IsOpen (OEv (E := E) v) ∧
  (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v ∧
  (∀ x ∈ OEv (E := E) v, ∀ y ∈ OEv (E := E) v, x * y ∈ OEv (E := E) v) ∧
  (∀ x ∈ OEv (E := E) v, ∀ y ∈ OEv (E := E) v, x + y ∈ OEv (E := E) v) ∧
  (∀ x ∈ OEv (E := E) v, -x ∈ OEv (E := E) v) ∧
  (∀ t ∈ v.adicCompletionIntegers F, ∀ x ∈ OEv (E := E) v, sc (E := E) v t * x ∈ OEv (E := E) v) ∧
  (∀ σ : E →ₐ[F] E, ∀ x ∈ OEv (E := E) v, sigR (Fv F v) σ x ∈ OEv (E := E) v)

def BoxMul : Prop :=
  ∀ (ι : Type) [Fintype ι] (μ : Measure (ι → Fv F v ⊗[F] E)) [μ.IsAddHaarMeasure]
    (y : ι → Fv F v ⊗[F] E), (∀ i, IsUnit (y i)) →
    (μ (Set.univ.pi fun i => {c | y i * c ∈ OEv (E := E) v})).toReal =
      (μ (Obox (E := E) v ι)).toReal * ∏ i, (absV v (Algebra.norm (Fv F v) (y i)))⁻¹

end PI.UnitaryGroupMassFormula.LocJacTyp
