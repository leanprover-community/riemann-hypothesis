module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContSplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.TensTopOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousTensMap
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

namespace PI.UnitaryGroupMassFormula.MeasWCore

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures NumberField
open scoped TensorProduct

theorem continuous_haMap {F E : Type} [Field F] [Field E] [Algebra F E]
    {R R' : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [CommRing R'] [Algebra F R']
    [TopologicalSpace R'] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (φ : R →ₐ[F] R')
    (hφ : Continuous (tensMap (E := E) φ)) : Continuous (haMap σ J φ) := by
  have hmat : Continuous (fun g : HA R σ J => (HA.mat R σ J g : GL (Fin n) (R ⊗[F] E))) :=
    continuous_subtype_val
  have key : Continuous (fun g : HA R σ J =>
      (Formalism.UG.bc (tensMap (E := E) φ) (HA.mat R σ J g) : GL (Fin n) (R' ⊗[F] E))) := by
    rw [Units.continuous_iff]
    constructor
    · change Continuous (fun g : HA R σ J =>
        ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map
          (tensMap (E := E) φ))
      exact (Units.continuous_val.comp hmat).matrix_map hφ
    · change Continuous (fun g : HA R σ J =>
        (((HA.mat R σ J g)⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map
          (tensMap (E := E) φ))
      exact (Units.continuous_coe_inv.comp hmat).matrix_map hφ
  exact continuous_induced_rng.2 key

theorem continuous_measure_splitting : ContSplit := by
  intro F E _ _ _ _ _ σ n J _
  have : FiniteDimensional F E := PI.VolSemiDirect.W.Lc.finite_nf F E
  exact (continuous_haMap σ J (fstA F)
      (continuous_tensMap (AF F) (fstA F) continuous_fstA)).prodMk
    (continuous_haMap σ J (sndA F) (continuous_tensMap (AF F) (sndA F) continuous_sndA))

end PI.UnitaryGroupMassFormula.MeasWCore
