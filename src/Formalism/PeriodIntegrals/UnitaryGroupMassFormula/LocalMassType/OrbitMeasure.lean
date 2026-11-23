module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.OmMeas
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.ContinuousHRRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.IsTopRingTens
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.IsClosedCongruenceSubgroup
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.LocMassTypM

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct
open PI.LocMassTypW

theorem orbit_measure : OmMeas := by
  intro F E _ _ _ _ _ σ n J ψ v r g P P' Λ T T' κ μG μS0 μS0' hyp
  obtain ⟨-, -, -, hSD, -, hg, hgv, -⟩ := hyp
  have hKv : IsClosed (Formalism.L2.SG.TypedSets.Kv σ J Λ v) := LocMassOrdKv.isClosed_Kv σ J v Λ hSD
  have hK1 : IsClosed (K1 σ J v Λ g P) := isClosed_congruence_subgroup σ J v Λ hSD hg P

  have hK1' : ∀ k : HA (Fv F v) σ J, IsClosed {c | k⁻¹ * c * κ⁻¹ ∈ K1 σ J v Λ g P} := fun k =>
    hK1.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  exact ⟨measurableSet_omTyp v Λ σ J hSD hg hgv r, LocMassOrdKv.kv_measurableSet σ J v Λ hSD,
    hK1.measurableSet, measurableSet_image_closed σ J v hKv _,
    fun k => measurableSet_image_closed σ J v (hK1' k) _⟩

end PI.LocMassTypM
