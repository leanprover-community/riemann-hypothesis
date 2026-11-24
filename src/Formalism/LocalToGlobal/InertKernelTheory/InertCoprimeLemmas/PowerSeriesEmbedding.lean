module

public import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
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
public import Mathlib.RingTheory.Algebraic.Cardinality
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
public import ReciprocityTheory.ReductiveGroups.LatticeEmbeddings.IotaPlaceB

@[expose] public section

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions

theorem lattice_extension : LamExt := by
  intro p _ lam
  have : Algebra.IsAlgebraic ℚ Formalism.MainNotions.TaylorLogMetric.Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  have hR : Cardinal.mk Formalism.MainNotions.TaylorLogMetric.Qbar ≤ Cardinal.aleph0 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ Formalism.MainNotions.TaylorLogMetric.Qbar).trans
      (max_le Cardinal.mk_le_aleph0 le_rfl)
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.ChartRestriction.B3.iop_extEmb (algebraMap Formalism.MainNotions.TaylorLogMetric.Qbar ℂ) lam hR
    (by simp [Cardinal.mk_complex, Cardinal.aleph0_lt_continuum])
    (Cardinal.mk_complex.trans (ReciprocityTheory.ChartRestriction.T1.lat_mk_Cp p).symm)
  exact ⟨σ, fun x => hσ x⟩

theorem lattice_embedding : LamCIota := by
  intro p _ lam ι h
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · unfold Formalism.MainNotions.TaylorLogMetric.lamC
    rw [dite_eq_left hx]
    exact (h ⟨x, hx⟩).symm
  · unfold Formalism.MainNotions.TaylorLogMetric.lamC
    rw [dite_eq_right hx]

theorem power_series_embedding : PSerIota := by
  intro D N N' p _ lam ι h G hG
  ext α
  rw [MvPowerSeries.coeff_map]
  change Formalism.MainNotions.TaylorLogMetric.lamC lam (Formalism.MainNotions.TaylorLogMetric.taylor D G α) = ι (Formalism.MainNotions.TaylorLogMetric.taylor D G α)
  exact (lattice_embedding p lam ι h).1 _ (hG α)

end Formalism.L2.KerInert
