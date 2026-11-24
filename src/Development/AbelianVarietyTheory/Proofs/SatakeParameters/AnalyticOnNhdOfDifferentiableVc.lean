module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemMoveLevUloc
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel
import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.LtCNeZero
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.CoeffProdRename

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory

variable {D : D7}

theorem analyticOnNhd_of_differentiable_vc {N N' : ℕ} (H : TaylorLogMetric.VC D N N' → ℂ) (hH : Differentiable ℂ H) :
    AnalyticOnNhd ℂ H Set.univ := by
  let e : TaylorLogMetric.VC D N N' ≃L[ℂ] (Fin (Module.finrank ℂ (TaylorLogMetric.VC D N N')) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [Module.finrank_fin_fun])
  have h1 : AnalyticOnNhd ℂ (H ∘ e.symm) Set.univ :=
    ReciprocityTheory.AnForm.Osgood.osgood _ Set.univ (H ∘ e.symm) isOpen_univ
      (hH.comp e.symm.differentiable).differentiableOn
  have h2 : H = (H ∘ e.symm) ∘ e := by
    funext z
    simp
  rw [h2]
  exact h1.comp (e.toContinuousLinearMap.analyticOnNhd Set.univ) (Set.mapsTo_univ _ _)

theorem entire_algCoef_comb : ∀ (D : D7) {N N' m : ℕ} (c : Fin m → ℂ) (G : Fin m → TaylorLogMetric.VC D N N' → ℂ), (∀ k, c k ∈ TaylorLogMetric.Qbar) → (∀ k, Differentiable ℂ (G k) ∧ TaylorLogMetric.CoefIn D (G k) TaylorLogMetric.Qbar) → Differentiable ℂ (fun z => ∑ k, c k * G k z) ∧ TaylorLogMetric.CoefIn D (fun z => ∑ k, c k * G k z) TaylorLogMetric.Qbar := by
  intro D N N' m c G hc hG
  have hd : ∀ k, Differentiable ℂ (G k) := fun k => (hG k).1
  refine ⟨by fun_prop, fun α => ?_⟩
  have hsm : ∀ k (n : ℕ), ContDiff ℂ n (G k) := fun k n =>
    Formalism.L2.KerInert.ie_smooth (analyticOnNhd_of_differentiable_vc (G k) (hd k)) n
  rw [Formalism.L2.KerInert.ie_taylor_lin c G hsm α]
  exact sum_mem fun k _ => mul_mem (hc k) ((hG k).2 α)

end GlobalTheory
