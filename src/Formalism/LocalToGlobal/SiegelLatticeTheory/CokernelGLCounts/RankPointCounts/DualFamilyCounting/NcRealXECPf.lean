module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXEC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXECPfA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXECPfB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXECPfC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.EC

open Formalism.QuantumDeterminants WlocSk.NB

theorem expChart_of (hS : ShearStep) (hC : ConstStep) : ExpChart := by
  intro k r
  obtain ⟨σ, hσ, hσe⟩ := hS k r
  obtain ⟨Λ, hΛm, hΛ, hvol⟩ := hC k r
  have hE := Formalism.MainNotions.BridgeCSB.continuous_expLie (k := k) (r := r) (Nset k r)
  let Φ : (CI k r → ℂ) × (Fin r → ℝ) → Mt k r := fun t => phi0 t.1 t.2
  have hφ : Continuous Φ := continuous_nilpotent_chart
  unfold Formalism.MainNotions.S.haarLie
  rw [one_smul, hvol, Measure.map_smul, Measure.map_map hE.measurable hΛm, ← hσ.map_eq]
  congr 1
  have e : ((fun x : Formalism.MainNotions.S.lieE (Nset k r) => fun i j =>
      NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) i j) ∘ Λ : (J k r → ℝ) → Mt k r) = Φ ∘ σ := by
    funext y
    simp only [Function.comp, Φ]
    rw [hσe y, hΛ y, Formalism.MainNotions.BridgeCSB.unrealify_RL]
  rw [e]
  exact (Measure.map_map hφ.measurable hσ.measurable).symm
  exact hE.measurable.aemeasurable

end Formalism.L2.SG.Pf.NcReal.JX.EC

namespace Formalism.L2.SG.Pf.NcReal.JX

theorem exponential_chart_haar : ExpChart := EC.expChart_of EC.shear_change_holds EC.constant_change_holds

end Formalism.L2.SG.Pf.NcReal.JX
