module

public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousTensMap
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff ENNReal

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}

theorem continuous_psiT (τ : D.what₂.Tau) : Continuous (psiT D τ) := by
  have heq : (psiT D τ : AE D → ℂ) = fun x => gW D (plW D τ) (fstA D.host.F ((basAF D).repr x 0)) +
      gW D (plW D τ) (fstA D.host.F ((basAF D).repr x 1)) * betaT D τ := by
    funext x
    simp only [psiT, RingHom.coe_comp, Function.comp_apply]
    rw [thetaC_decomp, repr_infPart, repr_infPart]
  rw [heq]
  have hc : ∀ k : Fin 2, Continuous fun x : AE D => (basAF D).repr x k := fun k => by
    have := (continuous_apply k).comp (G5.tensCoordH (basE D) (AF D.host.F)).continuous
    convert this using 1
    rfl
  have hf : Continuous (fstA D.host.F) := continuous_fst
  exact ((continuous_gW (D := D) _).comp (hf.comp (hc 0))).add
    (((continuous_gW (D := D) _).comp (hf.comp (hc 1))).mul continuous_const)

end Formalism.IndefR.Eqv

end
