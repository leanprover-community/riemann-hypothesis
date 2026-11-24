module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Development
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef

@[expose] public section

noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.PairValDefs Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepGram (D : D7) : StepGram D := by
  intro T T' G G₁ G₂ n m N M hn hN hM hG
  unfold ZhatL Zhat brS frame at *
  have hiso : ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y := hn
  funext a b

  have hL : ∑ c, star (N c a) * (VS D).hT (G.fl.fvec c) (G₂.fl.fvec b) =
      (VS D).hT (n (G.fl.fvec a)) (G₂.fl.fvec b) := by
    rw [hN a]

    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, starRingEnd_apply]
  have hR : ∑ c, (VS D).hT (G.fl.fvec a) (G₁.fl.fvec c) * M c b =
      (VS D).hT (G.fl.fvec a) (m (G₁.fl.fvec b)) := by
    rw [hM b]

    simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  change ∑ c, star (N c a) * (VS D).hT (G.fl.fvec c) (G₂.fl.fvec b) =
    ∑ c, (VS D).hT (G.fl.fvec a) (G₁.fl.fvec c) * M c b
  rw [hL, hR, hG b, hiso]

end PI.NRCW
