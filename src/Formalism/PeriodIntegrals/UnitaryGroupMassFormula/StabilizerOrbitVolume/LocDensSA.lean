module

public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.FiniteNeighbourhoodSecond
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open IsDedekindDomain NumberField

namespace PI.VolStabSW

def SAf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (U : AddSubgroup (FiniteAdeleRing (𝓞 F) F)),
    IsOpen (U : Set (FiniteAdeleRing (𝓞 F) F)) →
    ∀ x : FiniteAdeleRing (𝓞 F) F, ∃ a : F, x - algebraMap F (FiniteAdeleRing (𝓞 F) F) a ∈ U

theorem sAf_holds : SAf := by
  intro F _ _ U hU x
  obtain ⟨N, hN, hNU⟩ := PI.InvTopW.finite_neighbourhood_second F (U : Set (FiniteAdeleRing (𝓞 F) F)) (hU.mem_nhds U.zero_mem)
  obtain ⟨m, hm, hmx⟩ := PIW.AdelClassFin.DictRing.af_denom (F := F) x
  obtain ⟨β, y, hy, e⟩ := PIW.AdelClassFin.DictRing.af_approx (F := F) _ hmx (m * N) (Nat.mul_pos hm (by omega))
  refine ⟨(β : F) / m, ?_⟩
  have hm0 : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hu : (m : FiniteAdeleRing (𝓞 F) F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) ((m : F)⁻¹) = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) m, ← map_mul, mul_inv_cancel₀ hm0, map_one]
  have hβ : algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) β = algebraMap F (FiniteAdeleRing (𝓞 F) F) (β : F) :=
    IsScalarTower.algebraMap_apply (𝓞 F) F _ β
  have hdiv : algebraMap F (FiniteAdeleRing (𝓞 F) F) ((β : F) / m) =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (β : F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) ((m : F)⁻¹) := by
    rw [div_eq_mul_inv, map_mul]
  have key : x - algebraMap F (FiniteAdeleRing (𝓞 F) F) ((β : F) / m) = (N : FiniteAdeleRing (𝓞 F) F) * y := by
    rw [hdiv, ← hβ]
    push_cast at e
    linear_combination algebraMap F (FiniteAdeleRing (𝓞 F) F) ((m : F)⁻¹) * e -
      (x - (N : FiniteAdeleRing (𝓞 F) F) * y) * hu
  rw [key]
  exact hNU y hy

end PI.VolStabSW
