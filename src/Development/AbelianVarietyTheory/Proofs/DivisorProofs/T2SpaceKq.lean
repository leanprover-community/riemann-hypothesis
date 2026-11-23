module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.LKMid GlobalTheory.LKTrip GlobalTheory.LKRes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LKMid

theorem t2Space_kq {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) :
    T2Space (KQ p K r) := by
  haveI : IsModuleTopology ℚ_[p] (KQ p K r) := ⟨rfl⟩
  let b := Module.Free.chooseBasis ℚ_[p] (KQ p K r)
  let φ : KQ p K r →ₗ[ℚ_[p]] (Module.Free.ChooseBasisIndex ℚ_[p] (KQ p K r) → ℚ_[p]) :=
    Finsupp.lcoeFun ∘ₗ b.repr.toLinearMap
  have hinj : Function.Injective φ := by
    intro x y h
    apply b.repr.injective
    exact DFunLike.coe_injective h
  exact T2Space.of_injective_continuous hinj (IsModuleTopology.continuous_of_linearMap φ)

end GlobalTheory.LKMid
