module

public import GroundTheory.GlobalFields.HerbrandQuotients.Cyclic
public import GroundTheory.GlobalFields.HerbrandQuotients.CycTate
public import Mathlib.Basic.Real.Basic
public import GroundTheory.GlobalFields.HerbrandQuotients.Lattice
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Global

open MulAction
open scoped TensorProduct

variable {G : Type*} [Group G] [Fintype G]

theorem cyclicHerbrand_eq_cycHerbrand {M : Type*} [AddCommGroup M] (ρ : Representation ℤ G M)
    (σ : G) : cyclicHerbrand ρ σ = cycHerbrand ρ σ :=
  rfl

theorem cycHerbrand_trivial_int (σ : G) :
    cycHerbrand (Representation.trivial ℤ G ℤ) σ = Fintype.card G :=
  cyclicHerbrand_trivial_int σ

theorem cycHerbrand_eq_of_real_equiv {M M' : Type*} [AddCommGroup M] [Module.Finite ℤ M]
    [Module.Free ℤ M] [AddCommGroup M'] [Module.Finite ℤ M'] [Module.Free ℤ M']
    (ρ : Representation ℤ G M) (ρ' : Representation ℤ G M') (σ : G)
    (e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] M')
    (he : ∀ g x, e ((ρ g).baseChange ℝ x) = (ρ' g).baseChange ℝ (e x)) :
    cycHerbrand ρ σ = cycHerbrand ρ' σ :=
  cyclicHerbrand_eq_of_real_equiv ρ ρ' σ e he

end GroundTheory.Global
