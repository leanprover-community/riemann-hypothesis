module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import ReciprocityTheory.NeutralLocalFields.HilbertClassField

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem fixed_mem_Kur {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    (hK : FiniteDimensional ℚ_[l] K) (y : PadicAlgCl l)
    (h : ∀ ρ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l, (∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖ρ z - z‖ < 1) → ρ y = y) :
    y ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l K := by
  rw [ReciprocityTheory.DiscreteGroups.LocalClassField.mem_iff_fixed (ReciprocityTheory.DiscreteGroups.LocalClassField.le_Kur (p := l) (K := K)) y]
  intro σ hσ
  exact h σ ((ReciprocityTheory.DiscreteGroups.LocalClassField.mem_subG_Kur_iff hK σ).1 hσ)

end ReciprocityTheory.ChartRestriction.L1
