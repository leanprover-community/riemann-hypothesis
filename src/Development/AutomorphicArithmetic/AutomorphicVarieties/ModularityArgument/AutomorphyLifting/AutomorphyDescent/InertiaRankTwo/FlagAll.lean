module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.DownCsdK
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open UpperTheory.V.Z.Win.Dn
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.BasicNotions UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win
open scoped Pointwise

theorem UpperTheory.V.Z.Win.Dn.flagAll_of :
    FlagAll := by
  intro F Ω _ _ _ _ _ l _ n r h v hv B hB
  obtain ⟨A, hA, κ, P, hP⟩ := h v hv
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hA hB
  have hmem : ∀ s ∈ Dec (F := F) (g • A), g⁻¹ * s * g ∈ Dec (F := F) A := fun s hs => by
    have h1 : s • g • A = g • A := hs
    show (g⁻¹ * s * g) • A = A
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  let d : ↥(Dec (F := F) (g • A)) →* ↥(Dec (F := F) A) :=
    { toFun := fun s => ⟨g⁻¹ * s * g, hmem s s.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp [mul_assoc] }
  refine ⟨fun i => (κ i).comp d, P * r g⁻¹, fun s => ?_⟩
  have e : P * r g⁻¹ * r s * (P * r g⁻¹)⁻¹ = P * r (d s) * P⁻¹ := by
    show _ = P * r (g⁻¹ * s * g) * P⁻¹
    rw [map_mul, map_mul, map_inv]
    group
  rw [e]
  exact hP (d s)
