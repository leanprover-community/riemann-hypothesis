module

public import Formalism.CharacterColumnKernels.Statement
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem ko_killed_by_pow_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ x : Formalism.NG.KO O, ∃ n : ℕ, ϖ ^ n • x = 0 := by
  intro O _ _ _ ϖ hϖ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) y
  have hb : (b : O) ≠ 0 := nonZeroDivisors.ne_zero b.2
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  refine ⟨n, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
  refine ⟨a * ((u⁻¹ : Oˣ) : O), ?_⟩
  rw [Algebra.smul_def, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.eq_mk'_iff_mul_eq,
    ← map_mul]
  congr 1
  rw [hu]
  calc a * ((u⁻¹ : Oˣ) : O) * ((u : O) * ϖ ^ n) = a * ϖ ^ n * (((u⁻¹ : Oˣ) : O) * u) := by ring
    _ = ϖ ^ n * a := by simp [mul_comm]

end GlobalTheory.ShapeNeg
