module

import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNsmulMem
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.CompanionTheory.HatBound

theorem exists_nat_mul_integer (K : Type) [Field K] [NumberField K] (x : K) :
    ∃ m : ℕ, 0 < m ∧ ∃ r : 𝓞 K, (r : K) = m * x := by
  have hx : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy, h⟩ := hx.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rcases Int.natAbs_eq y with h1 | h1
  · refine ⟨⟨y • x, h⟩, ?_⟩
    change y • x = _
    rw [zsmul_eq_mul]
    congr 1
    conv_lhs => rw [h1]
    simp only [Int.cast_natCast]
  · refine ⟨⟨-(y • x), h.neg⟩, ?_⟩
    change -(y • x) = _
    rw [zsmul_eq_mul, ← neg_mul]
    congr 1
    conv_lhs => rw [h1]
    simp only [Int.cast_neg, Int.cast_natCast, neg_neg]

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem exists_nsmul_mem_lattice [NumberField E] (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ m : ℕ, 0 < m ∧ m • x ∈ L := by
  apply GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mem <;> assumption

end GlobalTheory.CompanionTheory.HatBound
