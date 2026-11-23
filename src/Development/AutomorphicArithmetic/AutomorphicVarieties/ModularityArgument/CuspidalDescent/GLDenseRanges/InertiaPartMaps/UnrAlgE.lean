module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.MuRange
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open UpperTheory.V.Alg UpperTheory.V.J UpperTheory.V.Z.Desc.V0

theorem UpperTheory.V.Z.Desc.V0.unrAlgE :
    UnrAlgW → MuRange → UnrAlgE := by
  intro hW hR O Λ B K _ _ _ _ _ _ _ _ _ _ _ _ _ _ lam J M _ _ _ h e he x 𝒢 b₀ hb₀ hJ h1 hG δ hδ hδJ hδl
  obtain ⟨J', M', _, _, _, h', hJJ', hy⟩ := hR O Λ B K lam J M h e he
  have key : ∀ a, (∀ y ∈ 𝒢, y b₀ ≠ 0 → y a = 0) → a * b₀ ∈ J := by
    intro a ha
    apply hJ
    intro y hy
    rw [map_mul]
    by_cases hb : y b₀ = 0
    · rw [hb, mul_zero]
    · rw [ha y hy hb, zero_mul]
  have hx' : J' ≤ RingHom.ker x := (hy x).2 h1
  have hG1 : ∀ y ∈ 𝒢, y b₀ ≠ 0 → J' ≤ RingHom.ker y := fun y hy1 hb =>
    (hy y).2 (le_trans h1 (hG y hy1 hb))
  refine hW O Λ B K lam J' M' h' x hx' {y | y ∈ 𝒢 ∧ y b₀ ≠ 0} b₀ hb₀ ?_ ?_ δ hδ ?_ hδl
  · intro a ha
    exact hJJ' (key a fun y hy hb => ha y ⟨hy, hb⟩)
  · rintro y ⟨hy1, hb⟩
    refine ⟨hG1 y hy1 hb, ?_⟩
    rw [(hy x).1, (hy y).1]
    exact hG y hy1 hb
  · intro a ha
    have h2 : a * b₀ ∈ J := key a fun y hy hb => RingHom.mem_ker.1 (hG1 y hy hb ha)
    have hxa : x a = 0 := RingHom.mem_ker.1 (hx' ha)
    have h3 : δ (a * b₀) = x a • δ b₀ + x b₀ • δ a := hδ a b₀
    rw [hδJ _ h2, hxa, zero_smul, zero_add, smul_eq_mul] at h3
    exact (mul_eq_zero.1 h3.symm).resolve_left hb₀
