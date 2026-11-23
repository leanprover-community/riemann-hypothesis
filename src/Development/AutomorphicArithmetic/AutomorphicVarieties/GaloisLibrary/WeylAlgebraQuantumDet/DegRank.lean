module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.MvPolynomial.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

@[expose] public section

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.degRank :
    ∀ (n N : ℕ), Module.finrank ℂ (MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N) ≤ (N + 1) ^ (n * n) := by
  intro n N
  change Module.finrank ℂ (MvPolynomial.restrictSupport ℂ
    {m : Fin n × Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ N}) ≤ _
  rw [Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport ℂ _)]
  have key : ∀ m : {m : Fin n × Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ N},
      ∀ i, (m : Fin n × Fin n →₀ ℕ) i < N + 1 := by
    intro m i
    have h1 := Finsupp.le_degree i (m : Fin n × Fin n →₀ ℕ)
    have h2 : Finsupp.degree (m : Fin n × Fin n →₀ ℕ)
        = (m : Fin n × Fin n →₀ ℕ).sum fun _ e => e := rfl
    have h3 := m.2
    simp only [Set.mem_setOf_eq] at h3
    omega
  calc Nat.card {m : Fin n × Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ N}
      ≤ Nat.card (Fin n × Fin n → Fin (N + 1)) :=
        Nat.card_le_card_of_injective (fun m i => ⟨(m : Fin n × Fin n →₀ ℕ) i, key m i⟩)
          (by
            intro a b h
            apply Subtype.ext
            ext i
            have := congrArg Fin.val (congrFun h i)
            simpa using this)
    _ = (N + 1) ^ (n * n) := by
      simp [Nat.card_eq_fintype_card, Fintype.card_fun]
