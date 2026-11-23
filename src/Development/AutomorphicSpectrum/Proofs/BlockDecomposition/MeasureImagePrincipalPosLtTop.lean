module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedCoeff
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenIsCompactPrincipal
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

@[expose] public section

open GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.PrincipalCongruence

theorem measure_image_principal_pos_lt_top :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N : ℕ) (ϖ : k) (m : ℕ), ϖ ≠ 0 → ValuativeRel.valuation k (ϖ) < 1 →
      (∀ x : k, ValuativeRel.valuation k (x) < 1 →
        ValuativeRel.valuation k (x) ≤ ValuativeRel.valuation k (ϖ)) → 1 ≤ m →
      ∀ [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : MeasureTheory.Measure (AdGL k N)),
        μ.IsHaarMeasure →
        0 < μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
          {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
            ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
              ValuativeRel.valuation k (ϖ ^ m)}) ∧
        μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
          {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
            ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
              ValuativeRel.valuation k (ϖ ^ m)}) < ⊤ := by
  intro k _ _ _ _ N ϖ m h0 h1 _ hm _ _ μ hμ
  have ht0 : ϖ ^ m ≠ 0 := pow_ne_zero m h0
  have ht1 : ValuativeRel.valuation k (ϖ ^ m) < 1 := by
    rw [map_pow]
    exact pow_lt_one' h1 (by omega)
  obtain ⟨hopen, hcomp⟩ := isOpen_isCompact_principal k N (ϖ ^ m) ht0 ht1
  have hone : (1 : GL (Fin N) k) ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
      ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
        ValuativeRel.valuation k (ϖ ^ m)} := by
    intro i j
    simp
  refine ⟨?_, ?_⟩
  · have himg : IsOpenMap (QuotientGroup.mk : GL (Fin N) k → AdGL k N) :=
      QuotientGroup.isOpenMap_coe
    exact (himg _ hopen).measure_pos μ ⟨_, Set.mem_image_of_mem _ hone⟩
  · exact (hcomp.image QuotientGroup.continuous_mk).measure_lt_top

end GlobalTheory.CompanionTheory.PrincipalCongruence
