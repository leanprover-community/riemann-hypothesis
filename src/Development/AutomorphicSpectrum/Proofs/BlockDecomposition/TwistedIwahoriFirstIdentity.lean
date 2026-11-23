module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousInvOfPowEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqOneOfLowerParab
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc.Contraction

theorem e1 : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.E1 k := by
  intro k _ _ _ _ N J θ l t hA hT g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  have hθJ : J.map θ.toMonoidHom = J := hA.2.2.2.2.2.2.1
  have hθa : θ a ∈ J := by
    rw [← hθJ]
    exact Subgroup.mem_map_of_mem _ ha
  obtain ⟨j₁, hj₁, n, hn, τ, hτ, h₁⟩ :=
    GlobalTheory.CompanionTheory.LbcKillN.killN N J θ l t hA hT (b * θ a) (J.mul_mem hb hθa)
  obtain ⟨j₂, hj₂, κ, hκ, h₂⟩ := GlobalTheory.CompanionTheory.Lbc.KillNlo.killNlo N J θ l t hA hT n hn τ hτ
  refine ⟨(a * j₁ * j₂)⁻¹, J.inv_mem (J.mul_mem (J.mul_mem ha hj₁) hj₂), κ, hκ, ?_⟩
  rw [← h₂, ← h₁]
  simp only [inv_inv, map_inv, map_mul]
  group

end GlobalTheory.CompanionTheory.Lbc.Contraction
