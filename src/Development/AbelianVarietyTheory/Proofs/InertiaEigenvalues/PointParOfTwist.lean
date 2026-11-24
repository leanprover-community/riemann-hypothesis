module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem pointPar_of_twist (D : D7) (hT : TwistInv D) (hc : D.naut.csd D.naut.etaT)
    (hz : ∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG D.naut.etaTinv τ,
      ∃ k : ℤ, z + ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = (k : ℂ)) : PointPar D := by
  intro i x π hx
  obtain ⟨P, -, hB⟩ := hx
  have hp : (⟨D.R.r, D.naut.tw π D.naut.etaTinv, 1⟩ : Formalism.BasicNotions.Part D.naut.CG) ∈
      twistIso D.nd D.naut ([⟨D.R.r, π, 1⟩] ++ [muPart D.nd D.naut i]) D.naut.etaTinv :=
    List.mem_cons_self
  obtain ⟨h1, -, h2⟩ := hB.1 _ hp
  refine ⟨?_, (D.naut.ralg_def π).2 fun τ => ?_⟩
  · have := D.naut.csd_tw _ _ hc h2
    rwa [hT.2 _ π h1] at this
  obtain ⟨s, hs⟩ := Multiset.card_eq_one.mp (D.naut.infG_card D.naut.etaTinv τ)
  obtain ⟨k0, hk0⟩ := hz τ s (by rw [hs]; exact Multiset.mem_singleton_self s)
  have hW : (D.naut.infWt i τ).Nodup ∧
      ∀ z ∈ D.naut.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
    rw [D.nbc.embAV_inf i P]
    exact D.nbc.infW_alg _ _ τ
  have hle : (D.naut.infG π τ).map (· + s) ≤ D.naut.infWt i τ := by
    rw [← hB.2.2.2.2.2 τ, ← D.naut.infG_tw π _ τ s hs]
    simp [isoInf, twistIso]
  refine ⟨Multiset.Nodup.of_map _ (Multiset.nodup_of_le hle hW.1), fun y hy => ?_⟩
  obtain ⟨k, hk⟩ := hW.2 _ (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hy))
  refine ⟨k - k0, ?_⟩
  rw [Ranks.nV] at hk
  push_cast at hk hk0 ⊢
  linear_combination hk - hk0

end GlobalTheory.TypeLeaf
