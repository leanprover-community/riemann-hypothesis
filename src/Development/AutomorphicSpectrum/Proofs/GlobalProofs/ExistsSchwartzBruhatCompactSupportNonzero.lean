module

public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSelfDualForm
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest

open NumberField IsDedekindDomain MeasureTheory
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta
open scoped TensorProduct ENNReal Matrix NumberField.AdeleRing

theorem exists_compactSupport_ne_zero :
    ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι],
      ∃ f ∈ schwartzBruhatPi (K := F) (ι := ι), HasCompactSupport f ∧ f 0 ≠ 0 := by
  intro F _ _ ι _ _
  obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds (0 : ι → 𝔸[F])
  obtain ⟨r, -, -, hr0, hrU, hrS⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.SdExist.exists_bump (K := F) 0 U hU
  refine ⟨_, hrS, HasCompactSupport.intro hUc fun x hx => ?_, ?_⟩
  · have : r x = 0 := by
      by_contra h
      exact hx (hrU x h)
    simp [this]
  · exact_mod_cast hr0.ne'

end GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest
