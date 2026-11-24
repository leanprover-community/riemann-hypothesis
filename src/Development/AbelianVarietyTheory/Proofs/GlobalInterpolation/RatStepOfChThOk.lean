module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BelowFiniteNonempty
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelChainSharpColumnValuationOwnChainIff

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

namespace GlobalTheory.KerT

theorem ratStep_of_chTh_ok : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ) (A : Formalism.L2.Ker.Amb X), X.Ok → Pr.Ok → Ch.Ok → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) → L.Ok Ch sel mu cst G m2 → cst.sharp = true → ChTh.Ok (Ch := Ch) cst (Formalism.L2.Ker.chTh W Ch sel mu cst A u m2) → i < R.m → GlobalTheory.KerT.RatStep W Ch sel mu cst A u i (i + 1) := by
  intro X Pr R W Ch sel S mu cst L G m2 u i A _ _ _ _ _ _ hL _ hT hi
  have hq := Formalism.L2.Ker.muqTie_of_ok Ch sel mu cst L hL
  have hm := hL.hm
  have key : ∀ j, (j = i + 1 ∧ i ≤ m2) ∨ (j = R.m ∧ i = m2 + 1) → GlobalTheory.KerT.RatStep W Ch sel mu cst A u i j := by
    intro j hj
    unfold RatStep
    rw [← Formalism.L2.Ker.stepC_eq_stepT W Ch sel mu cst hq A u i hi]
    rcases hj with ⟨rfl, h⟩ | ⟨rfl, rfl⟩
    · intro γ γ' N fr N' fr' c x h'
      exact (hT.th i h).equiv γ γ' N fr N' fr' c x h'.1 h'.2.1
    · intro γ γ' N fr N' fr' c x h'
      exact hT.top.equiv γ γ' N fr N' fr' c x h'.1 h'.2.1
  exact key _ (by omega)

end GlobalTheory.KerT
