module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem CommonFactorInduction.proof (hpos : ExcessPositive.Statement.{u}) (havoid : AvoidingFormExists.Statement.{u})
    (hhor : HorizontalAvoidingForm.Statement.{u}) (hpieces : BlowUpDecomposition.Statement.{u})
    (hdrop : BlowUpExcessDecreases.Statement.{u}) (hred : BlowUpReduction.Statement.{u})
    (hlhs : LeftSideAdditiveInDegree.Statement.{u}) (hrhs : RightSideMultiplicativeInForm.Statement.{u})
    (hmul : DivCycleMul.Statement.{u}) : CommonFactorInduction.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH hcommon IH L
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hε := hpos O ϖ hϖ K ι P d hP b f g hD s hsP hcommon

  obtain ⟨e, h, hh, hhP, hle, hhH, hhG, hh0, hmulε⟩ :=
    havoid O ϖ hϖ K ι P d hP b f g hD (fun k => (b k).toNat)
  have hdiv : ∀ W, divCycle P (s * h) W = divCycle P s W + divCycle P h W :=
    fun W => congrFun (hmul O K ι P s h hPp hsP hhP) W
  have hshP : s * h ∉ P := fun hm => (hPp.mem_or_mem hm).elim hsP hhP
  have hshH : ∀ H, divCycle P (s * h) H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g := by
    intro H hH hϖH
    rw [hdiv] at hH
    by_cases h1 : divCycle P s H = 0
    · exact hhH H (by rwa [h1, zero_add] at hH) hϖH
    · exact hsH H h1 hϖH
  have hcommon' : ∃ G, (C ϖ : MRing ι O) ∈ G ∧ divCycle P (s * h) G ≠ 0 ∧ ratDiv P f g G ≠ 0 := by
    obtain ⟨G, hG, hsG, hDG⟩ := hcommon
    exact ⟨G, hG, by rwa [hdiv, hhG G hG hDG, add_zero], hDG⟩

  set e₂ : K → ℕ := fun k => (((c + e) k : ℕ) - b k : ℤ).toNat with he₂def
  have he₂ : ∀ k, (((c + e) k : ℕ) : ℤ) = b k + e₂ k := by
    intro k
    have h1 : (b k).toNat ≤ e k := hle k
    have h2 : b k ≤ ((b k).toNat : ℤ) := Int.self_le_toNat (b k)
    simp only [he₂def, Pi.add_apply, Nat.cast_add]
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  obtain ⟨m, hm, hmP, hmH⟩ := hhor O ϖ hϖ K ι P d hP (s * h) hshP e₂
  obtain ⟨hmodel, hsl, hslP, hY₀P, hD₁, hE, hH₁, hH₀⟩ := hpieces O ϖ hϖ K ι P d hP b f g hD (c + e)
    (s * h) (hs.mul hh) hshP hshH e₂ he₂ m hm hmP hmH
  obtain ⟨hdrop₁, hdrop₀⟩ := hdrop O ϖ hϖ K ι P d hP b f g hD (c + e) (s * h) (hs.mul hh) hshP
    hshH e₂ he₂ m hm hmP hmH hcommon'
  rw [hmulε s hsP] at hdrop₁ hdrop₀

  have hId₁ := IH (Option K) (extIdx ι (BlowUpIdx ι)) _ d hmodel _ _ _ hD₁ _ _ hsl hslP
    (fun H hH hϖH => (hH₁ H hH hϖH).1) hdrop₁ (liftDegs L)
  have hId₀ := IH (Option K) (extIdx ι (BlowUpIdx ι)) _ d hmodel _ _ _ hE (Pi.single none 1)
    (newVar none) (isWeightedHomogeneous_X _ _ _) hY₀P hH₀ hdrop₀ (liftDegs L)

  have hIdsh := hred O ϖ hϖ K ι P d hP b f g hD (c + e) (s * h) (hs.mul hh) hshP hshH e₂ he₂ m hm
    hmP hmH L hId₁ hId₀
  have hIdh := IH K ι P d hP b f g hD e h hh hhP hhH (by rw [hh0]; exact hε) L

  rw [cutIdentity_iff] at hIdsh hIdh ⊢
  have h1 := hlhs O ϖ hϖ K ι P d hP b f g hD.1 c e L
  have h2 := hrhs O ϖ hϖ K ι P d hP b f g s h hsP hhP L
  linarith

end GroundTheory.Heights₂.Heights.NumbersDVR
