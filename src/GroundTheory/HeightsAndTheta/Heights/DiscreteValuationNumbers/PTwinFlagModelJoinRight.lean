module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExSubAlt
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerTail
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisTail
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreTer
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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord pullDeg liftVar midDeg midVar FlagModel)

namespace FlagModelJoinRightAlt

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

theorem midDeg_pullDeg (a : K → ℤ) :
    midDeg (K₂ := K₂) (pullDeg (K' := K') a) = pullDeg (K' := K₂ ⊕ K') a := by
  funext k
  rcases k with k | k | k <;> rfl

theorem midVar_comp_liftVar :
    midVar (ι := ι) (ι' := ι') ι₂ ∘ liftVar ι' = liftVar (Sum.elim ι₂ ι') :=
  rfl

theorem pullDeg_sub (a b : K → ℤ) :
    pullDeg (K' := K') a - pullDeg (K' := K') b = pullDeg (K' := K') (a - b) := by
  funext k
  cases k <;> simp [pullDeg]

end FlagModelJoinRightAlt


open FlagModelJoinRightAlt in
theorem FlagModelJoinRightAlt.proof (hVert : JoinVerticalDivisor.Statement)
    (hFlag : FlagPairJoinRight.Statement) (hNum : PairNumberJoinRight.Statement) :
    FlagModelJoinRightAlt.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' _ _ F K₂ _ ι₂ _ w hZ hfn EB E'B hp hp'
  obtain ⟨ψ, -, -, -, hdeg, hdeg', hf, hg⟩ :=
    hFlag O Ω K ι x F.K' F.ι' F.z K₂ ι₂ w N V E E' F.EB F.E'B F.pull F.pull' F.flag EB E'B hp hp'
  refine ⟨ψ, fun I I₁ hI hI₁ G r y y' f g hv c Q hc hG hQ => ?_⟩
  have hvert : ∀ i, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (joinCoord x F.z))
      (Fin.append F.flag.deg (fun l => pullDeg (K' := F.K') (y l)) i -
        Fin.append F.flag.deg' (fun l => pullDeg (K' := F.K') (y' l)) i)
      (Fin.append F.flag.f (fun l => rename (liftVar F.ι') (f l)) i)
      (Fin.append F.flag.g (fun l => rename (liftVar F.ι') (g l)) i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
      exact F.flag.vert j
    · simp only [Fin.append_right, pullDeg_sub]
      exact hVert O Ω K ι x F.K' F.ι' F.z _ _ _ (hv j)
  have hH : (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q).IsHomogeneous (d + 1) := by
    have h : (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q).IsHomogeneous (c + (d + 1 - c)) :=
      hG.rename_isHomogeneous.mul hQ.rename_isHomogeneous
    rwa [show c + (d + 1 - c) = d + 1 by omega] at h
  unfold FlagModel.value
  rw [hNum O Ω K ι x F.K' F.ι' F.z K₂ ι₂ w d F.model hZ (hfn.trans F.birat.symm) I I₁ hI hI₁ (N + r)
    _ _ _ _ hvert _ hH]
  congr 1 <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [hdeg, hdeg', hf, hg, midDeg_pullDeg, midVar_comp_liftVar]

end GroundTheory.Heights₂.Heights.NumbersDVR
