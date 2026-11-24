module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FormLetterLe
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TopLieVectorNormSqEqGramDet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem lamLen_of_isHerm : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l) (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La : ℝ), LamObjGood o f La → ∀ L : LamLetters o, L.IsGood → ∀ (hf : IsPolFibre (algebraMap (𝓞 o.K₁) o.K₁) o.B o.xB.P o.φB) (h : HermFam o.K₁ (Fin o.xB.P.g → o.K₁)), (GenFib.mk o.xB.P o.φB hf o.xB.v o.xB.basis : GenFib o.B).IsHerm h → ∀ (σ : o.K₁ →+* ℂ), o.LamL.n σ = Real.sqrt (h.gram σ (fun i : Fin o.xB.P.g => Pi.single i 1)).det.re ∧ ∀ k, (h.form σ (L.U k) (L.U k)).re ≤ (La * (L.ℓ k).n σ) ^ 2 := by
  intro hU hL E _ _ _ _ H l c nΨ n' f o La hG L hLg hp h Hh σ
  obtain ⟨-, -, -, -, hΨ, hA', -, -, -, tΨ, t', -, -, hI, hP, hb, vΨ, v', -, hgood, -, harch, -⟩ := hG
  refine ⟨?_, fun k => ?_⟩
  · have := GlobalTheory.CM.TopLieVector.sq_eq_det_gram hU hL o.K₁ o.B o.xB o.φB hp h Hh o.Tl o.LamL σ (harch σ)
    exact ((congrArg Real.sqrt this).symm.trans (Real.sqrt_sq (hgood.2 σ).le)).symm
  · obtain ⟨w, hw1, hw2⟩ := hLg.2.2.1 k
    have h4 := hLg.2.2.2 k
    unfold LamLetters.IsLetter at hw1
    cases hs : L.src k with
    | inl q =>
      rw [hs] at hw1 h4
      simp only at hw1 h4
      rw [h4]
      exact form_letter_le hU hL o.AΨ o.B o.oaΨ o.xΨ o.φΨg (S := psiSet H) o.τΨ _ hΨ tΨ
        (GenFib.mk o.xB.P o.φB hp o.xB.v o.xB.basis) h Hh (o.φΨ q.1) (hI.1 _) (o.hΨ q.1) (hP.2.2.1 q.1) La
        (hb.1 q.1) q.2 _ (vΨ q.2) _ w hw2 hw1 σ
    | inr q =>
      rw [hs] at hw1 h4
      simp only at hw1 h4
      rw [h4]
      exact form_letter_le hU hL o.A' o.B o.oa' o.x' o.φ'g (S := (psiSet H)ᶜ) o.τ' _ hA' t'
        (GenFib.mk o.xB.P o.φB hp o.xB.v o.xB.basis) h Hh (o.φ' q.1) (hI.2.1 _) (o.h' q.1) (hP.2.2.2 q.1) La
        (hb.2 q.1) q.2 _ (v' q.2) _ w hw2 hw1 σ

end GlobalTheory.LamF
