module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoDuality
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSummandTw
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section

namespace GlobalTheory.Pass.LocDual

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

theorem isSubFam_of_isSubSumOf {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL))
    (W A A' : GRep G Qp LL O) (hW : BlochKatoDuality.IsSubSumOf W.ρ A.ρ A'.ρ) (hA : IsSubFam Ms A)
    (hA' : IsSubFam Ms A') : IsSubFam Ms W := by
  obtain ⟨a, b, p, q, hp, hq, hinj⟩ := hW
  obtain ⟨a₁, x₁, p₁, hp₁, hinj₁⟩ := hA
  obtain ⟨a₂, x₂, p₂, hp₂, hinj₂⟩ := hA'
  let e : Fin (a * a₁ + b * a₂) ≃ (Fin a × Fin a₁) ⊕ (Fin b × Fin a₂) :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr finProdFinEquiv.symm finProdFinEquiv.symm)
  let X : (Fin a × Fin a₁) ⊕ (Fin b × Fin a₂) → ι :=
    Sum.elim (fun ij => x₁ ij.2) (fun ij => x₂ ij.2)
  let P : (Fin a × Fin a₁) ⊕ (Fin b × Fin a₂) → W.V →ₗ[LL] (Fin k → LL) :=
    Sum.elim (fun ij => (p₁ ij.2).comp (p ij.1)) (fun ij => (p₂ ij.2).comp (q ij.1))
  refine ⟨a * a₁ + b * a₂, X ∘ e, P ∘ e, ?_, ?_⟩
  · intro j g v
    simp only [Function.comp]
    generalize e j = s
    rcases s with ⟨i, j'⟩ | ⟨i, j'⟩
    · simp only [P, X, Sum.elim_inl, LinearMap.comp_apply, hp, hp₁]
    · simp only [P, X, Sum.elim_inr, LinearMap.comp_apply, hq, hp₂]
  · intro v hv
    apply hinj v
    · intro i
      apply hinj₁
      intro j'
      have h := hv (e.symm (Sum.inl (i, j')))
      simpa [P] using h
    · intro i
      apply hinj₂
      intro j'
      have h := hv (e.symm (Sum.inr (i, j')))
      simpa [P] using h

end Gen

section OnePD

theorem liftAll_of_liftFam :
    ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)) (e : ℕ)
    (A A' : GRep G Qp LL O), LiftFam (O := O) PD Ms e → IsSubFam Ms A → IsSubFam Ms A' → BlochKatoDuality.LiftAll PD A A' e := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ ι k Ms e A A' hL hA hA'
  intro W₁ W₂ h₁ h₂ L₁ L₂ F hF
  exact hL W₁ W₂ (isSubFam_of_isSubSumOf Ms W₁ A A' h₁ hA hA')
    (isSubFam_of_isSubSumOf Ms W₂ A A' h₂ hA hA') L₁ L₂ F hF

end OnePD

end GlobalTheory.Pass.LocDual

end
