module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryElementActsLocalOperatorAtPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodSplitPlaceTranslationActsThroughWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarModelLocalTripleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqZeroOfKillsProductSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdempotentCharacterValueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceTransformSchwartzBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplittingPreservesLocalSchwartzStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SwapActs

theorem swap_acts_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
    ∀ (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
    ∀ (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl (incM F G.V'.J)),
      ((w : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    ∃ c : ℂ, ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      ∀ ψ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ ψ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      ι ψ₁ = (fun Y => starRingEnd ℂ (ι (fun y => starRingEnd ℂ (φ₂ y)) (-Y))) →
      ι (fun y => starRingEnd ℂ (ψ₂ y)) = (fun Y => starRingEnd ℂ (ι φ₁ (-Y))) →
      Acts (evFin F v) (omd w) (boxFun φ₁ φ₂) (c • boxFun ψ₁ ψ₂) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv t ι hι d' hd' dd hdd omd hspl f hf1 hf2 hf3 hf4 hf5 w hw
  have hcm : IsCMExt F E σ := hT.base.cm
  obtain ⟨hAt, -⟩ := GlobalTheory.T.local_idempotent_character_value σ hcm (incM F G.V'.J) (d := a + a') v t f hf1 hf2 hf3 hf4 hf5 w hw
  have atAct : ∀ u : Matrix (Fin (a + a')) (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) u →
      At (evFin F v) (actB (cA σ) w u) := by
    intro u hu r hr
    simp only [actB]
    rw [← Matrix.smul_mul, hu r hr, Matrix.zero_mul]
  have hex := GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace F E σ B a a' G hT.base dd omd hspl v w hAt
  obtain ⟨S, hS, hSh⟩ := GlobalTheory.T.splitting_preserves_local_schwartz dd B.ψ hT.base.std (actB (cA σ)) omd hspl.toIsSplitting v w atAct hex
  have hSlin := GlobalTheory.LocWeilAct.linear_of_acts v (omd w) S hS
  obtain ⟨c, hc⟩ := GlobalTheory.T.linear_bar_model_local_triple F E σ B a a' G X om om' hT v t ι hι d' hd' dd hdd f hf1 hf2 hf3 hf4 hf5 w hw S
    (fun Φ hΦ => (hS Φ hΦ).1) hSlin hSh
  refine ⟨c, fun φ₁ h₁ φ₂ h₂ ψ₁ k₁ ψ₂ k₂ e₁ e₂ => ?_⟩
  have hbij := GlobalTheory.T.slice_transform_schwartz_bijective ι hι.bij
  have hΦ := GlobalTheory.BoxSpan.boxFun_mem_SB' h₁ h₂
  have hΨ : c • boxFun ψ₁ ψ₂ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) :=
    (SB _).smul_mem c (GlobalTheory.BoxSpan.boxFun_mem_SB' k₁ k₂)
  have key : S (boxFun φ₁ φ₂) = c • boxFun ψ₁ ψ₂ := by
    refine hbij.injOn (hS _ hΦ).1 hΨ ?_
    rw [hc _ hΦ, map_smul]
    congr 1
    funext Z
    rw [Function.comp_apply, GlobalTheory.SwapSlice.sliceT_boxFun, GlobalTheory.SwapSlice.sliceT_boxFun, GlobalTheory.SwapSlice.swapNeg_apply,
      GlobalTheory.SwapSlice.barL_apply, GlobalTheory.SwapSlice.barL_apply, e₁, e₂]
    simp only [Complex.conj_conj]
    ring
  have h := (hS _ hΦ).2
  rwa [key] at h

end GlobalTheory.SwapActs
