module

import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiTargetBilinearFormIntegral
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharEqOneOfOpENeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingAffPtUncurry
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpEOmTargetUnipotent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralLinear
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SecondCountableLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app app_coe)
open scoped Topology

noncomputable section
namespace GlobalTheory.PosOne.RrLin

theorem exists_open_translations {M : Type*} [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] {Φ : M → ℂ} (hΦ : Φ ∈ SB M) :
    ∃ Λ : AddSubgroup M, IsOpen (Λ : Set M) ∧ ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by
  let Λ : AddSubgroup M :=
    { carrier := {y | ∀ x, Φ (x + y) = Φ x}
      zero_mem' := fun x => by simp
      add_mem' := fun {y z} hy hz x => by rw [← add_assoc, hz, hy]
      neg_mem' := fun {y} hy x => by rw [← hy (x + -y)]; simp }
  refine ⟨Λ, Λ.isOpen_of_mem_nhds (g := 0) ?_, fun x y hy => hy x⟩
  have h1 : ∀ᶠ y in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x + y) = Φ x := by
    refine IsCompact.eventually_forall_of_forall_eventually hΦ.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : M × M => (Φ (q.2 + q.1), Φ q.2) :=
      (hΦ.1.comp_continuous (continuous_snd.add continuous_fst)).prodMk
        (hΦ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, x)] with q hq
    simp only [Prod.mk.injEq, add_zero] at hq
    rw [hq.1, hq.2]
  have h2 : ∀ᶠ y in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x + -y) = Φ x := by
    have ht : Filter.Tendsto (fun y : M => -y) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg (G := M)).tendsto 0
    exact ht.eventually h1
  filter_upwards [h1, h2] with y hs hs' x
  by_cases hx : x ∈ tsupport Φ
  · exact hs x hx
  by_cases hx' : x + y ∈ tsupport Φ
  · rw [← hs' _ hx']; simp
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem exists_isQuotInt_tInt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] {c p : ℕ} (hp : 1 ≤ p) (hpc : p ≤ c) {ψ : AddChar k Circle} (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] {μ : kˣ →* ℂˣ} (hμ : IsOpen (μ.ker : Set kˣ))
    (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure]
    {A : Type} [AddCommGroup A] [Module ℂ A] {σ : Representation ℂ (GL (n ⊕ Fin c) k) A} (hσ : IsSmoothRep σ)
    {B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ} (hB : BilPos ψ μ p σ B) (F : A)
    (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    ∃ z, IsQuotInt ν μX μG p (tInt ψ ν μ p σ B F Φ.1) z := by
  apply GlobalTheory.PosOne.FJTarget.exists_isQuotInt_tInt <;> assumption

end GlobalTheory.PosOne.RrLin

namespace GlobalTheory.PosOne.RrLin
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

theorem exists_linear_isQuotInt_tInt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ p σ B) (F : A) (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ'), ∃ Rr : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ, (∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsQuotInt ν μX μG p (tInt ψ ν μ p σ B F Φ.1) (Rr Φ)) ∧ IsNEquiv ψ p ρ' Rr := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp hpc ψ hψ hψ1 ν _ μ hμ μX _ μG _ A _ _ σ hσ B hB F ρ' hρ'
  have uniq := (GlobalTheory.QuotInt.quotInt_unique_exists k n c p hp hpc ν μX μG · |>.1)
  have hE := (opE_SB_and_linear k n n' c p ψ hψ ν).1

  have hfE : ∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) h,
      tInt ψ ν μ p σ B F Φ.1 h =
        B ⟨opE ψ ν p (om μ 1 h Φ.1), hE _ (om_mem_SB μ 1 h Φ.2)⟩ (σ h F) := fun Φ h => by
    rw [tInt]
    exact congrArg (fun l : A →ₗ[ℂ] ℂ => l (σ h F)) (app_coe B ⟨_, hE _ (om_mem_SB μ 1 h Φ.2)⟩)

  have hlinf : ∀ (a : ℂ) (Φ Ψ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)),
      tInt ψ ν μ p σ B F (a • Φ + Ψ).1 = fun h => a * tInt ψ ν μ p σ B F Φ.1 h + tInt ψ ν μ p σ B F Ψ.1 h := by
    intro a Φ Ψ
    funext h
    rw [hfE, hfE, hfE, ← smul_eq_mul, ← LinearMap.smul_apply, ← LinearMap.add_apply, ← map_smul, ← map_add (f := _)]
    congr 2
    apply Subtype.ext
    show opE ψ ν p (om μ 1 h (a • Φ.1 + Ψ.1)) =
      a • opE ψ ν p (om μ 1 h Φ.1) + opE ψ ν p (om μ 1 h Ψ.1)
    have e : om μ 1 h (a • Φ.1 + Ψ.1) = a • om μ 1 h Φ.1 + om μ 1 h Ψ.1 := by
      funext y; simp only [om, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact (opE_SB_and_linear k n n' c p ψ hψ ν).2 a _ (om_mem_SB μ 1 h Φ.2) _ (om_mem_SB μ 1 h Ψ.2)
  have hex := fun Φ => exists_isQuotInt_tInt hp hpc hψ hψ1 ν hμ μX μG hσ hB F Φ
  choose Rr hRr using hex
  have hlin : ∀ (a : ℂ) Φ Ψ, Rr (a • Φ + Ψ) = a * Rr Φ + Rr Ψ := fun a Φ Ψ => by
    refine uniq _ _ _ (hRr _) ?_
    rw [hlinf]
    exact GlobalTheory.RootEx.QuotLinear.isQuotInt_linear k n c p hp hpc ν μX μG _ _ a _ _ (hRr Φ) (hRr Ψ)
  have h0 : Rr 0 = 0 := by simpa using hlin 1 0 0
  let RL : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ :=
    { toFun := Rr
      map_add' := fun Φ Ψ => by simpa using hlin 1 Φ Ψ
      map_smul' := fun a Φ => by simpa [h0] using hlin a Φ 0 }
  refine ⟨RL, hRr, fun g hg Φ => ?_⟩
  show Rr (ρ' g Φ) = (ψ (simpleSum g) : ℂ) * Rr Φ
  have e : tInt ψ ν μ p σ B F (ρ' g Φ).1 = tInt ψ ν μ p σ B F ((ψ (simpleSum g) : ℂ) • Φ + 0).1 := by
    funext h
    rw [hfE, hfE]
    congr 2
    apply Subtype.ext
    show opE ψ ν p (om μ 1 h (ρ' g Φ).1) = opE ψ ν p (om μ 1 h ((ψ (simpleSum g) : ℂ) • Φ.1 + 0))
    have e1 : om μ 1 h (om μ g 1 Φ.1) = om μ g 1 (om μ 1 h Φ.1) := by
      rw [← om_mul, ← om_mul, one_mul, mul_one, mul_one, one_mul]
    rw [hρ', e1, GlobalTheory.RootExSource.opE_om_source k n n' c p hp hpc ψ ν μ _ g hg, add_zero]
    have e2 : om μ 1 h ((ψ (simpleSum g) : ℂ) • Φ.1) = (ψ (simpleSum g) : ℂ) • om μ 1 h Φ.1 := by
      funext y; simp only [om, Pi.smul_apply, smul_eq_mul]; ring
    rw [e2]
    funext x
    simp only [opE, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  have e3 : Rr (ρ' g Φ) = Rr ((ψ (simpleSum g) : ℂ) • Φ + 0) := uniq _ _ _ (hRr _) (e ▸ hRr _)
  rw [e3, hlin, h0, add_zero]

end GlobalTheory.PosOne.RrLin
