import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BuiltCols
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvLgCanonical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsRowValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivHermitianFrameNormAtComplexPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroColumnsClassSumFormPosDefStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsPrescribedUnitaryFormsStandInsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsHermLatticeGoodAndComplexBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDivStageStandIn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitsOrderOfEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsCombOfMemClosureFinset

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Df

namespace GlobalTheory.Core.Rk.TrueModel

attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem map_mem_span_image {K : Type} [Field K] (σ : K →+* ℂ) {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[σ] W) (S : Set V) {x : V} (hx : x ∈ Submodule.span K S) :
    j x ∈ Submodule.span ℂ (j '' S) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul k y _ hy => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

theorem span_image_eq_top {K : Type} [Field K] (σ : K →+* ℂ) {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[σ] W) {ι : Type} (b : Module.Basis ι K V) (S : Set V)
    (hS : Submodule.span K S = ⊤) (hb : Submodule.span ℂ (Set.range fun i => j (b i)) = ⊤) :
    Submodule.span ℂ (j '' S) = ⊤ := by
  rw [eq_top_iff, ← hb, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact map_mem_span_image σ j S (by rw [hS]; exact Submodule.mem_top)


set_option maxHeartbeats 1600000 in

theorem ambTrue_ex : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok), ∀ (Z : TC.Later B (I.cols l)) (e : ∀ a : (I.cols l).Tup, MtCx I a ≃ₗ[ℂ] Z.W.Amb a), DefTrue I l hX Z.W e → ∃ A : AmbForm (I.rec7 l Z) (RowSide.sharp (I.rec7 l Z)), AmbTrue I l hX Z e A := by
  intro B X I _ _ l hX Z e hD
  classical
  let j : ∀ a : (I.cols l).Tup, (MtHL I hX a).V →ₛₗ[B.embLL] MtCx I a := fun a => (Df.mtHL_good_basis I hX a).2.1.choose
  have hj : ∀ a x, j a x = toCx I hX a x := fun a => (Df.mtHL_good_basis I hX a).2.1.choose_spec
  let jA : ∀ a : (I.cols l).Tup, (MtHL I hX a).V →ₛₗ[B.embLL] Z.W.Amb a := fun a => (e a).toLinearMap.comp (j a)
  have hjA : ∀ a x, jA a x = e a (toCx I hX a x) := fun a x => by
    show e a (j a x) = _
    rw [hj]
  have hli : ∀ a, LinearIndependent ℂ (fun i => jA a ((MtHL I hX a).b i)) := fun a => by
    have h1 := (Df.mtHL_good_basis I hX a).2.2.1
    have h2 := h1.map' (e a).toLinearMap (LinearEquiv.ker _)
    have hf : (fun i => jA a ((MtHL I hX a).b i)) = (e a).toLinearMap ∘ (fun i => toCx I hX a ((MtHL I hX a).b i)) := by
      funext i
      simp only [Function.comp_apply, LinearEquiv.coe_coe]
      exact hjA a _
    rw [hf]
    exact h2
  have hspan : ∀ a, Submodule.span ℂ (Set.range (fun i => jA a ((MtHL I hX a).b i))) = ⊤ := fun a => by
    have h1 := (Df.mtHL_good_basis I hX a).2.2.2
    have hr : Set.range (fun i => jA a ((MtHL I hX a).b i)) = (e a).toLinearMap '' Set.range (fun i => toCx I hX a ((MtHL I hX a).b i)) := by
      rw [← Set.range_comp]
      congr 1
      funext i
      simp only [Function.comp_apply, LinearEquiv.coe_coe]
      exact hjA a _
    rw [hr, Submodule.span_image, h1, Submodule.map_top]
    exact LinearEquiv.range _
  have hinj : ∀ a, Function.Injective (jA a) := fun a => by
    rw [injective_iff_map_eq_zero]
    intro z hz
    set b := (MtHL I hX a).b
    have hsum : jA a z = ∑ i, B.embLL (b.repr z i) • jA a (b i) := by
      conv_lhs => rw [← b.sum_repr z]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smulₛₗ]
    rw [hsum] at hz
    have h0 := Fintype.linearIndependent_iff.mp (hli a) (fun i => B.embLL (b.repr z i)) hz
    have : b.repr z = 0 := by
      ext i
      have := h0 i
      simpa using this
    simpa using this
  refine ⟨⟨fun a => MtHL I hX a, jA, ?_, ?_, ?_, ?_, ?_⟩, ⟨fun a => ?_⟩⟩
  · intro μ _; exact (Df.mtHL_good_basis I hX μ).1
  · intro μ _; exact ⟨hli μ, hspan μ⟩
  · intro μ _ x
    have hlat := hD.lat μ
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := (hlat (jA μ x)).2 ⟨x, hx, (hjA μ x).symm⟩
      refine ⟨fun v => ⟨B.OtoLL (c v), (I.rec7 l Z).O_int (c v)⟩, ?_⟩
      exact hc
    · rintro ⟨c, hc⟩
      letI := Z.W.instAmb μ
      letI := Z.W.instAmbi μ
      have hg : ∀ v ∈ (Z.W.Mtilde μ).gen, ∃ y ∈ (MtHL I hX μ).L, jA μ y = v := fun v hv => by
        obtain ⟨y, hy, h⟩ := (hlat v).1 (hD.gen μ v hv)
        exact ⟨y, hy, (hjA μ y).trans h⟩
      choose! xv hxvL hxv using hg
      let c' : Z.W.Amb μ → 𝓞 B.LL := c
      have hmem : (∑ v ∈ (Z.W.Mtilde μ).gen, c' v • xv v) ∈ (MtHL I hX μ).L :=
        Submodule.sum_mem _ fun v hv => Submodule.smul_mem _ _ (hxvL v hv)
      have heq : jA μ (∑ v ∈ (Z.W.Mtilde μ).gen, c' v • xv v) = jA μ x := by
        rw [map_sum]
        refine Eq.trans (Finset.sum_congr rfl fun v hv => ?_) hc.symm
        have hs : ((c' v : B.LL)) • xv v = c' v • xv v := by
          letI := (MtHL I hX μ).modOV
          haveI := (MtHL I hX μ).towV
          exact algebraMap_smul B.LL (c' v) (xv v)
        rw [← hs, map_smulₛₗ, hxv v hv]
        rfl
      rw [← hinj μ heq]
      exact hmem
  · intro μ _ v hv
    obtain ⟨x, _, h⟩ := (hD.lat μ v).1 (hD.gen μ v hv)
    exact ⟨x, (hjA μ x).trans h⟩
  · intro μ _ x
    have h := hD.norm μ x
    have h2 := hjA μ x
    rw [← h2] at h
    exact h
  · show (⟨MtHL I hX a, fun x => jA a x⟩ : Σ H : HLat B.LL, (H.V → Z.W.Amb a)) = _
    exact congrArg (Sigma.mk (MtHL I hX a)) (funext (hjA a))



variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws)

def rowJ (h : I.Ok) (u : B.Word) : (MtTrue I).V →ₛₗ[B.embLL] (I.per l u I.mu0).Mt :=
  PeriodOnStep.rowEmb (Pr := B.primes X) B.wts I.Ch I.sel (I.tup I.mu0) I.Ps (I := I.chIn u I.mu0) (I.perIn u I.mu0).b0
    (I.perIn u I.mu0).til (I.perIn u I.mu0).ext (I.perIn u I.mu0).tz (I.perIn u I.mu0).H
    (Finset.disjoint_right.2 (Q_notMem_of_ok h I.mu0)) B.embLL










end GlobalTheory.Core.Rk.TrueModel

end
