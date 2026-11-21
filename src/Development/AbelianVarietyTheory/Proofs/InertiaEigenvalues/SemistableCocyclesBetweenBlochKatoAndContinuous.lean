import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisPhiFixedAddFinrankMonLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalExactSequenceContinuityAllTheories
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantLogSemistableToDeRhamStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorFundamentalExactSequenceCrystallineStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonVEqZeroIffExistsCrisIncl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusTensorCrisToSemistableComm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorFundamentalExactSequenceCrystalline
import BuildAid.ForwardExisting

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

noncomputable section

open Formalism Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage GlobalTheory.FundCont Filter Topology

namespace GlobalTheory.ContDR

theorem cont_dR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ (k : ℕ) (x : Fin k → V ⊗[ℚ_[l]] P.R.BdR) (β : Fin k → ↥(GK K) → ℚ_[l]), (∀ i, Continuous (β i)) → ∀ (x' : V ⊗[ℚ_[l]] P.R.BdR) (f : ↥(GK K) → V), (∀ g, f g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = ∑ i, β i g • x i + (actVdR (P.PD K) ρ g x' - x')) → Continuous f := by
  intro l _ P AI T K V _ _ _ _ _ ρ hρ k x β hβ x' f hf
  have hV : ∀ φ : V →ₗ[ℚ_[l]] ℚ_[l], Continuous φ := fun φ =>
    IsModuleTopology.continuous_of_linearMap φ
  have key : ∀ φ : V →ₗ[ℚ_[l]] ℚ_[l], Continuous fun g => φ (f g) := by
    intro φ
    let Φ : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] P.R.BdR :=
      (TensorProduct.lid ℚ_[l] P.R.BdR).toLinearMap ∘ₗ TensorProduct.map φ LinearMap.id
    have hΦ : ∀ v b, Φ (v ⊗ₜ b) = qB P (φ v) * b := by
      intro v b
      simp [Φ, Algebra.smul_def]
    have h1 : ∀ (y : V ⊗[ℚ_[l]] P.R.BdR) (i : Fin k), LatCont AI fun g => Φ (β i g • y) := by
      intro y i
      induction y using TensorProduct.induction_on with
      | zero => simpa using latCont_const AI 0
      | tmul v b =>
        simp only [TensorProduct.smul_tmul', hΦ]
        simpa using latCont_orbit AI T b ((hV φ).comp ((hβ i).smul continuous_const))
          (γ := fun _ => 1) continuous_const
      | add y y' ih ih' =>
        simp only [smul_add, map_add]
        exact ih.add AI ih'
    have h2 : ∀ y : V ⊗[ℚ_[l]] P.R.BdR, LatCont AI fun g => Φ (actVdR (P.PD K) ρ g y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simpa using latCont_const AI 0
      | tmul v b =>
        have e : ∀ g : ↥(GK K), Φ (actVdR (P.PD K) ρ g (v ⊗ₜ b)) =
            qB P (φ (ρ g v)) * P.actQdR (g : GQ l) b := by
          intro g
          rw [← P.PD_actdR K g b, ← hΦ]
          rfl
        simp only [e]
        exact latCont_orbit AI T b ((hV φ).comp (hρ v)) continuous_subtype_val
      | add y y' ih ih' =>
        simp only [map_add]
        exact ih.add AI ih'
    apply continuous_of_latCont AI T
    have e : ∀ g, qB P (φ (f g)) =
        ∑ i, Φ (β i g • x i) + (Φ (actVdR (P.PD K) ρ g x') + -Φ x') := by
      intro g
      have := congrArg Φ (hf g)
      rwa [hΦ, mul_one, map_add, map_sum, map_sub, sub_eq_add_neg] at this
    simp only [e]
    exact (LatCont.sum AI _ _ fun i => h1 (x i) i).add AI ((h2 x').add AI (latCont_const AI _))
  let b := Module.finBasis ℚ_[l] V
  have : f = fun g => ∑ j, b.coord j (f g) • b j := by
    funext g
    simp [b.sum_repr]
  rw [this]
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  haveI : ContinuousSMul ℚ_[l] V := IsModuleTopology.toContinuousSMul ℚ_[l] V
  exact continuous_finset_sum _ fun j _ => (key (b.coord j)).smul continuous_const

end GlobalTheory.ContDR
end
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_cochain_of_deRham_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ (k : ℕ) (x : Fin k → V ⊗[ℚ_[l]] P.R.BdR) (β : Fin k → ↥(GK K) → ℚ_[l]), (∀ i, Continuous (β i)) → ∀ (x' : V ⊗[ℚ_[l]] P.R.BdR) (f : ↥(GK K) → V), (∀ g, f g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = ∑ i, β i g • x i + (actVdR (P.PD K) ρ g x' - x')) → Continuous f := by
  atlas_forward_decl GlobalTheory.ContDR.cont_dR
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.InertiaEigenvalues

theorem lTensor_iota_equivariant : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → (∀ (g : GQ l) (x : Bst P), ι (actSt P g x) = P.actQdR g (ι x)) → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ (g : ↥(GK K)) (z : V ⊗[ℚ_[l]] Bst P), LinearMap.lTensor V ι.toLinearMap (stRep P ρ g z) = actVdR (P.PD K) ρ g (LinearMap.lTensor V ι.toLinearMap z)) ∧ (∀ w : V ⊗[ℚ_[l]] P.R.B, LinearMap.lTensor V ι.toLinearMap (crisIncl P ℚ_[l] V w) = ιV (P.PD K) (LL := ℚ_[l]) (V := V) w) ∧ ∀ v : V, LinearMap.lTensor V ι.toLinearMap (v ⊗ₜ[ℚ_[l]] (1 : Bst P)) = v ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) := by
  intro l _ P ι hC hG K V _ _ ρ
  refine ⟨fun g z => ?_, fun w => ?_, fun v => ?_⟩
  · induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp [stRep_tmul, actVdR, hG, P.PD_actdR]
    | add x y hx hy => simp only [map_add, hx, hy]
  · induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp [crisIncl_tmul, ιV, hC, P.PD_ι]
    | add x y hx hy => simp only [map_add, hx, hy]
  · simp

end GlobalTheory.InertiaEigenvalues
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lTensor_semistable_to_deRham_equivariant : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → (∀ (g : GQ l) (x : Bst P), ι (actSt P g x) = P.actQdR g (ι x)) → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ (g : ↥(GK K)) (z : V ⊗[ℚ_[l]] Bst P), LinearMap.lTensor V ι.toLinearMap (stRep P ρ g z) = actVdR (P.PD K) ρ g (LinearMap.lTensor V ι.toLinearMap z)) ∧ (∀ w : V ⊗[ℚ_[l]] P.R.B, LinearMap.lTensor V ι.toLinearMap (crisIncl P ℚ_[l] V w) = ιV (P.PD K) (LL := ℚ_[l]) (V := V) w) ∧ ∀ v : V, LinearMap.lTensor V ι.toLinearMap (v ⊗ₜ[ℚ_[l]] (1 : Bst P)) = v ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) := by
  atlas_forward_decl GlobalTheory.InertiaEigenvalues.lTensor_iota_equivariant
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory

theorem cocycle_dies_dR_of_dies_st : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (c : ↥(GK K) → V) (z : V ⊗[ℚ_[l]] Bst P), (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) → ∃ b : V ⊗[ℚ_[l]] P.R.BdR, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) ρ g b - b := by
  intro l _ P AI T K V _ _ ρ c z hz
  obtain ⟨ι, hC, hEq⟩ := GlobalTheory.T.exists_equivariant_log_semistable_to_deRham l P AI T
  obtain ⟨hst, -, hone⟩ := GlobalTheory.T.lTensor_semistable_to_deRham_equivariant l P ι hC hEq K V ρ
  refine ⟨LinearMap.lTensor V ι.toLinearMap z, fun g => ?_⟩
  rw [← hone (c g), hz g, map_sub, hst g z]

end GlobalTheory
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_deRham_of_coboundary_semistable : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (c : ↥(GK K) → V) (z : V ⊗[ℚ_[l]] Bst P), (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) → ∃ b : V ⊗[ℚ_[l]] P.R.BdR, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) ρ g b - b := by
  atlas_forward_decl GlobalTheory.cocycle_dies_dR_of_dies_st
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.CocycStLemma

theorem tmul_one_injective {F V B : Type} [Field F] [AddCommGroup V] [Module F V] [Ring B] [Algebra F B]
    [Nontrivial B] : Function.Injective (fun v : V => v ⊗ₜ[F] (1 : B)) := by
  have hinj : Function.Injective (Algebra.linearMap F B) := (algebraMap F B).injective
  obtain ⟨f, hf⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F B)
    (LinearMap.ker_eq_bot.mpr hinj)
  intro v w h
  have h2 := congrArg (fun x => TensorProduct.rid F V (LinearMap.lTensor V f x)) h
  have h1 : f 1 = 1 := by
    have := LinearMap.congr_fun hf 1
    simpa using this
  simpa [h1] using h2

end GlobalTheory.CocycStLemma

theorem GlobalTheory.cocycle_of_st_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ (z : V ⊗[ℚ_[l]] Bst P) (c : ↥(GK K) → V), (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) → c ∈ continuousCocycles ρ := by
  intro l _ P AI T K V _ _ _ _ _ _ _ ρ hρ z c hc
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ := GlobalTheory.T.coboundary_deRham_of_coboundary_semistable l P AI T K V ρ c z hc
    refine GlobalTheory.T.continuous_cochain_of_deRham_coboundary l P AI T K V ρ hρ 0 Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) b c ?_
    intro g
    simp [hb g]
  · intro g h
    haveI : Nontrivial P.R.B := nontrivial_B P
    haveI : Nontrivial (Bst P) := Polynomial.nontrivial
    apply GlobalTheory.CocycStLemma.tmul_one_injective (F := ℚ_[l]) (B := Bst P)
    simp only [add_tmul]
    rw [hc, hc g, map_mul, Module.End.mul_apply]
    have e : stRep P ρ g (c h ⊗ₜ[ℚ_[l]] (1 : Bst P)) = ρ g (c h) ⊗ₜ[ℚ_[l]] (1 : Bst P) := by
      rw [stRep_tmul, map_one]
    rw [← e, hc h, map_sub]
    abel
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousCocycle_of_semistable_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ (z : V ⊗[ℚ_[l]] Bst P) (c : ↥(GK K) → V), (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) → c ∈ continuousCocycles ρ := by
  atlas_forward_decl GlobalTheory.cocycle_of_st_coboundary
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.FilStable

theorem actVdR_mem_FilV : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V]
    [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (a : ℤ) (g : ↥(GK K))
    (y : V ⊗[ℚ_[l]] P.R.BdR), y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) a →
      actVdR (P.PD K) ρ g y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) a := by
  intro l _ P K V _ _ ρ a g y hy
  obtain ⟨z, rfl⟩ := hy
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Submodule.zero_mem]
  | tmul v b =>
    exact ⟨ρ g v ⊗ₜ[ℚ_[l]] ⟨(P.PD K).actdR g b.1, (P.PD K).Fil_G g a _ b.2⟩, rfl⟩
  | add x y hx hy =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ hx hy

end GlobalTheory.FilStable
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.actVdR_mem_tensorDeRhamFiltration : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (a : ℤ) (g : ↥(GK K)) (y : V ⊗[ℚ_[l]] P.R.BdR), y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) a → actVdR (P.PD K) ρ g y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) a := by
  atlas_forward_decl GlobalTheory.FilStable.actVdR_mem_FilV
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem monSt_surjective_onto {l : ℕ} [Fact l.Prime] (P : LocPrime l) :
    Function.Surjective (monSt P) := by
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact ⟨a + b, map_add _ _ _⟩
  | monomial n a =>
    have hn : ((n + 1 : ℕ) : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    refine ⟨-Polynomial.monomial (n + 1) (((n + 1 : ℕ) : ℚ_[l])⁻¹ • a), ?_⟩
    rw [map_neg, monSt_apply, neg_neg, Polynomial.derivative_monomial, Nat.add_sub_cancel,
      ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, mul_inv_cancel₀ hn, one_smul]

theorem monV_surjective_onto :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V],
      Function.Surjective (monV P ℚ_[l] V) := by
  intro l _ P V _ _ x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul v b =>
    obtain ⟨c, rfl⟩ := monSt_surjective_onto P b
    exact ⟨v ⊗ₜ c, monV_tmul P v c⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

end GlobalTheory.PMon
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monodromyTensorSemistablePeriodRing_surjective : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V], Function.Surjective (monV P ℚ_[l] V) := by
  atlas_forward_decl GlobalTheory.PMon.monV_surjective_onto
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem lTensor_crisIncl_eq_ιV {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR)
    (hι : ∀ b, ι (Polynomial.C b) = P.ιB b) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V]
    (w : V ⊗[ℚ_[l]] P.R.B) :
    LinearMap.lTensor V ι.toLinearMap (crisIncl P ℚ_[l] V w) = ιV (P.PD K) (LL := ℚ_[l]) (V := V) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    rw [crisIncl_tmul, LinearMap.lTensor_tmul]
    simp only [ιV, AlgebraTensorModule.map_tmul, LinearMap.id_coe, id_eq, AlgHom.toLinearMap_apply,
      LinearMap.coe_restrictScalars, hι, P.PD_ι]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem solve_mon_phi_fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → ∀ (K : FinExt l) (V : Type)
    [AddCommGroup V] [Module ℚ_[l] V] (x y : V ⊗[ℚ_[l]] Bst P),
    (l : ℚ_[l]) • phiV P ℚ_[l] V x - x = monV P ℚ_[l] V y → ∃ z : V ⊗[ℚ_[l]] Bst P,
      monV P ℚ_[l] V z = x ∧ phiV P ℚ_[l] V z - z = y ∧
      LinearMap.lTensor V ι.toLinearMap z ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) 0 := by
  intro l _ P AI T ι hι K V _ _ x y h
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.T.monodromyTensorSemistablePeriodRing_surjective l P V x
  have he : monV P ℚ_[l] V (phiV P ℚ_[l] V z₀ - z₀ - y) = 0 := by
    have h1 : monV P ℚ_[l] V (phiV P ℚ_[l] V z₀) = (l : ℚ_[l]) • phiV P ℚ_[l] V x := by
      rw [← End.mul_apply, monV_phiV, LinearMap.smul_apply, End.mul_apply, hz₀]
    rw [map_sub, map_sub, h1, hz₀, h, sub_self]
  obtain ⟨u, hu⟩ := (GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' l P V _).mp he
  obtain ⟨x₁, y₁, hy₁, hx₁, hxy⟩ := (GlobalTheory.T.tensor_fundamental_exact_sequence_crystalline l P AI T K ℚ_[l] V).1 u
    (-(LinearMap.lTensor V ι.toLinearMap z₀))
  refine ⟨z₀ + crisIncl P ℚ_[l] V x₁, ?_, ?_, ?_⟩
  · have h0 : monV P ℚ_[l] V (crisIncl P ℚ_[l] V x₁) = 0 := (GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' l P V _).mpr ⟨x₁, rfl⟩
    rw [map_add, hz₀, h0, add_zero]
  · have h2 : phiV P ℚ_[l] V (crisIncl P ℚ_[l] V x₁) - crisIncl P ℚ_[l] V x₁ = -crisIncl P ℚ_[l] V u := by
      rw [GlobalTheory.T.frobeniusTensor_crisToSemistable_comm l P K V x₁, ← map_sub, ← hx₁, ← map_neg, neg_sub]
    have h3 : phiV P ℚ_[l] V z₀ - z₀ = crisIncl P ℚ_[l] V u + y := by rw [hu]; abel
    calc phiV P ℚ_[l] V (z₀ + crisIncl P ℚ_[l] V x₁) - (z₀ + crisIncl P ℚ_[l] V x₁)
        = (phiV P ℚ_[l] V z₀ - z₀) + (phiV P ℚ_[l] V (crisIncl P ℚ_[l] V x₁) - crisIncl P ℚ_[l] V x₁) := by
          rw [map_add]; abel
      _ = y := by rw [h2, h3]; abel
  · rw [map_add, lTensor_crisIncl_eq_ιV P ι hι K V x₁]
    have : LinearMap.lTensor V ι.toLinearMap z₀ + ιV (P.PD K) (LL := ℚ_[l]) (V := V) x₁ = y₁ := by
      rw [← sub_eq_zero, add_sub_assoc, hxy, add_neg_cancel]
    rw [this]; exact hy₁

end GlobalTheory.PMon
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monodromy_frobenius_solution_fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (x y : V ⊗[ℚ_[l]] Bst P), (l : ℚ_[l]) • phiV P ℚ_[l] V x - x = monV P ℚ_[l] V y → ∃ z : V ⊗[ℚ_[l]] Bst P, monV P ℚ_[l] V z = x ∧ phiV P ℚ_[l] V z - z = y ∧ LinearMap.lTensor V ι.toLinearMap z ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) 0 := by
  atlas_forward_decl GlobalTheory.PMon.solve_mon_phi_fil
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem exists_eq_tmul_one_of_mon_phi_fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (z : V ⊗[ℚ_[l]] Bst P), monV P ℚ_[l] V z = 0 → phiV P ℚ_[l] V z = z → LinearMap.lTensor V ι.toLinearMap z ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) 0 → ∃ v : V, z = v ⊗ₜ[ℚ_[l]] (1 : Bst P) := by
  intro l _ P AI T ι hι K V _ _ z hN hφ hF
  obtain ⟨w, rfl⟩ := (GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' l P V z).mp hN
  rw [GlobalTheory.T.frobeniusTensor_crisToSemistable_comm l P K V w] at hφ
  have hw := crisIncl_injective P hφ
  have key : ∀ x : V ⊗[ℚ_[l]] P.R.B, LinearMap.lTensor V ι.toLinearMap (crisIncl P ℚ_[l] V x) =
      ιV (P.PD K) (LL := ℚ_[l]) (V := V) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [ιV, hι, P.PD_ι]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [key] at hF
  obtain ⟨v, rfl⟩ := (GlobalTheory.FundSeq.tensor_fundamental_sequence l P AI T K ℚ_[l] V).2 w hw hF
  exact ⟨v, by rw [crisIncl_tmul, Polynomial.C_1]⟩

end GlobalTheory.PMon
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_tmul_one_of_monodromy_frobenius_filtration : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (z : V ⊗[ℚ_[l]] Bst P), monV P ℚ_[l] V z = 0 → phiV P ℚ_[l] V z = z → LinearMap.lTensor V ι.toLinearMap z ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) 0 → ∃ v : V, z = v ⊗ₜ[ℚ_[l]] (1 : Bst P) := by
  atlas_forward_decl GlobalTheory.PMon.exists_eq_tmul_one_of_mon_phi_fil
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem GlobalTheory.semistable_class_of_pair : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ x ∈ Dst P ρ, ∀ y ∈ Dst P ρ, (l : ℚ_[l]) • phiV P ℚ_[l] V x - x = monV P ℚ_[l] V y → ∃ (z : V ⊗[ℚ_[l]] Bst P) (c : ↥(GK K) → V), c ∈ continuousCocycles ρ ∧ (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) ∧ monV P ℚ_[l] V z = x := by
  intro l _ P AI T K V _ _ _ _ _ _ _ ρ hρ x hx y hy hxy
  obtain ⟨ι, hιC, hιact⟩ := GlobalTheory.T.exists_equivariant_log_semistable_to_deRham l P AI T
  obtain ⟨hιst, -, -⟩ := GlobalTheory.T.lTensor_semistable_to_deRham_equivariant l P ι hιC hιact K V ρ
  obtain ⟨z, hNz, hφz, hFz⟩ := GlobalTheory.T.exists_monodromy_frobenius_solution_fil l P AI T ι hιC K V x y hxy
  have hx' := (mem_Dst P ρ).mp hx
  have hy' := (mem_Dst P ρ).mp hy
  have hw : ∀ g : ↥(GK K), ∃ v : V, stRep P ρ g z - z = v ⊗ₜ[ℚ_[l]] (1 : Bst P) := by
    intro g
    refine GlobalTheory.T.exists_eq_tmul_one_of_monodromy_frobenius_filtration l P AI T ι hιC K V (stRep P ρ g z - z) ?_ ?_ ?_
    · rw [map_sub, ← Module.End.mul_apply, monV_stRep, Module.End.mul_apply, hNz, hx', sub_self]
    · have hφz' : phiV P ℚ_[l] V z = z + y := by rw [← hφz]; abel
      rw [map_sub, ← Module.End.mul_apply, phiV_stRep, Module.End.mul_apply, hφz', map_add, hy']
      abel
    · rw [map_sub, hιst]
      exact Submodule.sub_mem _ (GlobalTheory.T.actVdR_mem_tensorDeRhamFiltration l P K V ρ 0 g _ hFz) hFz
  choose c hc using hw
  have hc' : ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z := fun g => (hc g).symm
  exact ⟨z, c, GlobalTheory.T.continuousCocycle_of_semistable_coboundary l P AI T K V ρ hρ z c hc', hc', hNz⟩
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistable_cocycle_of_frobenius_monodromy_pair : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ x ∈ Dst P ρ, ∀ y ∈ Dst P ρ, (l : ℚ_[l]) • phiV P ℚ_[l] V x - x = monV P ℚ_[l] V y → ∃ (z : V ⊗[ℚ_[l]] Bst P) (c : ↥(GK K) → V), c ∈ continuousCocycles ρ ∧ (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) ∧ monV P ℚ_[l] V z = x := by
  atlas_forward_decl GlobalTheory.semistable_class_of_pair
end

section
section
open TensorProduct Module

namespace GlobalTheory

theorem finrank_add_le_finrank_range_add_of_comap_le : ∀ (k : Type) [Field k] (E A M : Type) [AddCommGroup E] [Module k E] [AddCommGroup A] [Module k A] [AddCommGroup M] [Module k M] (π : E →ₗ[k] A) (ν : E →ₗ[k] M) (Z : Submodule k A) (R U : Submodule k M) [FiniteDimensional k ↥(LinearMap.range π)] [FiniteDimensional k ↥U], Z ≤ LinearMap.range π → R ≤ U → U ≤ LinearMap.range ν → (∀ e, π e ∈ Z → ν e ∈ R) → finrank k ↥Z + finrank k ↥U ≤ finrank k ↥(LinearMap.range π) + finrank k ↥R := by
  intro k _ E A M _ _ _ _ _ _ π ν Z R U _ _ hZ hRU hU hmap
  set Q := LinearMap.range π with hQ
  set Z' : Submodule k Q := Z.comap Q.subtype
  set R' : Submodule k U := R.comap U.subtype
  have hZ' : finrank k Z' = finrank k Z := (Submodule.comapSubtypeEquivOfLe hZ).finrank_eq
  have hR' : finrank k R' = finrank k R := (Submodule.comapSubtypeEquivOfLe hRU).finrank_eq
  set K : Submodule k E := U.comap ν
  let g : K →ₗ[k] Q ⧸ Z' := Z'.mkQ ∘ₗ π.rangeRestrict ∘ₗ K.subtype
  let f : K →ₗ[k] U ⧸ R' := R'.mkQ ∘ₗ ((ν ∘ₗ K.subtype).codRestrict U (fun x => x.2))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨u, rfl⟩ := R'.mkQ_surjective y
    obtain ⟨e, he⟩ := hU u.2
    have heU : ν e ∈ U := he ▸ u.2
    refine ⟨⟨e, heU⟩, ?_⟩
    have hu : ((ν ∘ₗ K.subtype).codRestrict U (fun x => x.2)) ⟨e, heU⟩ = u := Subtype.ext he
    exact congrArg R'.mkQ hu
  have hker : LinearMap.ker g ≤ LinearMap.ker f := by
    intro x hx
    have h0 : Submodule.Quotient.mk (p := Z') (π.rangeRestrict (x : E)) = 0 := LinearMap.mem_ker.mp hx
    have hx' : π (x : E) ∈ Z := (Submodule.Quotient.mk_eq_zero (p := Z')).mp h0
    have hy : ν (x : E) ∈ R := hmap _ hx'
    rw [LinearMap.mem_ker]
    exact (Submodule.Quotient.mk_eq_zero (p := R')
      (x := ((ν ∘ₗ K.subtype).codRestrict U (fun x => x.2)) x)).mpr hy
  let gq := (LinearMap.ker g).liftQ g le_rfl
  let fq := (LinearMap.ker g).liftQ f hker
  have hgq : Function.Injective gq := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  have hfq : Function.Surjective fq := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have : Module.Finite k (K ⧸ LinearMap.ker g) := Module.Finite.of_injective gq hgq
  have key : finrank k (U ⧸ R') ≤ finrank k (Q ⧸ Z') :=
    (LinearMap.finrank_le_finrank_of_surjective hfq).trans
      (LinearMap.finrank_le_finrank_of_injective hgq)
  have h1 := Submodule.finrank_quotient_add_finrank R'
  have h2 := Submodule.finrank_quotient_add_finrank Z'
  omega

end GlobalTheory
end

open TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_add_finrank_le_finrank_range_add_finrank : ∀ (k : Type) [Field k] (E A M : Type) [AddCommGroup E] [Module k E] [AddCommGroup A] [Module k A] [AddCommGroup M] [Module k M] (π : E →ₗ[k] A) (ν : E →ₗ[k] M) (Z : Submodule k A) (R U : Submodule k M) [FiniteDimensional k ↥(LinearMap.range π)] [FiniteDimensional k ↥U], Z ≤ LinearMap.range π → R ≤ U → U ≤ LinearMap.range ν → (∀ e, π e ∈ Z → ν e ∈ R) → finrank k ↥Z + finrank k ↥U ≤ finrank k ↥(LinearMap.range π) + finrank k ↥R := by
  atlas_forward_decl GlobalTheory.finrank_add_le_finrank_range_add_of_comap_le
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

noncomputable def stPairs {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {V : Type} [AddCommGroup V]
    [Module ℚ_[l] V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V) : Submodule ℚ_[l] ((↥(GK K) → V) × (V ⊗[ℚ_[l]] Bst P)) where
  carrier := {p | p.1 ∈ continuousCocycles ρ ∧ ∀ g, p.1 g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g p.2 - p.2}
  zero_mem' := ⟨(continuousCocycles ρ).zero_mem, fun g => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, hx⟩ ⟨hb, hy⟩
    refine ⟨(continuousCocycles ρ).add_mem ha hb, fun g => ?_⟩
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_tmul, hx, hy, map_add]
    abel
  smul_mem' := by
    rintro c a ⟨ha, hx⟩
    refine ⟨(continuousCocycles ρ).smul_mem c ha, fun g => ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul, ← smul_sub, ← hx]
    rfl

theorem exists_stCocycles_lower : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v : V, Continuous fun g => ρ g v) → IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → Module.Finite ℚ_[l] ↥(continuousCocycles ρ) → ∃ S : Submodule ℚ_[l] (↥(GK K) → V), finiteCocycles (P.PD K) ρ ≤ S ∧ S ≤ continuousCocycles ρ ∧ (∀ c ∈ S, ∃ z : V ⊗[ℚ_[l]] Bst P, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) ∧ (∀ c ∈ S, ∃ b : V ⊗[ℚ_[l]] P.R.BdR, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) ρ g b - b) ∧ finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) ≤ finrank ℚ_[l] ↥S := by
  intro l _ P AI T K V _ _ _ _ _ _ _ V' _ _ _ ρ ρ' m hc hd hs hfin
  let π : ↥(stPairs P ρ) →ₗ[ℚ_[l]] (↥(GK K) → V) := (LinearMap.fst _ _ _).comp (stPairs P ρ).subtype
  let ν : ↥(stPairs P ρ) →ₗ[ℚ_[l]] (V ⊗[ℚ_[l]] Bst P) :=
    (monV P ℚ_[l] V).comp ((LinearMap.snd _ _ _).comp (stPairs P ρ).subtype)
  have hcris : ∀ (c : ↥(GK K) → V) (x : V ⊗[ℚ_[l]] P.R.B),
      (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) ρ g x - x) →
      ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g (crisIncl P ℚ_[l] V x) - crisIncl P ℚ_[l] V x := by
    intro c x hx g
    rw [stRep_crisIncl, ← map_sub, ← hx, crisIncl_tmul, map_one]
  have h1 : finiteCocycles (P.PD K) ρ ≤ LinearMap.range π := by
    rintro c ⟨hc1, x, hx⟩
    exact ⟨⟨(c, crisIncl P ℚ_[l] V x), hc1, hcris c x hx⟩, rfl⟩
  have h2 : LinearMap.range π ≤ continuousCocycles ρ := by
    rintro _ ⟨e, rfl⟩
    exact e.2.1
  have h3 : ∀ c ∈ LinearMap.range π, ∃ z : V ⊗[ℚ_[l]] Bst P,
      ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z := by
    rintro _ ⟨e, rfl⟩
    exact ⟨e.1.2, e.2.2⟩
  refine ⟨LinearMap.range π, h1, h2, h3, fun c hc => ?_, ?_⟩
  · obtain ⟨z, hz⟩ := h3 c hc
    exact GlobalTheory.T.coboundary_deRham_of_coboundary_semistable l P AI T K V ρ c z hz
  have hφ : ∀ y ∈ Dst P ρ, phiV P ℚ_[l] V y ∈ Dst P ρ := fun y hy =>
    (mem_Dst P ρ).mpr fun g => by
      rw [← End.mul_apply, ← phiV_stRep, End.mul_apply, (mem_Dst P ρ).mp hy g]
  have hN : ∀ y ∈ Dst P ρ, monV P ℚ_[l] V y ∈ Dst P ρ := fun y hy =>
    (mem_Dst P ρ).mpr fun g => by
      rw [← End.mul_apply, ← monV_stRep, End.mul_apply, (mem_Dst P ρ).mp hy g]
  haveI := GlobalTheory.T.finiteDimensional_Dst_of_isSst' l P K V ρ hs
  haveI : FiniteDimensional ℚ_[l] ↥(LinearMap.range π) := Submodule.finiteDimensional_of_le h2
  haveI : FiniteDimensional ℚ_[l] ↥(Dst P ρ ⊓ ((Dst P ρ).map (monV P ℚ_[l] V)).comap
      ((l : ℚ_[l]) • phiV P ℚ_[l] V - LinearMap.id)) := Submodule.finiteDimensional_of_le inf_le_left
  have h4 := GlobalTheory.T.finrank_add_finrank_le_finrank_range_add_finrank ℚ_[l] _ _ _ π ν (finiteCocycles (P.PD K) ρ) ((Dst P ρ).map (monV P ℚ_[l] V))
    (Dst P ρ ⊓ ((Dst P ρ).map (monV P ℚ_[l] V)).comap ((l : ℚ_[l]) • phiV P ℚ_[l] V - LinearMap.id)) h1
    (by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨hN y hy, phiV P ℚ_[l] V y - y, Submodule.sub_mem _ (hφ y hy) hy, ?_⟩
      rw [map_sub, ← End.mul_apply, monV_phiV]
      rfl)
    (by
      rintro x ⟨hx, y, hy, hxy⟩
      obtain ⟨z, c, hc1, hc2, hz⟩ := GlobalTheory.T.semistable_cocycle_of_frobenius_monodromy_pair l P AI T K V ρ hc x hx y hy hxy.symm
      exact ⟨⟨(c, z), hc1, hc2⟩, hz⟩)
    (by
      rintro e ⟨-, x, hx⟩
      refine ⟨e.1.2 - crisIncl P ℚ_[l] V x, (mem_Dst P ρ).mpr fun g => ?_, ?_⟩
      · have := (e.2.2 g).symm.trans (hcris _ x hx g)
        rw [map_sub, sub_eq_sub_iff_sub_eq_sub]
        exact this
      · rw [map_sub, (GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' l P V _).mpr ⟨x, rfl⟩, sub_zero]
        rfl)
  have h5 := GlobalTheory.T.finrank_dcris_phi_fixed_add_finrank_mon_le_alt l P AI T K V V' ρ ρ' m hd hs
  omega

end GlobalTheory.PMon
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistable_cocycles_between_blochKato_and_continuous : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v : V, Continuous fun g => ρ g v) → IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → Module.Finite ℚ_[l] ↥(continuousCocycles ρ) → ∃ S : Submodule ℚ_[l] (↥(GK K) → V), finiteCocycles (P.PD K) ρ ≤ S ∧ S ≤ continuousCocycles ρ ∧ (∀ c ∈ S, ∃ z : V ⊗[ℚ_[l]] Bst P, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) ∧ (∀ c ∈ S, ∃ b : V ⊗[ℚ_[l]] P.R.BdR, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) ρ g b - b) ∧ finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) ≤ finrank ℚ_[l] ↥S := by
  atlas_forward_decl GlobalTheory.PMon.exists_stCocycles_lower
end
