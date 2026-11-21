import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTypePlaceCompletionIdentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClassMapCorrespondenceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeComponentsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSupportCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroSupercuspidalCuspidalModuleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameParameterCoupledStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LabLPIsLabelActK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ValuationLtOneIffNormLtOnePadicCmCompletion

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitUniqSer

theorem splitPlace_unique : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s s' : SplitPlace L),
    s.w = s'.w → s = s' :=
  GlobalTheory.SplitUniq.splitPlace_eq_of_w_eq

end GlobalTheory.SplitUniqSer
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmSplitPlace_eq_of_prime_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s s' : SplitPlace L), s.w = s'.w → s = s' := by
  atlas_forward_decl GlobalTheory.SplitUniqSer.splitPlace_unique
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_lt_one_iff_norm_lt_one_padic_cmCompletion : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (g : ℕ) [Fact g.Prime] (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (j : ℚ_[g] ≃+* s.w.adicCompletion L), Continuous i → Continuous j → ∀ z : s.v.adicCompletion (maximalRealSubfield L), Valued.v z < 1 ↔ ‖j.symm (i z)‖ < 1 := by
  first | exact @GlobalTheory.valuation_lt_one_iff_norm_lt_one_of_continuous | exact GlobalTheory.valuation_lt_one_iff_norm_lt_one_of_continuous | (intros; apply GlobalTheory.valuation_lt_one_iff_norm_lt_one_of_continuous <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LiftRed

theorem liftred_exists : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g n : ℕ) [Fact g.Prime] (θ : v.adicCompletion F ≃+* ℚ_[g]), (∀ z, Valued.v z < 1 → ‖θ z‖ < 1) → ∀ (A : GL (Fin n) (v.adicCompletion F)) (γ : GL (Fin n) (ZMod g)), (∀ a b, Valued.v ((A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b - ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : v.adicCompletion F)) < 1) → ∃ k ∈ (GlobalTheory.GLp.red g n).ker, Matrix.GeneralLinearGroup.map θ.toRingHom A = GlobalTheory.GLp.lift g n γ * GlobalTheory.GLp.inc g n k := by
  intro F _ _ v g n _ θ hθ A γ hA

  have hent : ∀ a b, ‖θ ((A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b) -
      ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : ℚ_[g])‖ < 1 := by
    intro a b
    have h := hθ _ (hA a b)
    rwa [map_sub, map_natCast] at h
  have hle : ∀ a b, ‖θ ((A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b)‖ ≤ 1 := by
    intro a b
    have h1 : ‖((((γ : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : ℚ_[g])‖ ≤ 1 := by
      exact_mod_cast PadicInt.norm_le_one ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : ℤ_[g])
    have := IsUltrametricDist.norm_add_le_max
      (θ ((A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b) -
        ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : ℚ_[g]))
      ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : ℚ_[g])
    rw [sub_add_cancel] at this
    exact this.trans (max_le (le_of_lt (hent a b)) h1)
  let Mx : Matrix (Fin n) (Fin n) ℤ_[g] := fun a b => ⟨θ ((A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b), hle a b⟩
  have hred : Mx.map (PadicInt.toZMod (p := g)) = (γ : Matrix (Fin n) (Fin n) (ZMod g)) := by
    ext a b
    simp only [Matrix.map_apply]
    have hm : Mx a b - ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : ℤ_[g]) ∈
        RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast]
      exact hent a b
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_eq_zero] at hm
    exact hm
  have hdet : IsUnit Mx.det := by
    by_contra hnu
    have hm : Mx.det ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
      exact hnu
    rw [RingHom.mem_ker, RingHom.map_det,
      show (PadicInt.toZMod (p := g)).mapMatrix Mx = (γ : Matrix (Fin n) (Fin n) (ZMod g)) from hred] at hm
    have hu : IsUnit (γ : Matrix (Fin n) (Fin n) (ZMod g)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit
    rw [hm] at hu
    exact not_isUnit_zero hu
  let M : GL (Fin n) ℤ_[g] := Matrix.nonsingInvUnit Mx hdet
  have hMred : GlobalTheory.GLp.red g n M = γ := by
    ext a b
    have := congrFun (congrFun hred a) b
    exact this
  have hMinc : GlobalTheory.GLp.inc g n M = Matrix.GeneralLinearGroup.map θ.toRingHom A := by
    ext a b
    rfl
  set N := Function.invFun (GlobalTheory.GLp.red g n) γ with hN
  have hNred : GlobalTheory.GLp.red g n N = γ := Function.invFun_eq ⟨M, hMred⟩
  refine ⟨N⁻¹ * M, ?_, ?_⟩
  · rw [MonoidHom.mem_ker, map_mul, map_inv, hNred, hMred, inv_mul_cancel]
  · rw [GlobalTheory.GLp.lift, ← hN, ← map_mul, mul_inv_cancel_left, hMinc]

end GlobalTheory.LiftRed
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padic_lift_mul_principalCongruence_of_reduction : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g n : ℕ) [Fact g.Prime] (θ : v.adicCompletion F ≃+* ℚ_[g]), (∀ z, Valued.v z < 1 → ‖θ z‖ < 1) → ∀ (A : GL (Fin n) (v.adicCompletion F)) (γ : GL (Fin n) (ZMod g)), (∀ a b, Valued.v ((A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b - ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : v.adicCompletion F)) < 1) → ∃ k ∈ (GlobalTheory.GLp.red g n).ker, Matrix.GeneralLinearGroup.map θ.toRingHom A = GlobalTheory.GLp.lift g n γ * GlobalTheory.GLp.inc g n k := by
  atlas_forward_decl GlobalTheory.LiftRed.liftred_exists
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem GLp.inc_map_sub_one_valued_lt_one : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g n : ℕ) [Fact g.Prime] (θ : v.adicCompletion F ≃+* ℚ_[g]), (∀ z, ‖θ z‖ < 1 → Valued.v z < 1) → ∀ k ∈ (GlobalTheory.GLp.red g n).ker, ∀ a b : Fin n, Valued.v ((Matrix.GeneralLinearGroup.map θ.symm.toRingHom (GlobalTheory.GLp.inc g n k) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b - (((((1 : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : v.adicCompletion F)) < 1 := by
  intro F _ _ v g n _ θ hθ k hk a b
  have hk' : PadicInt.toZMod ((k : Matrix (Fin n) (Fin n) ℤ_[g]) a b) =
      ((1 : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) a b := by
    have := congrArg (fun x : GL (Fin n) (ZMod g) => (x : Matrix (Fin n) (Fin n) (ZMod g)) a b)
      (MonoidHom.mem_ker.mp hk)
    simpa [GlobalTheory.GLp.red] using this
  set c : ℕ := (((1 : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) a b).val with hc
  have hmem : (k : Matrix (Fin n) (Fin n) ℤ_[g]) a b - (c : ℤ_[g]) ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
    rw [RingHom.mem_ker, map_sub, hk', map_natCast, hc, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZMod] at hmem
  have hnorm : ‖(k : Matrix (Fin n) (Fin n) ℤ_[g]) a b - (c : ℤ_[g])‖ < 1 := PadicInt.mem_nonunits.mp hmem
  apply hθ
  have he : θ ((Matrix.GeneralLinearGroup.map θ.symm.toRingHom (GlobalTheory.GLp.inc g n k) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b - (c : v.adicCompletion F)) =
      (((k : Matrix (Fin n) (Fin n) ℤ_[g]) a b - (c : ℤ_[g]) : ℤ_[g]) : ℚ_[g]) := by
    simp [GlobalTheory.GLp.inc, Matrix.GeneralLinearGroup.map]
  rw [he, PadicInt.padic_norm_e_of_padicInt]
  exact hnorm

end GlobalTheory
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruence_map_completion_sub_one_valued_lt : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g n : ℕ) [Fact g.Prime] (θ : v.adicCompletion F ≃+* ℚ_[g]), (∀ z, ‖θ z‖ < 1 → Valued.v z < 1) → ∀ k ∈ (GlobalTheory.GLp.red g n).ker, ∀ a b : Fin n, Valued.v ((Matrix.GeneralLinearGroup.map θ.symm.toRingHom (GlobalTheory.GLp.inc g n k) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b - (((((1 : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : v.adicCompletion F)) < 1 := by
  atlas_forward_decl GlobalTheory.GLp.inc_map_sub_one_valued_lt_one
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem indep_subfamily_of_disjoint_or_le : ∀ (ι M : Type) [AddCommGroup M] [Module ℂ M] (N : ι → Submodule ℂ M), (∀ i (J : Finset ι), Disjoint (N i) (⨆ j ∈ J, N j) ∨ N i ≤ ⨆ j ∈ J, N j) → ∀ F : Finset ι, ∃ J ⊆ F, (⨆ j ∈ J, N j) = (⨆ j ∈ F, N j) ∧ ∀ f f' : ι → M, (∀ j ∈ J, f j ∈ N j) → (∀ j ∈ J, f' j ∈ N j) → ∑ j ∈ J, f j = ∑ j ∈ J, f' j → ∀ j ∈ J, f j = f' j := by
  intro ι M _ _ N h F
  classical
  refine Finset.induction_on F ?_ ?_
  · exact ⟨∅, Finset.Subset.refl _, rfl, by simp⟩
  · intro i F hi ih
    obtain ⟨J, hJF, hJsup, huniq⟩ := ih
    have hiJ : i ∉ J := fun hh => hi (hJF hh)
    rcases h i J with hd | hle
    · refine ⟨insert i J, Finset.insert_subset_insert _ hJF, ?_, ?_⟩
      · rw [Finset.iSup_insert, Finset.iSup_insert, hJsup]
      · intro f f' hf hf' hsum
        rw [Finset.sum_insert hiJ, Finset.sum_insert hiJ] at hsum
        have hdiff : f i - f' i = ∑ j ∈ J, f' j - ∑ j ∈ J, f j := by
          rw [sub_eq_sub_iff_add_eq_add, hsum, add_comm]
        have hmem : f i - f' i ∈ N i ⊓ ⨆ j ∈ J, N j := by
          refine ⟨Submodule.sub_mem _ (hf i (Finset.mem_insert_self _ _))
            (hf' i (Finset.mem_insert_self _ _)), ?_⟩
          rw [hdiff]
          exact Submodule.sub_mem _
            (Submodule.sum_mem_biSup fun j hj => hf' j (Finset.mem_insert_of_mem hj))
            (Submodule.sum_mem_biSup fun j hj => hf j (Finset.mem_insert_of_mem hj))
        rw [hd.eq_bot, Submodule.mem_bot, sub_eq_zero] at hmem
        rw [hmem] at hsum
        have hJs : ∑ j ∈ J, f j = ∑ j ∈ J, f' j := add_left_cancel hsum
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hmem
        · exact huniq f f' (fun k hk => hf k (Finset.mem_insert_of_mem hk))
            (fun k hk => hf' k (Finset.mem_insert_of_mem hk)) hJs j hj
    · refine ⟨J, hJF.trans (Finset.subset_insert _ _), ?_, huniq⟩
      rw [Finset.iSup_insert, ← hJsup]
      exact (sup_eq_right.mpr hle).symm

end GlobalTheory
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_independent_subfamily_same_iSup : ∀ (ι M : Type) [AddCommGroup M] [Module ℂ M] (N : ι → Submodule ℂ M), (∀ i (J : Finset ι), Disjoint (N i) (⨆ j ∈ J, N j) ∨ N i ≤ ⨆ j ∈ J, N j) → ∀ F : Finset ι, ∃ J ⊆ F, (⨆ j ∈ J, N j) = (⨆ j ∈ F, N j) ∧ ∀ f f' : ι → M, (∀ j ∈ J, f j ∈ N j) → (∀ j ∈ J, f' j ∈ N j) → ∑ j ∈ J, f j = ∑ j ∈ J, f' j → ∀ j ∈ J, f j = f' j := by
  atlas_forward_decl GlobalTheory.indep_subfamily_of_disjoint_or_le
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SerSys

theorem finTyp_eq_iSup_rt_local : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (s : SplitPlace L) (V : Type) [AddCommGroup V] [Module ℂ V] [Nontrivial V] (T : V →ₗ[ℂ] (GAf L n → ℂ)), Function.Injective T → (∀ a, T a ∈ π.S) → (∀ x : GAf L n, TrivOutside {s.v} x → ∀ a, ∃ b, NG.rt L n x (T a) = T b) → π.S = ⨆ y : {y : GAf L n // TrivOutside {s.v}ᶜ y}, LinearMap.range ((NG.rt L n y.1).comp T) := by
  intro L _ _ _ n π s V _ _ _ T hT hTS hx
  obtain ⟨hdec, hcomm, -⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  have hrt : ∀ (h h' : GAf L n) (f : GAf L n → ℂ), NG.rt L n h (NG.rt L n h' f) = NG.rt L n (h * h') f := by
    intro h h' f; funext g; simp [NG.rt, mul_assoc]
  have hone : ∀ f : GAf L n → ℂ, NG.rt L n 1 f = f := by
    intro f; funext g; simp [NG.rt]
  have h1 : TrivOutside {s.v}ᶜ (1 : GAf L n) := by
    intro v _; simp
  set Wd := ⨆ y : {y : GAf L n // TrivOutside {s.v}ᶜ y}, LinearMap.range ((NG.rt L n y.1).comp T) with hWd
  have hle : Wd ≤ π.S := by
    refine iSup_le fun y => ?_
    rintro f ⟨a, rfl⟩
    exact π.stable _ _ (hTS a)
  have hstab : ∀ h, ∀ f ∈ Wd, NG.rt L n h f ∈ Wd := by
    intro h f hf
    refine Submodule.iSup_induction _ (motive := fun f => NG.rt L n h f ∈ Wd) hf ?_ ?_ ?_
    · rintro y _ ⟨a, rfl⟩
      obtain ⟨x, y', hx1, hy', he⟩ := hdec (h * y.1)
      obtain ⟨b, hb⟩ := hx x hx1 a
      have : NG.rt L n h (NG.rt L n y.1 (T a)) = NG.rt L n y' (T b) := by
        rw [hrt, he, (hcomm x y' hx1 hy').eq, ← hrt, hb]
      simp only [LinearMap.comp_apply]
      rw [this]
      exact Submodule.mem_iSup_of_mem (⟨y', hy'⟩ : {y : GAf L n // TrivOutside {s.v}ᶜ y}) ⟨b, rfl⟩
    · simp
    · intro f₁ f₂ h₁ h₂; rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  rcases π.irr Wd hle hstab with h0 | h0
  · exfalso
    obtain ⟨a, ha⟩ := exists_ne (0 : V)
    have hmem : T a ∈ Wd := by
      have := Submodule.mem_iSup_of_mem (p := fun y : {y : GAf L n // TrivOutside {s.v}ᶜ y} => LinearMap.range ((NG.rt L n y.1).comp T)) (⟨1, h1⟩ : {y : GAf L n // TrivOutside {s.v}ᶜ y}) (⟨a, rfl⟩ : ((NG.rt L n 1).comp T) a ∈ LinearMap.range ((NG.rt L n 1).comp T))
      simpa [hone] using this
    rw [h0, Submodule.mem_bot] at hmem
    exact ha (hT (by rw [hmem, map_zero]))
  · exact h0.symm

end GlobalTheory.SerSys
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteType_eq_iSup_splitTrivial_translates_local : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (s : SplitPlace L) (V : Type) [AddCommGroup V] [Module ℂ V] [Nontrivial V] (T : V →ₗ[ℂ] (GAf L n → ℂ)), Function.Injective T → (∀ a, T a ∈ π.S) → (∀ x : GAf L n, TrivOutside {s.v} x → ∀ a, ∃ b, NG.rt L n x (T a) = T b) → π.S = ⨆ y : {y : GAf L n // TrivOutside {s.v}ᶜ y}, LinearMap.range ((NG.rt L n y.1).comp T) := by
  atlas_forward_decl GlobalTheory.SerSys.finTyp_eq_iSup_rt_local
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.SlocDich.translate_dichotomy : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)), Function.Injective T → (∀ x : GAf L n, TrivOutside {s.v} x → ∀ a, T (τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T a)) → ∀ y : GAf L n, TrivOutside {s.v}ᶜ y → ∀ P : Submodule ℂ (GAf L n → ℂ), (∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ P, NG.rt L n x f ∈ P) → Disjoint (LinearMap.range ((NG.rt L n y).comp T)) P ∨ LinearMap.range ((NG.rt L n y).comp T) ≤ P := by
  intro L _ _ _ n s τ i T _hTi hT y hy P hP
  have hpart := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s

  have hstab : ∀ (g : GL (Fin n) (s.w.adicCompletion L)) (a : τ.V),
      a ∈ P.comap ((NG.rt L n y).comp T) → τ.ρ g a ∈ P.comap ((NG.rt L n y).comp T) := by
    intro g a ha
    obtain ⟨x, ⟨hx, hxA⟩, -⟩ := hpart.2.2 (Matrix.GeneralLinearGroup.map i.symm.toRingHom g)
    have hg : g = Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x) := by
      rw [hxA]; ext j k; simp
    have hc := hpart.2.1 x y hx hy
    simp only [Submodule.mem_comap, LinearMap.comp_apply] at ha ⊢
    rw [hg, hT x hx a]
    have e : NG.rt L n y (NG.rt L n x (T a)) = NG.rt L n x (NG.rt L n y (T a)) := by
      funext g'
      show T a (g' * y * x) = T a (g' * x * y)
      rw [mul_assoc, mul_assoc, hc.eq]
    rw [e]
    exact hP x hx _ ha
  let Q : Subrepresentation τ.ρ := ⟨P.comap ((NG.rt L n y).comp T), hstab⟩
  rcases τ.irr.eq_bot_or_eq_top Q with h | h
  · left
    rw [Submodule.disjoint_def]
    rintro f ⟨a, rfl⟩ hf
    have ha : a ∈ Q.toSubmodule := hf
    rw [h] at ha
    have : a = 0 := ha
    simp [this]
  · right
    rintro f ⟨a, rfl⟩
    have ha : a ∈ Q.toSubmodule := by rw [h]; trivial
    exact ha
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTrivialTranslate_localComponent_disjoint_or_le : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)), Function.Injective T → (∀ x : GAf L n, TrivOutside {s.v} x → ∀ a, T (τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T a)) → ∀ y : GAf L n, TrivOutside {s.v}ᶜ y → ∀ P : Submodule ℂ (GAf L n → ℂ), (∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ P, NG.rt L n x f ∈ P) → Disjoint (LinearMap.range ((NG.rt L n y).comp T)) P ∨ LinearMap.range ((NG.rt L n y).comp T) ≤ P := by
  atlas_forward_decl GlobalTheory.SlocDich.translate_dichotomy
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM

noncomputable section

open GlobalTheory.LabPin

namespace GlobalTheory.DepthZeroSer

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem rt_rt' {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (h h' : GAf L n) (f : GAf L n → ℂ) :
    NG.rt L n h (NG.rt L n h' f) = NG.rt L n (h * h') f := by
  funext x; simp [NG.rt, mul_assoc]

theorem rt_one' {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (f : GAf L n → ℂ) :
    NG.rt L n 1 f = f := by
  funext x; simp [NG.rt]

theorem nontrivial_of_irr {G : Type} [Group G] [TopologicalSpace G] (τ : GlobalTheory.SmGL.IrrRep G) : Nontrivial τ.V := by
  haveI := τ.irr
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply (bot_ne_top : (⊥ : Subrepresentation τ.ρ) ≠ ⊤)
  ext x
  simp [Subsingleton.elim x 0]

theorem serFix_of_locS {L : Type} [Field L] [NumberField L] [IsCMField L] {n g : ℕ} [Fact g.Prime]
    (π : NG.FinTyp L n) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (j : ℚ_[g] ≃+* s.w.adicCompletion L) (hj : Continuous j) (a : MonoidAlgebra ℂ (GL (Fin n) (ZMod g)))
    (hloc : GlobalTheory.HeightCounting.IsLocS π.S s τ)
    (ha : ∀ y ∈ GlobalTheory.GLp.fixK1 (τ.ρ.comp (Matrix.GeneralLinearGroup.map j.toRingHom)),
      GlobalTheory.GLp.actK (τ.ρ.comp (Matrix.GeneralLinearGroup.map j.toRingHom)) a y = y) :
    SerFix π s a := by
  classical
  obtain ⟨i, T, hi, -, hT, hTS, hTeq⟩ := hloc
  set ρ' := τ.ρ.comp (Matrix.GeneralLinearGroup.map (n := Fin n) j.toRingHom) with hρ'
  set θ : s.v.adicCompletion (maximalRealSubfield L) ≃+* ℚ_[g] := i.trans j.symm with hθdef
  have hθ : ∀ z, Valued.v z < 1 ↔ ‖θ z‖ < 1 := fun z => GlobalTheory.T.valuation_lt_one_iff_norm_lt_one_padic_cmCompletion L s g i j hi hj z
  have hτθ : ∀ A : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)),
      τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom A) = ρ' (Matrix.GeneralLinearGroup.map θ.toRingHom A) := by
    intro A
    simp only [hρ', MonoidHom.coe_comp, Function.comp_apply]
    congr 1
    ext a b
    simp [θ]
  have hI := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  haveI := nontrivial_of_irr τ
  intro ℓ hℓ φ hφS hφfix
  let N : {y : GAf L n // TrivOutside {s.v}ᶜ y} → Submodule ℂ (GAf L n → ℂ) :=
    fun y => LinearMap.range ((NG.rt L n y.1).comp T)
  have hspan := GlobalTheory.T.finiteType_eq_iSup_splitTrivial_translates_local L n π s τ.V T hT hTS (fun x hx a => ⟨_, (hTeq x hx a).symm⟩)
  have hNst : ∀ y x, TrivOutside {s.v} x → ∀ f ∈ N y, NG.rt L n x f ∈ N y := by
    rintro y x hx f ⟨b, rfl⟩
    refine ⟨τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) b, ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [hTeq x hx b, rt_rt', rt_rt', (hI.2.1 x y.1 hx y.2).eq]
  have hsupst : ∀ (J : Finset _) x, TrivOutside {s.v} x → ∀ f ∈ ⨆ j ∈ J, N j, NG.rt L n x f ∈ ⨆ j ∈ J, N j := by
    intro J x hx f hf
    have : (⨆ j ∈ J, N j) ≤ (⨆ j ∈ J, N j).comap (NG.rt L n x) := by
      refine iSup₂_le fun j hj => ?_
      intro f hf
      exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj (hNst j x hx f hf))
    exact this hf
  have hdich : ∀ y (J : Finset _), Disjoint (N y) (⨆ j ∈ J, N j) ∨ N y ≤ ⨆ j ∈ J, N j :=
    fun y J => GlobalTheory.T.splitTrivialTranslate_localComponent_disjoint_or_le L n s τ i T hT hTeq y.1 y.2 _ (hsupst J)
  have hφ : φ ∈ ⨆ y, N y := hspan ▸ hφS
  obtain ⟨F, hF⟩ := Submodule.mem_iSup_iff_exists_finset.1 hφ
  obtain ⟨J, -, hJsup, hJuniq⟩ := GlobalTheory.T.exists_independent_subfamily_same_iSup _ _ N hdich F
  rw [← hJsup] at hF
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum N φ).1 hF
  choose c hc using fun y => (μ y).2
  have hφsum : φ = ∑ y ∈ J, NG.rt L n y.1 (T (c y)) := by
    rw [← hμ]; exact Finset.sum_congr rfl fun y _ => (hc y).symm
  have hinj : ∀ (y : {y : GAf L n // TrivOutside {s.v}ᶜ y}), Function.Injective (fun b => NG.rt L n y.1 (T b)) := by
    intro y b b' h
    apply hT
    have := congrArg (NG.rt L n y.1⁻¹) h
    simpa [rt_rt', rt_one'] using this
  have hfix : ∀ y ∈ J, c y ∈ GlobalTheory.GLp.fixK1 ρ' := by
    intro y hy
    simp only [GlobalTheory.GLp.fixK1, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    intro kk
    obtain ⟨x, ⟨hx1, hx2⟩, -⟩ := hI.2.2 (Matrix.GeneralLinearGroup.map θ.symm.toRingHom (GlobalTheory.GLp.inc g n kk))
    have hlift : IsLift s x (1 : GL (Fin n) (ZMod g)) :=
      ⟨hx1, fun p q => by
        have H := GlobalTheory.T.principalCongruence_map_completion_sub_one_valued_lt _ s.v g n θ (fun z => (hθ z).2) (kk : GL (Fin n) ℤ_[g]) kk.2 p q
        rw [hx2]
        exact H⟩
    have hx := hφfix x hlift
    have hθx : Matrix.GeneralLinearGroup.map θ.toRingHom (s.loc n x) = GlobalTheory.GLp.inc g n kk := by
      rw [hx2]; ext; simp
    rw [hφsum, map_sum] at hx
    have hx' : ∑ y ∈ J, NG.rt L n y.1 (T (ρ' (GlobalTheory.GLp.inc g n kk) (c y))) = ∑ y ∈ J, NG.rt L n y.1 (T (c y)) := by
      rw [← hx]; refine Finset.sum_congr rfl fun y _ => ?_
      rw [← hθx, ← hτθ, hTeq x hx1, rt_rt', rt_rt', (hI.2.1 x y.1 hx1 y.2).eq]
    exact hinj y (hJuniq _ _ (fun y _ => ⟨_, rfl⟩) (fun y _ => ⟨_, rfl⟩) hx' y hy)
  have hfix' : ∀ y ∈ J, ∀ kk ∈ (GlobalTheory.GLp.red g n).ker, ρ' (GlobalTheory.GLp.inc g n kk) (c y) = c y := by
    intro y hy kk hkk
    have := hfix y hy
    simp only [GlobalTheory.GLp.fixK1, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero] at this
    exact this ⟨kk, hkk⟩
  have hℓ' : ∀ γ, ∃ kk ∈ (GlobalTheory.GLp.red g n).ker,
      Matrix.GeneralLinearGroup.map θ.toRingHom (s.loc n (ℓ γ)) = GlobalTheory.GLp.lift g n γ * GlobalTheory.GLp.inc g n kk :=
    fun γ => GlobalTheory.T.exists_padic_lift_mul_principalCongruence_of_reduction _ s.v g n θ (fun z => (hθ z).1) _ γ (hℓ γ).2
  choose kk hkk hkkeq using hℓ'
  have hterm : ∀ γ, NG.rt L n (ℓ γ) φ = ∑ y ∈ J, NG.rt L n y.1 (T (ρ' (GlobalTheory.GLp.lift g n γ) (c y))) := by
    intro γ
    rw [hφsum, map_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [rt_rt', (hI.2.1 (ℓ γ) y.1 (hℓ γ).1 y.2).eq, ← rt_rt', ← hTeq _ (hℓ γ).1, hτθ, hkkeq, map_mul,
      Module.End.mul_apply, hfix' y hy _ (hkk γ)]
  rw [finsum_eq_sum_of_fintype]
  calc ∑ γ, a.coeff γ • NG.rt L n (ℓ γ) φ = ∑ y ∈ J, NG.rt L n y.1 (T (GlobalTheory.GLp.actK ρ' a (c y))) := by
        simp only [hterm, Finset.smul_sum, GlobalTheory.GLp.actK, LinearMap.sum_apply,
          LinearMap.smul_apply, map_sum, map_smul]
        exact Finset.sum_comm
    _ = φ := by
        rw [hφsum]
        exact Finset.sum_congr rfl fun y hy => by rw [ha _ (hfix y hy)]

theorem serFix_of_locS' {L : Type} [Field L] [NumberField L] [IsCMField L] {n g : ℕ} [Fact g.Prime]
    (π : NG.FinTyp L n) (s : SplitPlace L) {w : HeightOneSpectrum (𝓞 L)} (h : s.w = w)
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion L)))
    (j : ℚ_[g] ≃+* w.adicCompletion L) (hj : Continuous j) (a : MonoidAlgebra ℂ (GL (Fin n) (ZMod g)))
    (hloc : GlobalTheory.HeightCounting.IsLocS π.S s (h ▸ τ))
    (ha : ∀ y ∈ GlobalTheory.GLp.fixK1 (τ.ρ.comp (Matrix.GeneralLinearGroup.map j.toRingHom)),
      GlobalTheory.GLp.actK (τ.ρ.comp (Matrix.GeneralLinearGroup.map j.toRingHom)) a y = y) :
    SerFix π s a := by
  subst h
  exact serFix_of_locS π s τ j hj a hloc ha

theorem serFix_of_comp : ∀ (D : D7) (I : Ident D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (cp : GlobalTheory.GoodTypes.Comp D), IsComp I rep cp → ∀ σ k v (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))), (∀ y ∈ fixK1 (cp σ k v).ρ, actK (cp σ k v).ρ a y = y) → ∀ s : SplitPlace D.host.E, s.w = D.naut.plGw k v → GlobalTheory.LabPin.SerFix (rep σ) s a := by
  intro D I rep cp hc σ k v a ha s hs
  obtain ⟨s₀, h₀, τ, hloc, hcp⟩ := hc σ k v
  obtain rfl : s = s₀ := GlobalTheory.T.cmSplitPlace_eq_of_prime_eq _ s s₀ (hs.trans h₀.symm)
  rw [hcp] at ha
  exact serFix_of_locS' (rep σ) s h₀ τ (I.i k v) (I.cont k v) a hloc ha

end GlobalTheory.DepthZeroSer

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthZeroIdentity_finiteType_of_typePrimeComponent : ∀ (D : D7) (I : Ident D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (cp : GlobalTheory.GoodTypes.Comp D), IsComp I rep cp → ∀ σ k v (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))), (∀ y ∈ fixK1 (cp σ k v).ρ, actK (cp σ k v).ρ a y = y) → ∀ s : SplitPlace D.host.E, s.w = D.naut.plGw k v → GlobalTheory.LabPin.SerFix (rep σ) s a := by
  atlas_forward_decl GlobalTheory.DepthZeroSer.serFix_of_comp
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM

namespace GlobalTheory.LabPin
open GlobalTheory.TypeRec
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem principalCongruence_fixed_vector_rational_local_field {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)))
    (h : GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin n)) ≠ ⊥) :
    fixK1 (pull I k v τ).ρ ≠ ⊥ := by
  have hw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hle : ∀ t : ℚ_[D.host.g k], ‖t‖ ≤ 1 → ‖I.i k v t‖ ≤ 1 := fun t ht =>
    GlobalTheory.TypeRec.Model.emb_le (D.naut.plGw k v) (D.host.g k) (I.i k v).toRingHom (I.cont k v) t ht
  have hlt : ∀ t : ℚ_[D.host.g k], ‖t‖ < 1 → ‖I.i k v t‖ < 1 := by
    intro t ht
    have hp := (Fact.out : (D.host.g k).Prime)
    have h2 : ‖t‖ ≤ ((D.host.g k : ℕ) : ℝ) ^ (-1 : ℤ) :=
      (Padic.norm_le_pow_iff_norm_lt_pow_add_one t (-1)).2 (by simpa using ht)
    have hp0 : ((D.host.g k : ℕ) : ℚ_[D.host.g k]) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have h3 : ‖t / ((D.host.g k : ℕ) : ℚ_[D.host.g k])‖ ≤ 1 := by
      rw [norm_div, Padic.norm_p, div_le_one₀ (by have := hp.one_lt; positivity)]
      simpa using h2
    have e : I.i k v t = ((D.host.g k : ℕ) : (D.naut.plGw k v).adicCompletion D.host.E) *
        I.i k v (t / ((D.host.g k : ℕ) : ℚ_[D.host.g k])) := by
      rw [← map_natCast (I.i k v) (D.host.g k), ← map_mul, mul_div_cancel₀ _ hp0]
    rw [e, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (hle _ h3))
      (Formalism.BasicNotions.Examples₂.LocF.norm_l_lt (D.naut.plGw k v) (D.host.g k) hw)
  have hint : ∀ (q : GL (Fin n) ℤ_[D.host.g k]) a b,
      (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom (GlobalTheory.GLp.inc (D.host.g k) n q)).1 a b ∈
        (D.naut.plGw k v).adicCompletionIntegers D.host.E := by
    intro q a b
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
      (Valued.toNormedField.norm_le_one_iff.1 (hle _ (PadicInt.norm_le_one (q.1 a b))))
  have hone : ∀ a b : Fin n, (1 : Matrix (Fin n) (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)) a b =
      I.i k v (((1 : Matrix (Fin n) (Fin n) ℤ_[D.host.g k]) a b : ℤ_[D.host.g k]) : ℚ_[D.host.g k]) := by
    intro a b
    by_cases h' : a = b
    · subst h'; simp
    · simp [Matrix.one_apply_ne h']
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨y, (Submodule.mem_iInf _).2 fun z => ?_, hy0⟩
  have hu : Matrix.GeneralLinearGroup.map (I.i k v).toRingHom (GlobalTheory.GLp.inc (D.host.g k) n z) ∈
      GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin n) := by
    rw [← (GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne (D.naut.plGw k v) n).2, GlobalTheory.AdelicU.mem_princ_iff,
      GlobalTheory.AdelicU.mem_GLint_iff]
    refine ⟨⟨fun a b => hint _ a b, fun a b => ?_⟩, fun a b => ?_⟩
    · rw [← map_inv, ← map_inv]
      exact hint _ a b
    · have hz : GlobalTheory.GLp.red (D.host.g k) n z = 1 := z.2
      have hab : PadicInt.toZMod ((z : GL (Fin n) ℤ_[D.host.g k]).1 a b) =
          (1 : Matrix (Fin n) (Fin n) (ZMod (D.host.g k))) a b :=
        congrArg (fun m : GL (Fin n) (ZMod (D.host.g k)) => m.1 a b) hz
      have h4 : (z : GL (Fin n) ℤ_[D.host.g k]).1 a b - (1 : Matrix (Fin n) (Fin n) ℤ_[D.host.g k]) a b ∈
          RingHom.ker (PadicInt.toZMod (p := D.host.g k)) := by
        rw [RingHom.mem_ker, map_sub, hab]
        by_cases h' : a = b
        · subst h'; simp
        · simp [Matrix.one_apply_ne h']
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at h4
      have h5 := hlt _ h4
      apply Valued.toNormedField.norm_lt_one_iff.1
      rw [Matrix.sub_apply, hone a b]
      convert h5 using 2
      rw [PadicInt.coe_sub, map_sub]
      rfl
  change τ.ρ (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom (GlobalTheory.GLp.inc (D.host.g k) n z)) y - y = 0
  rw [sub_eq_zero]
  exact GlobalTheory.Parabolic.mem_fixed.1 hy _ hu

theorem principalCongruenceFixedVectors_ne_bot_of_iso {g : ℕ} [Fact g.Prime] {n : ℕ} {π π' : QRep g n} (e : π ≅ π') (h : fixK1 π'.ρ ≠ ⊥) :
    fixK1 π.ρ ≠ ⊥ := by
  intro hb
  apply h
  rw [Submodule.eq_bot_iff] at hb ⊢
  intro x hx
  have hy : (e.inv.hom x) ∈ fixK1 π.ρ := by
    simp only [fixK1, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
    intro q
    rw [← Rep.hom_comm_apply, hx q]
  have h0 := hb _ hy
  have : e.hom.hom (e.inv.hom x) = x := by simp
  rw [← this, h0, map_zero]

end GlobalTheory.LabPin

namespace GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem typeLab_of_local : Green → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : GlobalTheory.HeightCounting.RowSide D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (L : ∀ k, LabelDatum (D.host.g k)), GlobalTheory.HeightCounting.LabTrue D T → GlobalTheory.HeightCounting.RowTrue hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR → GlobalTheory.HeightCounting.RowDepth D rep → GlobalTheory.SerSys.LabTie D L → (∀ k v, ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k), TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen) → GlobalTheory.LabPin.TypeLab D rep := by
  intro hG hZ hDZ hL D T Rw rep L hLab hRow hDep hLT hTame
  obtain ⟨I⟩ := GlobalTheory.T.nonempty_typePlaceCompletionIdent D
  obtain ⟨rc, hrc, hcls⟩ := GlobalTheory.T.exists_class_map_correspondence hL D T I
  obtain ⟨cp, hcomp, hcp⟩ := GlobalTheory.T.exists_type_components hL D T I rc hrc Rw rep hRow hDep
  have hP : LabParam D L rc := GlobalTheory.SerSys.Bridge.labParam_of D L rc hG (GlobalTheory.T.tame_support_compatible hZ hL D T I rc hrc)
    (fun k => GlobalTheory.T.depthZeroSupercuspidal_cuspidalModule (D.host.g k))
    (fun k v => by
      obtain ⟨κ, hκ⟩ := hTame k v
      exact GlobalTheory.T.tame_parameter_coupled hDZ hL D T I rc hrc L k v κ hκ)
  have hfix : ∀ σ k v, fixK1 (cp σ k v).ρ ≠ ⊥ := by
    intro σ k v
    obtain ⟨s, τ, hsw, hloc, hfx⟩ := hDep σ k v
    have hT := hRow.1 σ s τ hloc
    have key : ∀ (w : PlE D.host) (hw : w = D.naut.plGw k v)
        (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (w.adicCompletion D.host.E))),
        T.e w (Rw.locR σ w) = GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls τ) →
        GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (w.adicCompletion D.host.E) (Fin D.R.r)) ≠ ⊥ →
        fixK1 (cp σ k v).ρ ≠ ⊥ := by
      intro w hw τ hT hfx
      subst hw
      have h1 := hrc k v D.R.r τ (pull I k v τ) ⟨CategoryTheory.Iso.refl _⟩
      have h2 : rc k v D.R.r (pull I k v τ) = rc k v D.R.r (cp σ k v) := by
        rw [← (hcp σ k v).2]
        exact (T.e _).injective (h1.trans hT.symm)
      obtain ⟨e⟩ := (((hcls k v) D.R.r (cp σ k v) (hcp σ k v).1).2 (pull I k v τ) (GlobalTheory.TypeRec.Model.irrSm_pull I k v τ)).1 h2.symm
      exact GlobalTheory.LabPin.principalCongruenceFixedVectors_ne_bot_of_iso e (GlobalTheory.LabPin.principalCongruence_fixed_vector_rational_local_field I k v τ hfx)
    exact key s.w hsw τ hT hfx
  intro σ k v
  have hlab : D.nd.lab k σ v = D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r (cp σ k v)) := by
    rw [Rw.lab_eq, (hcp σ k v).2]
  obtain ⟨h1, h2⟩ := GlobalTheory.SerSys.inertiaCharpoly_isLabel_of_action hG hL D T I rc L hrc hLab hLT hP k v (cp σ k v) (hcp σ k v).1 (hfix σ k v)
  show IsLabel D k (D.nd.lab k σ v) ∧ ∀ s : SplitPlace D.host.E, s.w = D.naut.plGw k v → SerFix (rep σ) s (D.ntypes.eSer k (D.nd.lab k σ v))
  rw [hlab]
  exact ⟨h1, fun s hs => GlobalTheory.T.depthZeroIdentity_finiteType_of_typePrimeComponent D I rep cp hcomp σ k v _ h2 s hs⟩

end GlobalTheory.LabPin
end
