import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationTowerCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormVEqNormVUnderPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LtOneOfContinuous

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LiftTrans

open Matrix

section Places

variable {K M N : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field N] [NumberField N]
  [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N]

theorem under_under (w : HeightOneSpectrum (𝓞 N)) :
    (w.under (𝓞 M)).under (𝓞 K) = w.under (𝓞 K) := by
  apply HeightOneSpectrum.ext
  simp only [HeightOneSpectrum.under_asIdeal]
  exact Ideal.under_under w.asIdeal

theorem eq_under_of_continuous {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 N)}
    (i : v.adicCompletion K →+* w.adicCompletion N) (hi : Continuous i)
    (he : ∀ x : K, i (algebraMap K _ x) = algebraMap N _ (algebraMap K N x)) : v = w.under (𝓞 K) := by
  have h1 : v.asIdeal ≤ (w.under (𝓞 K)).asIdeal := by
    intro x hx
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, GlobalTheory.DegOneLift.mem_iff_lt_one]
    rw [GlobalTheory.DegOneLift.mem_iff_lt_one] at hx
    have := GlobalTheory.DegOneLift.lt_one_of_continuous i hi hx
    rw [he] at this
    exact this
  exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le (w.under (𝓞 K)).isPrime.ne_top h1)

end Places

end GlobalTheory.LiftTrans

open GlobalTheory.LiftTrans in

theorem GlobalTheory.LiftTrans.isLift_trans : ∀ (K M N : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Field N] [NumberField N] [IsTotallyComplex N] [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N] (a : ℕ) (π : CuspSub K a) (P : CuspSub M a) (Q : CuspSub N a), IsLift π P → IsLift P Q → IsLift π Q := by
  intro K M N _ _ _ _ _ _ _ _ _ _ _ _ _ a π P Q h1 h2
  refine ⟨?_, ?_, ?_⟩
  · intro w f B hf hB
    obtain ⟨f1, hf1⟩ := GlobalTheory.AboveL.ResDeg.normV_eq_under_pow K M (w.under (𝓞 M))
    obtain ⟨f2, hf2⟩ := GlobalTheory.AboveL.ResDeg.normV_eq_under_pow M N w
    rw [under_under] at hf1
    have hP := h1.sat (w.under (𝓞 M)) f1 B (by rw [under_under]; exact hf1) (by rw [under_under]; exact hB)
    have hQ := h2.sat w f2 _ hf2 hP
    have hff : f = f1 * f2 := by
      have h2le := GlobalTheory.DegOneLift.two_le_normV (w.under (𝓞 K))
      apply Nat.pow_right_injective h2le
      change normV (w.under (𝓞 K)) ^ f = normV (w.under (𝓞 K)) ^ (f1 * f2)
      rw [← hf, pow_mul, ← hf1, hf2]
    rw [Multiset.map_map] at hQ
    convert hQ using 2
    simp [Function.comp, hff, pow_mul]
  · intro τ
    rw [h2.inf τ, h1.inf, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  · intro v w i hi hie σ σ' hσ hσ'
    have hv := eq_under_of_continuous i.toRingHom hi hie
    subst hv
    set u := w.under (𝓞 M) with hu
    haveI : w.asIdeal.LiesOver u.asIdeal := by rw [hu, HeightOneSpectrum.under_asIdeal]; infer_instance
    haveI : u.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := by
      constructor
      rw [hu, HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal, Ideal.under_under]
    haveI : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := by rw [HeightOneSpectrum.under_asIdeal]; infer_instance
    let φ1 := GroundTheory.Global.adicCompletionMap (w.under (𝓞 K)) u
    let φ2 := GroundTheory.Global.adicCompletionMap u w
    have hcomp : ∀ y, φ2 (φ1 y) = GroundTheory.Global.adicCompletionMap (w.under (𝓞 K)) w y := fun y =>
      congrFun (congrArg DFunLike.coe (GlobalTheory.BCChar.adicCompletionMap_comp_adicCompletionMap (w.under (𝓞 K)) u w)) y
    have hiφ : ∀ y, i y = φ2 (φ1 y) := fun y => by
      rw [hcomp]
      exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) (K := K) (w.under (𝓞 K))).equalizer hi
        (GroundTheory.Global.continuous_adicCompletionMap _ _)
        (funext fun x => (hie x).trans (GroundTheory.Global.adicCompletionMap_algebraMap _ _ x).symm)) y
    have hb2 : Function.Bijective φ2 := ⟨φ2.injective, fun z => by
      obtain ⟨y, rfl⟩ := i.surjective z
      exact ⟨φ1 y, (hiφ y).symm⟩⟩
    have hb1 : Function.Bijective φ1 := ⟨φ1.injective, fun t => by
      obtain ⟨y, hy⟩ := i.surjective (φ2 t)
      exact ⟨y, hb2.1 (by rw [← hiφ, hy])⟩⟩
    obtain ⟨τ, hτ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL M a P u
    obtain ⟨e1, he1⟩ := h1.loc (w.under (𝓞 K)) u (RingEquiv.ofBijective φ1 hb1)
      (GroundTheory.Global.continuous_adicCompletionMap _ _) (fun x => GroundTheory.Global.adicCompletionMap_algebraMap _ _ x) σ τ hσ hτ
    obtain ⟨e2, he2⟩ := h2.loc u w (RingEquiv.ofBijective φ2 hb2)
      (GroundTheory.Global.continuous_adicCompletionMap _ _) (fun x => GroundTheory.Global.adicCompletionMap_algebraMap _ _ x) τ σ' hτ hσ'
    refine ⟨e1.trans e2, fun g x => ?_⟩
    have hg : Matrix.GeneralLinearGroup.map (RingEquiv.ofBijective φ2 hb2).toRingHom
        (Matrix.GeneralLinearGroup.map (RingEquiv.ofBijective φ1 hb1).toRingHom g) =
        Matrix.GeneralLinearGroup.map i.toRingHom g := by
      apply Units.ext
      ext j k
      simp only [Matrix.GeneralLinearGroup.map_apply]
      exact congrArg _ (hiφ _).symm
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, he1, he2, hg]
end
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_baseChange_trans_tower : ∀ (K M N : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Field N] [NumberField N] [IsTotallyComplex N] [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N] (a : ℕ) (π : CuspSub K a) (P : CuspSub M a) (Q : CuspSub N a), IsLift π P → IsLift P Q → IsLift π Q := by
  first | (exact @GlobalTheory.LiftTrans.isLift_trans) | (exact GlobalTheory.LiftTrans.isLift_trans) | (intros; apply GlobalTheory.LiftTrans.isLift_trans  <;> assumption)
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem chars_congr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    {ξ ξ' : Fin n → (kˣ →* ℂˣ)} (hξ : ∀ j, IsSmoothChar (ξ j)) (hξ' : ∀ j, IsSmoothChar (ξ' j)) (e : ξ = ξ') :
    chars ξ hξ = chars ξ' hξ' := by
  subst e; rfl

theorem charLift_trans : ∀ (K M N : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Field N] [NumberField N] [IsTotallyComplex N] [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N] (a : ℕ) (π : CuspSub K a) (P : CuspSub M a) (Q : CuspSub N a), CharLift π P → CharLift P Q → CharLift π Q := by
  intro K M N _ _ _ _ _ _ _ _ _ _ _ _ _ a π P Q h1 h2
  refine ⟨GlobalTheory.T.cuspidal_baseChange_trans_tower K M N a π P Q h1.1 h2.1, ?_⟩
  intro v w _ τ T hτ hT ξ hξ hs
  let u : HeightOneSpectrum (𝓞 M) := w.under (𝓞 M)
  haveI hwu : w.asIdeal.LiesOver u.asIdeal := ⟨rfl⟩
  haveI huv : u.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.tower_bot w.asIdeal u.asIdeal v.asIdeal
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL M a P u
  have h3 := h1.2 v u τ σ hτ hσ ξ hξ hs
  have h4 := h2.2 u w σ T hσ hT _ _ h3
  have e := GlobalTheory.BCChar.normU_comp_normU v u w
  refine (congrArg (HasSupport T.ρ) (chars_congr _ _ ?_)).mp h4
  funext j
  rw [MonoidHom.comp_assoc, e]

end GlobalTheory.RoadU
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspRep_characterSupportLift_trans_tower : ∀ (K M N : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Field N] [NumberField N] [IsTotallyComplex N] [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N] (a : ℕ) (π : CuspSub K a) (P : CuspSub M a) (Q : CuspSub N a), CharLift π P → CharLift P Q → CharLift π Q := by
  first | (exact @GlobalTheory.RoadU.charLift_trans) | (exact GlobalTheory.RoadU.charLift_trans) | (intros; apply GlobalTheory.RoadU.charLift_trans  <;> assumption)
end
