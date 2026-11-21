import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricCuspidalMultiplicityOneOfTwisted
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricDiscreteSelfDualMultOneOfIsobaricSumMult
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharEqOfSplitOfTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuIntOfCharTied
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalInvariantsMatchSemisimple
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowFinrankEqZeroOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularDefinite
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyFactorizationSemisimple
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixCharpolySmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Adm2OfHyp
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowLeSpan
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContMapRepIotaOQ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamGaloisSideIffDeRhamAtLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterIndependentOfLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodLabelsRankPartParameterCuspidal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricRigidOfPin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TieAutAndSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisCompatibilityOfJumpsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsBisTer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd

section
namespace GlobalTheory.RowClose

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

open Polynomial NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.RowClose.heckeSplitOne_of_charTied : ∀ (D : _root_.Formalism.BasicNotions.D7) (C : _root_.Formalism.L2.Host.CharFrame D)
    (nch : _root_.Formalism.BasicNotions.NChoice D) (Tp : _root_.Formalism.L2.Host.TupTied D C nch), _root_.Formalism.L2.Host.NCharTied D C nch Tp →
    _root_.GlobalTheory.RowCopy.HeckeSplitOne D := by
  intro D C nch Tp T
  have h := _root_.GlobalTheory.HeckeSplitRow.heckeSplitOne_of_tie D.nd D.naut
    (_root_.GlobalTheory.HeckeSplitRow.heckeCharTie_of_tied T)
  unfold _root_.GlobalTheory.ThetaExh.HeckeSplitOne at h
  exact h

end GlobalTheory.RowClose
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_invariants_match_semisimple : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → Formalism.MainNotions.SumRepresentations.adm2 D → Formalism.MainNotions.SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (a : ℕ), 1 ≤ a → ∀ (π : D.naut.CG a) (s : ℝ), D.naut.csd (D.naut.tw π D.naut.etaT) → D.naut.ralg (D.naut.tw π D.naut.etaT) → (∃ m : ℤ, s = (m : ℝ) + 1 / 2) → ∀ ρ : G D.host.E D.nd.Om →* GL (Fin a) (D.nd.O i), GlobalTheory.LocalInv.Cont D.nd i ρ → IsSSRep (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) ρ) → GlobalTheory.LocalInv.Matches D.nd D.naut i ρ π (s + (1 - (a : ℝ)) / 2) → ∀ w, GlobalTheory.LocalInv.wd D.nd D.naut i ρ w = D.naut.lpTw (D.naut.locG π w) (s + (1 - (a : ℝ)) / 2) ∧ (w ∈ placesOver D.host.E (D.nd.l i) → GlobalTheory.LocalInv.DeRham D.nd D.naut i ρ w) := by
  first | exact @GlobalTheory.TwistLG.localGlobal_twist | exact GlobalTheory.TwistLG.localGlobal_twist | (intros; apply GlobalTheory.TwistLG.localGlobal_twist <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_factorization_semisimple : ∀ (D : D7), Formalism.MainNotions.SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (r : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)), IsHeckeGalois D.nd i x r → ∀ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i), IsSSRep (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) ρ) → (∀ g, ((r g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).charpoly = ((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly * ∏ c ∈ Finset.Icc 1 D.R.t, (X - C ((D.nd.chi i c g : (D.nd.O i)ˣ) : D.nd.O i))) → GlobalTheory.LocalInv.Cont D.nd i ρ := by
  first | exact @GlobalTheory.SSComplement.cont | exact GlobalTheory.SSComplement.cont | (intros; apply GlobalTheory.SSComplement.cont <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.Ggeo.WpKInv

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

def toPi (i : N.Loc) :
    TensorProduct (N.O i) (Fin R.r → N.O i) (FractionRing (N.O i)) ≃ₗ[N.O i] (Fin R.r → Kf N i) :=
  (TensorProduct.comm (N.O i) _ _).trans
    (TensorProduct.piScalarRight (N.O i) (N.O i) (FractionRing (N.O i)) (Fin R.r))

theorem toPi_tmul (i : N.Loc) (v : Fin R.r → N.O i) (k : FractionRing (N.O i)) :
    toPi N i (v ⊗ₜ k) = fun j => algebraMap (N.O i) (Kf N i) (v j) * k := by
  funext j
  simp [toPi, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul, Algebra.smul_def]

theorem Wp_apply (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (g : G H.E N.Om)
    (v : Fin R.r → N.O i) :
    Glob.Wp N i ρ g v = ((((N.chi i 1 g)⁻¹ : (N.O i)ˣ) : N.O i) •
      ((ρ g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i))).mulVec v := by
  rw [Matrix.smul_mulVec]
  rfl

theorem toPi_WpK (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (g : G H.E N.Om)
    (t : TensorProduct (N.O i) (Fin R.r → N.O i) (FractionRing (N.O i))) :
    toPi N i (Glob.WpK N i ρ g t) = (GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matW N i ρ g).mulVec (toPi N i t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, Matrix.mulVec_add]
  | tmul v k =>
    have h1 : Glob.WpK N i ρ g (v ⊗ₜ k) = (Glob.Wp N i ρ g v) ⊗ₜ k := by
      simp [Glob.WpK, coefRep, Representation.tprod_apply]
    rw [h1, toPi_tmul, toPi_tmul, Wp_apply]
    have h2 : (fun j => algebraMap (N.O i) (Kf N i) (v j) * k) =
        k • (algebraMap (N.O i) (Kf N i) ∘ v) := by
      funext j; simp [mul_comm]
    rw [h2, Matrix.mulVec_smul]
    funext j
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matW, ← RingHom.map_mulVec]

theorem H0_weight_part_eq_bot :
    ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (i : N.Loc)
      (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (Dg : Subgroup (G H.E N.Om)),
      GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.NoInv Dg (GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matW N i ρ) →
        H0 ((Formalism.MainNotions.N.Glob.WpK N i ρ).comp Dg.subtype) = ⊥ := by
  intro R H what₂ N i ρ Dg h
  rw [eq_bot_iff]
  intro t ht
  rw [Submodule.mem_bot]
  have ht' : ∀ g ∈ Dg, Glob.WpK N i ρ g t = t := fun g hg =>
    (Representation.mem_invariants _ t).1 ht ⟨g, hg⟩
  have h0 : toPi N i t = 0 := h _ fun g hg => by rw [← toPi_WpK, ht' g hg]
  exact (toPi N i).map_eq_zero_iff.1 h0

end GlobalTheory.Ggeo.WpKInv
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H0_weight_part_no_invariants : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (Dg : Subgroup (G H.E N.Om)), GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.NoInv Dg (GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matW N i ρ) → H0 ((Formalism.MainNotions.N.Glob.WpK N i ρ).comp Dg.subtype) = ⊥ := by
  atlas_forward_decl GlobalTheory.Ggeo.WpKInv.H0_weight_part_eq_bot
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.TateDualCoef

open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts TensorProduct

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)

def coordEquiv :
    TensorProduct (N.O i) (Module.Dual (N.O i) (Fin R.r → N.O i)) (Kf N i) ≃ₗ[N.O i] (Fin R.r → Kf N i) :=
  (TensorProduct.congr (Pi.basisFun (N.O i) (Fin R.r)).dualBasis.equivFun (LinearEquiv.refl _ _)) ≪≫ₗ
    TensorProduct.comm (N.O i) (Fin R.r → N.O i) (Kf N i) ≪≫ₗ
      TensorProduct.piScalarRight (N.O i) (N.O i) (Kf N i) (Fin R.r)

theorem coordEquiv_tmul (f : Module.Dual (N.O i) (Fin R.r → N.O i)) (c : Kf N i) :
    coordEquiv N i (f ⊗ₜ c) = fun a => f (Pi.single a 1) • c := by
  ext a
  simp [coordEquiv, TensorProduct.piScalarRight_apply]

theorem tate_dual_single_basis (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (g : G H.E N.Om)
    (f : Module.Dual (N.O i) (Fin R.r → N.O i)) (a : Fin R.r) :
    (Glob.T2 N i ρ g f) (Pi.single a 1) =
      ∑ b, ((Glob.epsO N i g : (N.O i)ˣ) : N.O i) * ((((N.chi i 1 g⁻¹)⁻¹ : (N.O i)ˣ) : N.O i) *
        ((ρ g⁻¹ : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i)) b a) * f (Pi.single b 1) := by
  have hv : ∀ v : Fin R.r → N.O i, f v = ∑ b, v b * f (Pi.single b 1) := fun v => by
    conv_lhs => rw [pi_eq_sum_univ v]
    simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  simp only [Glob.T2, Glob.Wp, twistRep, glRep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply,
    Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, MonoidHom.inv_apply]
  rw [map_smul, hv]
  simp only [smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [Matrix.toLin'_apply, Pi.smul_apply, mul_assoc]

theorem coordEquiv_equivariant (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (g : G H.E N.Om)
    (x : TensorProduct (N.O i) (Module.Dual (N.O i) (Fin R.r → N.O i)) (Kf N i)) :
    coordEquiv N i (coefRep (Glob.T2 N i ρ) (Kf N i) g x) = (matT N i ρ g).mulVec (coordEquiv N i x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, Matrix.mulVec_add]
  | tmul f c =>
    have e1 : coefRep (Glob.T2 N i ρ) (Kf N i) g (f ⊗ₜ c) = (Glob.T2 N i ρ g f) ⊗ₜ c := rfl
    rw [e1, coordEquiv_tmul, coordEquiv_tmul]
    funext a
    rw [tate_dual_single_basis]
    simp only [Matrix.mulVec, dotProduct, matT, matW, Matrix.smul_apply, Matrix.transpose_apply,
      Matrix.map_apply, smul_eq_mul]
    simp only [Algebra.smul_def, map_sum, map_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [eps, Glob.epsO]
    ring

theorem H0_coefRep_T2_comp_subtype_eq_bot_of_noInv : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (Dg : Subgroup (G H.E N.Om)), GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.NoInv Dg (GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matT N i ρ) → H0 ((Formalism.MainNotions.N.coefRep (Formalism.MainNotions.N.Glob.T2 N i ρ) (Kf N i)).comp Dg.subtype) = ⊥ := by
  intro R H what₂ N i ρ Dg h
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  have hfix : ∀ g ∈ Dg, (matT N i ρ g).mulVec (coordEquiv N i x) = coordEquiv N i x := by
    intro g hg
    rw [← coordEquiv_equivariant]
    congr 1
    exact (Representation.mem_invariants _ x).1 hx ⟨g, hg⟩
  have h0 := h _ hfix
  exact (coordEquiv N i).injective (by rw [h0, map_zero])

end GlobalTheory.TateDualCoef
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H0_coefRep_T2_subtype_eq_bot_of_noInv_matT : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (Dg : Subgroup (G H.E N.Om)), GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.NoInv Dg (GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matT N i ρ) → H0 ((Formalism.MainNotions.N.coefRep (Formalism.MainNotions.N.Glob.T2 N i ρ) (Kf N i)).comp Dg.subtype) = ⊥ := by
  atlas_forward_decl GlobalTheory.TateDualCoef.H0_coefRep_T2_comp_subtype_eq_bot_of_noInv
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.LocalInvEta

open GlobalTheory.LocalInv GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts Matrix

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def LocalGlobalEta : Prop := ∀ (i : N.Loc) (a : ℕ), 1 ≤ a → ∀ (π : A.CG a) (s : ℝ),
  A.csd (A.tw π A.etaT) → A.ralg (A.tw π A.etaT) → (∃ m : ℤ, s = (m : ℝ) + 1 / 2) →
  ∀ ρ : G H.E N.Om →* GL (Fin a) (N.O i), Cont N i ρ →
    IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) ρ) → Matches N A i ρ π (s + (1 - (a : ℝ)) / 2) →
    ∀ w, wd N A i ρ w = A.lpTw (A.locG π w) (s + (1 - (a : ℝ)) / 2) ∧
      (w ∈ placesOver H.E (N.l i) → DeRham N A i ρ w)

theorem not_subOrQuot (eig : Eig N A) (hT : GlobalTheory.IndefiniteRowSideFullHecke.TemperedRepresentations.Tempered N A) (hLG : LocalGlobalEta N A)
    (hL : EigLaws N A eig) (hA : EigAway N A eig) (hAb : EigAbove N A eig) (hS : TemperedSizes N A eig)
    (hη : EtaType N A) (hW : WeightRegular N A) (i : N.Loc) (x : N.X i) (π : A.CG R.r)
    (hx : HasParamX N A i x [⟨R.r, π, 1⟩]) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i))
    (hρ : IsRankPart N i x ρ) (w : PlE H) (j : ℕ) :
    ¬ SubOrQuot N i ρ (N.chi i 1 * eps N i ^ j) w := by
  intro hs
  obtain ⟨P, hP, hB⟩ := hx
  obtain ⟨σ, hσ⟩ : ∃ σ, FrobLift N w σ := exists_isFrob (N.plOm.2 w)
  obtain ⟨r, hr⟩ := r_odd R
  obtain ⟨t, ht⟩ := R.t_odd
  have hrt := r_add_le R
  have a1 := part_alg N A hη hW i P _ hB ⟨R.r, A.tw π A.etaTinv, 1⟩ (by simp [twistIso]) (r_odd R) odd_one
  have a2 := part_alg N A hη hW i P _ hB ⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩ (by simp [twistIso, muPart])
    odd_one R.t_odd
  have x1 : (1 - (R.nV : ℝ)) / 2 = -(R.t : ℝ) / 2 + (1 - (R.r : ℝ)) / 2 := by
    rw [Ranks.nV]; push_cast; ring
  have l1 := hLG i R.r (r_odd R).pos (A.tw π A.etaTinv) (-(R.t : ℝ) / 2) a1.1 a1.2
    ⟨-(t : ℤ) - 1, by rw [ht]; push_cast; ring⟩
    ρ hρ.1 hρ.2.1 (x1 ▸ matches_rho N A i x π P hP hB ρ hρ) w
  have hc : Cont N i (charRep N i (N.chi i 1 * eps N i ^ j)) := by
    refine charRep_cont N i _ ?_
    refine ((N.chi_cont i 1).mul ((eps_cont N i).pow j)).congr fun g => ?_
    simp
  have x2 : ((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + j =
      (-(R.r : ℝ) / 2 + j) + (1 - ((1 : ℕ) : ℝ)) / 2 := by
    rw [Ranks.nV]; push_cast; ring
  have l2 := hLG i 1 le_rfl (A.tw (A.muC i) A.etaTinv) (-(R.r : ℝ) / 2 + j) a2.1 a2.2
    ⟨(j : ℤ) - r - 1, by rw [hr]; push_cast; ring⟩
    _ hc (charRep_ss N i _) (x2 ▸ matches_chi N A i j) w
  obtain ⟨c1, c2, c3⟩ := hL w σ hσ
  obtain ⟨m, hm⟩ := Multiset.card_eq_one.mp
    ((c1 (A.locG (A.tw (A.muC i) A.etaTinv) w)).trans (A.locG_dim _ w))
  obtain ⟨c, hcc⟩ := Multiset.card_eq_one.mp ((c1 (A.locG A.etaT w)).trans (A.locG_dim _ w))
  have hmem := eig_mem N A eig hA hAb i ρ _ hρ.1 hc w l1.2 l2.2 hs σ hσ _
    (by rw [l2.1, c2, hm, Multiset.map_singleton])
  rw [l1.1, c2] at hmem
  obtain ⟨α, hα, he⟩ := Multiset.mem_map.mp hmem
  have s1 := (hS w σ hσ _ (hT _ (r_odd R).pos _ a1.1 a1.2 w) (α * c) (by
    rw [A.locG_tw, c3 _ _ c (A.locG_dim _ w) hcc]
    exact Multiset.mem_map_of_mem _ hα)).2
  have s2 := (hS w σ hσ _ (hT _ le_rfl _ a2.1 a2.2 w) (m * c) (by
    rw [A.locG_tw, c3 _ _ c (A.locG_dim _ w) hcc, hm]
    simp)).1
  rw [A.locG_dim] at s1 s2
  have hq := one_lt_normV w
  have hq0 : (0 : ℝ) < ((normV w : ℕ) : ℝ) := lt_trans one_pos hq
  have s2' : 1 ≤ ‖m * c‖ := by simpa using s2
  have hn : ‖α * c‖ * ((normV w : ℕ) : ℝ) ^ (-(R.t : ℝ) / 2 + (1 - (R.r : ℝ)) / 2) =
      ‖m * c‖ * ((normV w : ℕ) : ℝ) ^ ((-(R.r : ℝ) / 2 + j) + (1 - ((1 : ℕ) : ℝ)) / 2) := by
    rw [← norm_cpow w, ← norm_cpow w, ← norm_mul, ← norm_mul]
    congr 1
    linear_combination c * he
  have hle : ((normV w : ℕ) : ℝ) ^ ((-(R.r : ℝ) / 2 + j) + (1 - ((1 : ℕ) : ℝ)) / 2) ≤
      ((normV w : ℕ) : ℝ) ^ (((R.r : ℝ) - 1) / 2 + (-(R.t : ℝ) / 2 + (1 - (R.r : ℝ)) / 2)) := by
    rw [Real.rpow_add hq0 (((R.r : ℝ) - 1) / 2)]
    calc _ ≤ ‖m * c‖ * ((normV w : ℕ) : ℝ) ^ ((-(R.r : ℝ) / 2 + j) + (1 - ((1 : ℕ) : ℝ)) / 2) :=
          le_mul_of_one_le_left (Real.rpow_nonneg hq0.le _) s2'
      _ = _ := hn.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right s1 (Real.rpow_nonneg hq0.le _)
  rw [Real.rpow_le_rpow_left_iff hq] at hle
  have h1 : (R.r : ℝ) + 5 ≤ R.t := by exact_mod_cast hrt
  have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  push_cast at hle
  linarith

theorem noLocalInv_cusp (eig : Eig N A) (hT : GlobalTheory.IndefiniteRowSideFullHecke.TemperedRepresentations.Tempered N A) (hLG : LocalGlobalEta N A)
    (hL : EigLaws N A eig) (hA : EigAway N A eig) (hAb : EigAbove N A eig) (hS : TemperedSizes N A eig)
    (hη : EtaType N A) (hW : WeightRegular N A) (i : N.Loc) (x : N.X i) (hx : IsCuspPoint N A i x)
    (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (hρ : IsRankPart N i x ρ) : NoLocalInv N i ρ := by
  obtain ⟨-, Sig, hx, π, rfl⟩ := hx
  intro w
  have key := not_subOrQuot N A eig hT hLG hL hA hAb hS hη hW i x π hx ρ hρ w
  constructor
  · intro v hv
    by_contra h0
    refine key 0 ⟨v, h0, Or.inl fun g hg => ?_⟩
    rw [matK_eq, Matrix.smul_mulVec, hv g hg]
    simp
  · intro v hv
    by_contra h0
    refine key 1 ⟨v, h0, Or.inr fun g hg => ?_⟩
    have h1 : Matrix.vecMul v (matT N i ρ g)ᵀ = v := by
      rw [Matrix.vecMul_transpose]; exact hv g hg
    have h2 : Matrix.vecMul v (matW N i ρ g) =
        algebraMap (N.O i) (Kf N i) ((eps N i g : (N.O i)ˣ) : N.O i) • v := by
      conv_lhs => rw [← h1]
      rw [Matrix.vecMul_vecMul, matT_transpose_mul_matW, Matrix.vecMul_smul, Matrix.vecMul_one]
    rw [matK_eq, Matrix.vecMul_smul, h2, smul_smul]
    simp

theorem etaType_of_tie (D : D7) (h : Formalism.MainNotions.SumRepresentations.tie0 D) : EtaType D.nd D.naut := by
  obtain ⟨-, ⟨⟨h1, -⟩, h2, -⟩, -⟩ := h
  refine ⟨h1, fun τ z hz => ?_⟩
  rcases (h2 τ).1 with e | e <;> rw [e, Multiset.mem_singleton] at hz <;> subst hz
  · exact ⟨0, by simp⟩
  · exact ⟨-1, by push_cast; ring⟩

end GlobalTheory.LocalInvEta

theorem GlobalTheory.LocalInvEta.noLocalInvariants_everywhere : ∀ (D : D7) (T : WDTie D.nd D.naut), Formalism.MainNotions.SumRepresentations.tie0 D → Formalism.MainNotions.SumRepresentations.adm2 D → Formalism.MainNotions.SumRepresentations.adm5 D → Formalism.MainNotions.SumRepresentations.adm7 D → MuInt D.nd D.naut → GlobalTheory.LocalInv.GoodCuspidal D.nd D.naut → GlobalTheory.LocalInv.EigAway D.nd D.naut T.eig → GlobalTheory.LocalInv.EigAbove D.nd D.naut T.eig → Formalism.MainNotions.SumRepresentations.CuspidalGaloisUnramified D := by
  intro D T htie h2 h5 h7 _ hG hA hAb i r hr x hx ρ hss hchar w
  have hcusp : GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.IsCuspPoint D.nd D.naut i x := by
    rcases hx with ⟨hz, Sig, h1, h2⟩ | h
    · exact ⟨hz, Sig, h1, hG i x Sig h1 h2⟩
    · exact h
  have hcont := GlobalTheory.T.charpoly_factorization_semisimple D h5 i x (r x) (hr x) ρ hss hchar
  have hrank : GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.IsRankPart D.nd i x ρ :=
    ⟨hcont, hss, fun w hw B σ hB hσ => by rw [← hchar σ]; exact (hr x).2.2 w hw B σ hB hσ⟩
  have hLG : GlobalTheory.LocalInvEta.LocalGlobalEta D.nd D.naut := GlobalTheory.T.local_invariants_match_semisimple D htie h2 h5
  have hT : GlobalTheory.IndefiniteRowSideFullHecke.TemperedRepresentations.Tempered D.nd D.naut := fun a ha π hc hra => h7 a π ha hc hra
  have hno := GlobalTheory.LocalInvEta.noLocalInv_cusp D.nd D.naut T.eig hT hLG
    (GlobalTheory.RowTie.eigLaws_of_wdTie _ _ _ _ _ T) hA hAb (GlobalTheory.LocalInv.temperedSizes_of_tie _ _ _ _ _ T)
    (GlobalTheory.LocalInvEta.etaType_of_tie D htie) (GlobalTheory.LocalInv.weightRegular_definite D) i x hcusp ρ hrank w
  exact ⟨GlobalTheory.T.H0_weight_part_no_invariants _ _ _ _ i ρ _ hno.1, GlobalTheory.T.H0_coefRep_T2_subtype_eq_bot_of_noInv_matT _ _ _ _ i ρ _ hno.2⟩
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne

namespace GlobalTheory.RowTie

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

def WDOfTie (T : WDTie N A) : Prop :=
  ∀ (i : N.Loc) (a : ℕ) (r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) (w : PlE H)
    (hl : ((N.l i : ℕ) : 𝓞 H.E) ∉ w.asIdeal),
    Continuous (fun g => ((r g : GL (Fin a) (Qbar (N.l i))) :
      Matrix (Fin a) (Fin a) (Qbar (N.l i)))) →
    T.e w (A.wdOf i r w) = wdOf (N.plOm.2 w) hl (A.iotaQC i) r

theorem prod_roots_of_monic {p : ℂ[X]} (hp : p.Monic) : (p.roots.map fun α => X - C α).prod = p :=
  ((IsAlgClosed.splits p).eq_prod_roots_of_monic hp).symm

theorem eigAway_of_wdOfTie : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂)
    (A : NAut N) (T : WDTie N A), WDOfTie T → GlobalTheory.LocalInv.EigAway N A T.eig := by
  intro R H what₂ N A T hT i a ρ hρ w hw σ hσ
  have hW : σ ∈ Weil (N.plOm.2 w) := mem_Weil_of_isFrob _ hσ
  have hr : Continuous (fun g => ((mapRep (iotaOQ N A i) ρ g : GL (Fin a) (Qbar (N.l i))) :
      Matrix (Fin a) (Fin a) (Qbar (N.l i)))) :=
    Continuous.matrix_map hρ (GlobalTheory.CoeffEmbedding.continuous_iotaOQ R H what₂ N A i)
  have hcomp : iotaO N A i = (A.iotaQC i).toRingHom.comp (iotaOQ N A i) := rfl
  rw [WDTie.eig, GlobalTheory.LocalInv.wd, hT i a _ w hw hr, WD.inePol_of_mem _ hW,
    prod_roots_of_monic (WD.charPol_monic _ _), charPol_wdOf hw (A.iotaQC i) hr ⟨σ, hW⟩, hcomp,
    ← Polynomial.map_map, ← Matrix.charpoly_map]
  rfl

end GlobalTheory.RowTie
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EigConcrete

theorem wdOfTie {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (P : Pin hL D) : WDOfTie P.T := by
  intro i a r w hl _
  rw [(P.wdOf i a r w).1]
  exact P.wd.away _ _ r w hl

set_option maxHeartbeats 1000000 in

theorem e_wdOf_above (hB : GlobalTheory.Published.DeRhamPotSemistable) {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (P : Pin hL D)
    (i : D.nd.Loc) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)) {b : ℕ}
    (r : G D.host.E D.nd.Om →* GL (Fin b) (Qbar (D.nd.l i)))
    (hr : Continuous (fun g => ((r g : GL (Fin b) (Qbar (D.nd.l i))) : Matrix (Fin b) (Fin b) (Qbar (D.nd.l i)))))
    (hd : D.naut.IsdRW i r w) :
    IsPstAt (D.loc (D.nd.l i)) (D.nbr i w hw) (resDec D.nd.plOm.1 r w) ∧
    P.T.e w (D.naut.wdOf i r w) = wdAt (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w)
      (D.nbr_ind i w hw) (resDec D.nd.plOm.1 r w) := by
  have hd' : P.wd.IsdRW (D.nd.l i) (D.naut.iotaQC i) r w := (P.wdOf i b r w).2.2.2.1.1 hd
  have pst : ∀ (O : Type) [CommRing O] [Algebra ℤ_[D.nd.l i] O] [TopologicalSpace O]
      (Bw : LocBridge (D.nd.l i) D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw →
      IsPstAt (D.loc (D.nd.l i)) Bw (resDec D.nd.plOm.1 r w) := by
    intro O _ _ _ Bw hj
    exact hB.isPstAt (D.locT (D.nd.l i)) Bw _ (hr.comp continuous_subtype_val)
      ((GlobalTheory.DeRhamRead.isdRW_iff_isdRAt D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) w hw O Bw hj b r hr).1 hd')
  refine ⟨pst _ (D.nbr i w hw) (D.nbr_ind i w hw), ?_⟩
  obtain ⟨L1, B1, j1, e1⟩ := P.wd.above (D.nd.l i) (D.naut.iotaQC i) r w hw
  rw [(P.wdOf i b r w).1, e1]
  exact GlobalTheory.T.fontaineParameter_independent_of_localEmbedding (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩ (D.naut.iotaQC i)
    D.host.E D.nd.Om _ w (D.nd.plOm.2 w) _ (D.nd.O i) B1 (D.nbr i w hw) j1 (D.nbr_ind i w hw) b _
    (hr.comp continuous_subtype_val) (pst _ B1 j1) (pst _ (D.nbr i w hw) (D.nbr_ind i w hw))

set_option maxHeartbeats 1000000 in

theorem main : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D),
    GlobalTheory.LocalInv.EigAway D.nd D.naut P.T.eig ∧ GlobalTheory.LocalInv.EigAbove D.nd D.naut P.T.eig := by
  intro hB hL D P
  refine ⟨eigAway_of_wdOfTie _ _ _ D.nd D.naut P.T (wdOfTie P), ?_⟩
  intro i a ρ χ hρ hχ w hw dρ dχ hs σ hσ
  obtain ⟨p1, e1⟩ := e_wdOf_above hB P i w hw (mapRep (iotaOQ D.nd D.naut i) ρ)
    (GlobalTheory.LocalInv.cont_mapRep_iotaOQ D.nd D.naut i ρ hρ) dρ
  obtain ⟨p2, e2⟩ := e_wdOf_above hB P i w hw (mapRep (iotaOQ D.nd D.naut i) (GlobalTheory.LocalInv.charRep D.nd i χ))
    (GlobalTheory.LocalInv.cont_mapRep_iotaOQ D.nd D.naut i _ hχ) dχ
  have hW := mem_Weil_of_isFrob (D.nd.plOm.2 w) hσ
  show ((P.T.e w (GlobalTheory.LocalInv.wd D.nd D.naut i (GlobalTheory.LocalInv.charRep D.nd i χ) w)).inePol σ).roots ≤
    ((P.T.e w (GlobalTheory.LocalInv.wd D.nd D.naut i ρ w)).inePol σ).roots
  rw [GlobalTheory.LocalInv.wd, GlobalTheory.LocalInv.wd, e1, e2, WD.inePol_of_mem _ hW, WD.inePol_of_mem _ hW]
  obtain ⟨v, hv, hs⟩ := hs
  have hv0 : (D.naut.iotaQ i) ∘ v ≠ 0 := by
    intro h0
    apply hv
    funext k
    have := congrFun h0 k
    simpa using this
  have hM : ∀ g : ↥(Dec (F := D.host.E) (D.nd.plOm.1 w)),
      ((resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) ρ) w g : GL (Fin a) (Om (D.nd.l i))) :
        Matrix (Fin a) (Fin a) (Om (D.nd.l i))) = (GlobalTheory.LocalInv.matK D.nd i ρ g).map (D.naut.iotaQ i) := by
    intro g
    ext p q
    rfl
  have hC : ∀ g : ↥(Dec (F := D.host.E) (D.nd.plOm.1 w)),
      ((resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) (GlobalTheory.LocalInv.charRep D.nd i χ)) w g :
        GL (Fin 1) (Om (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Om (D.nd.l i))) 0 0 =
        D.naut.iotaQ i (algebraMap (D.nd.O i) (Kf D.nd i) ((χ g : (D.nd.O i)ˣ) : D.nd.O i)) := by
    intro g
    rfl
  rcases hs with hs | hs
  · refine GlobalTheory.T.local_galois_rep_decomposition_induced (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) _ _ p1 p2
      ((D.naut.iotaQ i) ∘ v) hv0 (fun g => ?_) ⟨σ, hW⟩
    rw [hM, hC]
    funext k
    rw [← RingHom.map_mulVec, hs g g.2]
    simp
  · refine GlobalTheory.T.local_galois_rep_induced_matches (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩ (D.naut.iotaQC i) (D.nbr i w hw)
      (D.nd.plOm.2 w) (D.nbr_ind i w hw) _ _ p1 p2 ((D.naut.iotaQ i) ∘ v) hv0 (fun g => ?_) ⟨σ, hW⟩
    rw [hM, hC]
    funext k
    rw [← RingHom.map_vecMul, hs g g.2]
    simp

end GlobalTheory.EigConcrete

end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowsAClose

theorem main : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), JumpsCard D.nd D.naut → GlobalTheory.NRows.RowsA D := by
  intro hP hL D P hJ
  have hlab := GlobalTheory.TieLabAt.main hL D P
  have hrig : IsobaricRigid D.nd D.naut := GlobalTheory.NPin.isobaricRigid_of_pin hP.fin hP.js hL D P
  have han1 := GlobalTheory.RowClose.isobaricCuspidalMultiplicityOne_of_twisted _ _ _ D.nd D.naut hrig
  have han2 := GlobalTheory.SpehRigid.isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne _ _ _ D.nd D.naut hrig
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hP.cheb D
  have ha5 : Formalism.MainNotions.SumRepresentations.adm5 D := (Formalism.MainNotions.SumRepresentations.condition_iff_additive_maps D).2 ⟨han1, han2, fun Sg hSg => by
    have hd := (hcheb hSg.toFinset).closure_eq
    convert hd using 4 with σ
    simp [Set.Finite.mem_toFinset]⟩
  have haut := GlobalTheory.AutomorphismSplitting.tieAut_and_split hP.fin hL D P
  have htie0 : Formalism.MainNotions.SumRepresentations.tie0 D :=
    ⟨GlobalTheory.RowTieLP.main D P.T, haut.1, GlobalTheory.T.galois_compatibility_of_jumps hP.berger hL D P hJ⟩
  have ha2 : Formalism.MainNotions.SumRepresentations.adm2 D := GlobalTheory.GalClose.main hP hL D P
  have ha7 : Formalism.MainNotions.SumRepresentations.adm7 D := GlobalTheory.TempGal.main hP.fin hP.gal hL D P
  have heig := GlobalTheory.EigConcrete.main hP.berger hL D P
  refine ⟨hlab.1, GlobalTheory.RowClose.heckeSplitOne_of_charTied D P.cf P.C P.tp P.chr, htie0, ha2, han1, han2, ha5, ha7,
    GlobalTheory.LocalInvEta.noLocalInvariants_everywhere D P.T htie0 ha2 ha5 ha7
      (GlobalTheory.MuIntegral.muInt_of_charTied D P.cf P.C P.tp P.chr) (GlobalTheory.GoodCuspPoint.main D hlab.1) heig.1 heig.2,
    haut.2⟩

end GlobalTheory.RowsAClose
end
