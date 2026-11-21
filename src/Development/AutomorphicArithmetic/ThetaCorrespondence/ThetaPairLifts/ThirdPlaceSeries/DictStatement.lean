import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilityEighthStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilityEighth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGoodStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodOffGp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExtensionVectorThetaCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExtensionVectorThetaCompatible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAutomorphicVectorSatakeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAutomorphicVectorSatake
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlAwayRepsum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsoTypeSpaceMaximalCompactStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsoTypeSpaceMaximalCompact
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHasSatakeOfUnr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeUnramifiedFrobeniusEigenStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeUnramifiedFrobeniusEigen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSplit_of_hk3_good : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → ∃ sp : SplitPlace D.host.E, sp.w = w ∧ (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) := by
  first | exact @_root_.GlobalTheory.OffBad.offbad_alt | exact _root_.GlobalTheory.OffBad.offbad_alt | (intros; apply _root_.GlobalTheory.OffBad.offbad_alt <;> assumption)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.EigTransport
end GlobalTheory.EigTransport
namespace GlobalTheory.EigTransport
end GlobalTheory.EigTransport
namespace GlobalTheory.EigTransport
end GlobalTheory.EigTransport
namespace GlobalTheory.EigTransport
end GlobalTheory.EigTransport
namespace GlobalTheory.EigTransport
end GlobalTheory.EigTransport
namespace GlobalTheory.EigTransport
theorem transport_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → ∀ sp : SplitPlace D.host.E, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) sp.w → (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) ((P.M.loc i).real (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i))) = s sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0) • (P.M.loc i).real (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) := by
  intro _ hL D P X A _ _ _ i hμ j hj f y hy h hOps s hEig sp hG hJ ϖ hϖ k hk
  have hn : (Formalism.IndefR.Links.Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have hLab := isLab_std A.hF (A.PV j) (A.stdV j) hn sp ϖ hϖ k hk
  have hsum := eig_sum X hμ j f y hy h hOps s hEig sp.w hG (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0) hLab
  have hGf := GlobalTheory.DefLiftHecke.rep_mem_GfC (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0)
  classical
  let xi : Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Vc D j) → Formalism.AUTREP.GAf D.host.E D.R.nV := fun γ =>
    if hγ : γ ∈ Formalism.L2.Theta.GfC (Formalism.IndefR.Links.Vc D j) then ((A.PV j).onto γ hγ).choose else 1
  have hxi : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0), (A.PV j).ψ (xi γ) = γ := fun γ hγ => by
    simp only [xi, dif_pos (hGf γ hγ)]
    exact ((A.PV j).onto γ (hGf γ hγ)).choose_spec
  have hT : ∀ x ∈ Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k, TrivOutside {sp.v} x := fun x hx => hx.1
  suffices key : ∀ (m : ℕ) (e : j.1 + 1 = m) (p1 : 1 ≤ m) (p2 : m ≤ D.R.m),
      (∀ κ : Formalism.AUTREP.GAf D.host.E D.R.nV, TrivOutside {sp.v} κ →
        (κ ∈ (P.M (D.nd.mu i) m p1 p2).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧
          ∀ hκ : κ ∈ (P.M (D.nd.mu i) m p1 p2).J, (P.M (D.nd.mu i) m p1 p2).χ ⟨κ, hκ⟩ = 1) →
      NG.heckeD (P.M (D.nd.mu i) m p1 p2).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k)
          ((P.M (D.nd.mu i) m p1 p2).real (e ▸ f)) =
        s sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0) • (P.M (D.nd.mu i) m p1 p2).real (e ▸ f) from key _ hj _ _ hJ
  intro m e
  subst e
  intro p1 p2 hJ
  have hF : ∀ g, (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f g =
      A.eW _ hμ j (X.fn hμ j f ((A.PV j).ψ ((A.a j)⁻¹ * g))) := fun g => A.real (D.nd.mu i) hμ j f g
  have hinv : ∀ κ (hκ : κ ∈ (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J), (P.M (D.nd.mu i) (j.1 + 1) p1 p2).χ ⟨κ, hκ⟩ = 1 →
      ∀ g, (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f (g * κ) = (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f g := by
    intro κ hκ h1 g
    have hmem : (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f ∈ Formalism.L2.NG.TypeSp (P.M (D.nd.mu i) (j.1 + 1) p1 p2).wt.ρ
        (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J (P.M (D.nd.mu i) (j.1 + 1) p1 p2).χ := by
      rw [← (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real_range]
      exact LinearMap.mem_range_self _ _
    have := congrFun (hmem.2 ⟨κ, hκ⟩) g
    rw [h1] at this
    simp only [Units.val_one, one_smul] at this
    exact this
  have hmemT : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0), xi γ ∈ Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k := by
    intro γ hγ
    refine (tSet_iff A.hF (A.PV j) (A.stdV j) hn sp ϖ hϖ k hk _).2 ⟨γ, hγ, ?_⟩
    rw [hxi γ hγ, inv_mul_cancel]
    exact GlobalTheory.DefLiftHecke.one_mem_hyp _ _
  funext g
  show (∑ᶠ c : Formalism.AUTREP.GAf D.host.E D.R.nV ⧸ (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J,
      if hc : ∃ x ∈ Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k,
          (x : Formalism.AUTREP.GAf D.host.E D.R.nV ⧸ (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J) = c then
        (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f (g * hc.choose) else 0) = _
  rw [finsum_cosets (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J _ (GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0)) xi _
    ?h1 ?h2 ?h3 ?h4 g]
  case h1 => exact hmemT
  case h2 =>
    intro x hx
    obtain ⟨γ, hγ, hm⟩ := (tSet_iff A.hF (A.PV j) (A.stdV j) hn sp ϖ hϖ k hk x).1 hx
    refine ⟨γ, hγ, ?_⟩
    rw [← hxi γ hγ, ← map_inv, ← map_mul] at hm
    obtain ⟨hU, hT'⟩ := (frame_hyp A.hF (A.PV j) (A.stdV j) sp _).1 hm
    exact (hJ _ hT').1.2 hU
  case h3 =>
    intro γ hγ γ' hγ' hm
    have ht := triv_mul (triv_inv (hT _ (hmemT γ hγ))) (hT _ (hmemT γ' hγ'))
    have hU := (hJ _ ht).1.1 hm
    have hh := (frame_hyp A.hF (A.PV j) (A.stdV j) sp _).2 ⟨hU, ht⟩
    rw [map_mul, map_inv, hxi γ hγ, hxi γ' hγ'] at hh
    exact rep_inj _ _ _ hLab γ hγ γ' hγ' hh
  case h4 =>
    intro y hy y' hy' hm g0
    have ht := triv_mul (triv_inv (hT _ hy)) (hT _ hy')
    have := hinv _ hm ((hJ _ ht).2 hm) (g0 * y)
    rw [mul_assoc, mul_inv_cancel_left] at this
    exact this
  rw [Pi.smul_apply, hF g]
  calc ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0), (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f (g * xi γ)
      = ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0),
          A.eW _ hμ j (X.fn hμ j f ((A.PV j).ψ ((A.a j)⁻¹ * g) * γ)) :=
        Finset.sum_congr rfl fun γ hγ => by rw [hF, ← mul_assoc, map_mul, hxi γ hγ]
    _ = A.eW _ hμ j (∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0),
          X.fn hμ j f ((A.PV j).ψ ((A.a j)⁻¹ * g) * γ)) := (map_sum _ _ _).symm
    _ = _ := by rw [hsum, map_smul]
end GlobalTheory.EigTransport
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extension_vector_theta_compatible_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → ∀ sp : SplitPlace D.host.E, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) sp.w → (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) ((P.M.loc i).real (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i))) = s sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0) • (P.M.loc i).real (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) := by
  atlas_forward_decl _root_.GlobalTheory.EigTransport.transport_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.IsoComp
open GlobalTheory.CompRed
section Gen
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
variable {W : Type} [AddCommGroup W] [Module ℂ W]
end Gen
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (x : D.nd.X i) (f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)), f' ∈ eigC D.nd D.naut i x → f' ≠ 0 → ∀ sp : SplitPlace D.host.E, ∀ c : ℕ → ℂ, (∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) ((P.M.loc i).real f') = c k • (P.M.loc i).real f') → ∃ Q : D.naut.AV i, D.naut.ptV i Q = some x ∧ ∃ F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ ∧ F ≠ 0 ∧ ∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) F = c k • F := by
  intro hL D P i x f' hf' hf0 sp c hc
  classical
  have hfin : ∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k, ((fun y : GAf D.host.E D.R.nV =>
      (y : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J)) '' Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k).Finite := by
    intro ϖ hϖ k
    obtain ⟨N, hN, hNJ⟩ := (P.M.loc i).J_open
    exact GlobalTheory.T.finite_image_heckeSet_split_place_cosets D.host.E D.R.nV (P.M.loc i).J ⟨N, hN, fun κ hκ => (hNJ κ hκ).1⟩ sp ϖ k hϖ
  unfold eigC at hf'
  rw [Submodule.mem_iSup_iff_exists_finsupp] at hf'
  obtain ⟨g, hgmem, hgsum⟩ := hf'
  have hg' : ∀ Q, g Q ≠ 0 → D.naut.ptV i Q = some x ∧ g Q ∈ D.naut.typeV i Q := by
    intro Q hQ
    by_cases h : D.naut.ptV i Q = some x
    · refine ⟨h, ?_⟩
      have := hgmem Q
      rwa [iSup_pos (show Q ∈ {P | D.naut.ptV i P = some x} from h)] at this
    · exfalso
      have := hgmem Q
      rw [iSup_neg (show Q ∉ {P | D.naut.ptV i P = some x} from h), Submodule.mem_bot] at this
      exact hQ this
  obtain ⟨Q0, hQ0⟩ : ∃ Q, g Q ≠ 0 := by
    by_contra h
    push_neg at h
    apply hf0
    rw [← hgsum, show g = 0 from Finsupp.ext h, Finsupp.sum_zero_index]
  set G : D.naut.AV i → (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) := fun Q => (P.M.loc i).real (g Q) with hGdef
  have hsum : (P.M.loc i).real f' = ∑ Q ∈ g.support, G Q := by
    rw [← hgsum, Finsupp.sum, map_sum]
  have hGiso : ∀ Q ∈ g.support, G Q ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    intro Q hQ
    have hy := (hg' Q (Finsupp.mem_support_iff.1 hQ)).2
    rw [P.H.av.typeV] at hy
    exact hy
  have hind := isoTyp_indep (P.M.loc i).wt (P.H.av.S i) (P.H.av.irr i) (P.H.av.inj i)
  have hQ0s : Q0 ∈ g.support := Finsupp.mem_support_iff.2 hQ0
  refine ⟨Q0, (hg' Q0 hQ0).1, G Q0, hGiso Q0 hQ0s, ?_, ?_, ?_⟩
  · rw [← (P.M.loc i).real_range]
    exact ⟨g Q0, rfl⟩
  · intro h
    exact hQ0 ((P.M.loc i).real_inj (h.trans (map_zero (P.M.loc i).real).symm))
  · intro ϖ hϖ k hk
    set Dk := Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k
    set t : D.naut.AV i → (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) :=
      fun Q => NG.heckeD (P.M.loc i).J Dk (G Q) - c k • G Q with htdef
    have htmem : ∀ Q ∈ g.support, t Q ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := fun Q hQ =>
      Submodule.sub_mem _ (heckeD_mem_isoTyp _ _ _ (hfin ϖ hϖ k) _ (hGiso Q hQ))
        (Submodule.smul_mem _ _ (hGiso Q hQ))
    have htsum : ∑ Q ∈ g.support, t Q = 0 := by
      simp only [t]
      rw [Finset.sum_sub_distrib, ← heckeD_finset_sum _ _ (hfin ϖ hϖ k), ← Finset.smul_sum, ← hsum, hc ϖ hϖ k hk,
        sub_self]
    have hrest : t Q0 = -∑ Q ∈ g.support.erase Q0, t Q := by
      rw [eq_neg_iff_add_eq_zero, Finset.add_sum_erase _ _ hQ0s, htsum]
    have hmem2 : t Q0 ∈ ⨆ (j : D.naut.AV i) (_ : j ≠ Q0), NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i j) := by
      rw [hrest]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun Q hQ => ?_)
      obtain ⟨hne, hQs⟩ := Finset.mem_erase.1 hQ
      exact (le_iSup₂ (f := fun (j : D.naut.AV i) (_ : j ≠ Q0) => NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i j)) Q hne)
        (htmem Q hQs)
    have h0 : t Q0 = 0 := Submodule.disjoint_def.1 (iSupIndep_def.1 hind Q0) _ (htmem Q0 hQ0s) hmem2
    exact sub_eq_zero.1 h0
end GlobalTheory.IsoComp
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_automorphic_vector_satake_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (x : D.nd.X i) (f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)), f' ∈ eigC D.nd D.naut i x → f' ≠ 0 → ∀ sp : SplitPlace D.host.E, ∀ c : ℕ → ℂ, (∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) ((P.M.loc i).real f') = c k • (P.M.loc i).real f') → ∃ Q : D.naut.AV i, D.naut.ptV i Q = some x ∧ ∃ F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ ∧ F ≠ 0 ∧ ∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) F = c k • F := by
  atlas_forward_decl _root_.GlobalTheory.IsoComp.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.SplitSatLoc
section Local
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => NumberField.maximalRealSubfield L
end Local
section Key
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => NumberField.maximalRealSubfield L
end Key
section Main
set_option maxHeartbeats 800000 in
theorem exists_locComp_hasSatake_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q : D.naut.AV i) (sp : SplitPlace D.host.E), (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ B : Multiset ℂˣ, B.card = D.R.nV → ∀ F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ → F ≠ 0 → (∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) F = GlobalTheory.LFun.satEig (Formalism.UG.qV D.host.E sp.w) D.R.nV B k • F) → ∃ (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (sp.w.adicCompletion D.host.E))) (α : Fin D.R.nV → ℂˣ), IsLocS (P.H.av.S i Q) sp σ ∧ GlobalTheory.SmGL.HasSatake σ.ρ α ∧ Finset.univ.val.map α = B := by
  intro _ hL D P i Q sp hJ B hB F hFiso hFty hF0 hFeig
  have hirr := P.H.av.irr i Q
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV
    ({ (P.M.loc i).wt with S := P.H.av.S i Q, irrS := hirr } : NG.AutRep D.host.E D.R.nV) sp
  have hσ' : IsLocS (P.H.av.S i Q) sp σ := hσ
  obtain ⟨c, T0, hc, hcL, -, -, -⟩ := hσ'
  have hFfix : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → NG.rt D.host.E D.R.nV κ F = F := by
    intro κ hκ ht
    have hJκ := ((hJ κ ht).1).2 hκ
    have h1 := hFty.2 ⟨κ, hJκ⟩
    rw [(hJ κ ht).2 hJκ] at h1
    simpa using h1
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.LocVec.main D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) hirr sp σ hσ c hc hcL
    (Formalism.UG.GLint (Fin D.R.nV) (sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).toSubring) 1
    (fun g hg => hg) (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ) F hFiso hF0
    (fun κ ht h => by
      rw [MonoidHom.one_apply, Units.val_one, one_smul]
      exact hFfix κ ((GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff sp ht).1 h) ht)
  have hufix : u ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.LFun.KGL sp.w D.R.nV) := by
    refine GlobalTheory.LGrp.mem_fixed.2 fun A hA => ?_
    have hA' := (map_mem_KGL_iff hc hcL (Matrix.GeneralLinearGroup.map c.symm.toRingHom A)).1
      (by rw [map_map_symm]; exact hA)
    have := hu _ hA'
    rwa [map_map_symm, MonoidHom.one_apply, Units.val_one, one_smul] at this
  have hsph : GlobalTheory.SmGL.IsSpherical σ.ρ := by
    have : u ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KO (sp.w.adicCompletion D.host.E) (Fin D.R.nV)) := by
      rw [GlobalTheory.HeckeEigConj.KO_eq_KGL D.host.E sp.w D.R.nV]; exact hufix
    exact (Submodule.ne_bot_iff _).2 ⟨u, this, hu0⟩
  have hR := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 sp.w)
  obtain ⟨α, hα⟩ := _root_.UpperTheory.One.M.exists_hasSatake_of_unr_alt hR ((_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical hR σ).2 hsph)
  have hSat := GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake D.host.E sp.w D.R.nV σ.V σ.ρ α hα
  obtain ⟨e, he1, he2⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc D.host.E D.R.nV sp
  have hspan := GlobalTheory.SpanLoc.main D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) hirr sp σ hσ c hc hcL hFiso
  rw [iSup_subtype'] at hspan
  have hFK : F ∈ GlobalTheory.PRep.fixed (locAct D.R.nV (P.M.loc i).wt.W sp c e) (GlobalTheory.LFun.KGL sp.w D.R.nV) := by
    refine GlobalTheory.LGrp.mem_fixed.2 fun A hA => ?_
    rw [locAct_apply]
    refine hFfix _ ((GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff sp (he1 _)).1 ?_) (he1 _)
    rw [he2]
    exact (map_mem_KGL_iff hc hcL _).1 (by rw [map_map_symm]; exact hA)
  have hspan' : F ∈ ⨆ T : {T : σ.V →ₗ[ℂ] (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) // (∀ v, T v ∈ NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) ∧ ∀ x : GAf D.host.E D.R.nV, TrivOutside {sp.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (sp.loc D.R.nV x)) v) = NG.rt D.host.E D.R.nV x (T v)}, LinearMap.range T.1 := hspan
  have hequiv : ∀ (T : {T : σ.V →ₗ[ℂ] (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) // (∀ v, T v ∈ NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) ∧ ∀ x : GAf D.host.E D.R.nV, TrivOutside {sp.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (sp.loc D.R.nV x)) v) = NG.rt D.host.E D.R.nV x (T v)}) g v, T.1 (σ.ρ g v) = locAct D.R.nV (P.M.loc i).wt.W sp c e g (T.1 v) := by
    intro T g v
    rw [locAct_apply, ← T.2.2 _ (he1 _) v, he2, map_map_symm]
  have hIs : GlobalTheory.LFun.IsSatVecGL sp.w (locAct D.R.nV (P.M.loc i).wt.W sp c e) F (Finset.univ.val.map α) :=
    GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup (ρ := locAct D.R.nV (P.M.loc i).wt.W sp c e) σ.irr hSat
      Subtype.val hequiv hspan' hFK hF0
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV (E := maximalRealSubfield D.host.E) sp.v
  have hϖ' : IsUnif D.host.E sp.v ϖ := hϖ
  have heq : ∀ k ≤ D.R.nV, GlobalTheory.LFun.satEig (Formalism.UG.qV D.host.E sp.w) D.R.nV (Finset.univ.val.map α) k =
      GlobalTheory.LFun.satEig (Formalism.UG.qV D.host.E sp.w) D.R.nV B k := by
    intro k hk
    have h1 := hIs.2.2.2 (c ϖ) (isUnifV_map hc hcL hϖ') k hk
    rw [← heckeD_eq_heckeVec sp c hc hcL e he1 he2 _ (fun κ ht => (hJ κ ht).1) hϖ' k hFfix, hFeig ϖ hϖ' k hk] at h1
    exact (smul_left_injective ℂ hF0 h1).symm
  exact ⟨σ, α, hσ, hα, GlobalTheory.LFun.eq_of_satEig_eq (GlobalTheory.LFun.qV_ne_zero sp.w) (by simp) hB heq⟩
end Main
end GlobalTheory.SplitSatLoc
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iso_type_space_maximal_compact_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q : D.naut.AV i) (sp : SplitPlace D.host.E), (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ B : Multiset ℂˣ, B.card = D.R.nV → ∀ F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ → F ≠ 0 → (∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) F = GlobalTheory.LFun.satEig (Formalism.UG.qV D.host.E sp.w) D.R.nV B k • F) → ∃ (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (sp.w.adicCompletion D.host.E))) (α : Fin D.R.nV → ℂˣ), IsLocS (P.H.av.S i Q) sp σ ∧ GlobalTheory.SmGL.HasSatake σ.ρ α ∧ Finset.univ.val.map α = B := by
  atlas_forward_decl _root_.GlobalTheory.SplitSatLoc.exists_locComp_hasSatake_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LlcSplit
theorem locV_unr_frobEig_of_hasSatake_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q : D.naut.AV i) (sp : SplitPlace D.host.E) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (sp.w.adicCompletion D.host.E))) (α : Fin D.R.nV → ℂˣ), IsLocS (P.H.av.S i Q) sp σ → GlobalTheory.SmGL.HasSatake σ.ρ α → D.naut.unr (D.naut.locV i Q sp.w) ∧ D.naut.frobEig (D.naut.locV i Q sp.w) = Finset.univ.val.map (fun k => (((α k)⁻¹ : ℂˣ) : ℂ)) := by
  intro hL D P i Q sp σ α hS hα
  have h3 := P.au (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i Q) sp σ hS
  rw [← P.H.emb i Q, ← D.nbc.embAV_loc i Q sp.w,
    _root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 sp.w)) hα] at h3
  have hu : D.naut.unr (D.naut.locV i Q sp.w) :=
    (P.T.unr _ _).2 (by rw [h3]; exact (GlobalTheory.WeilDeligne.WD.unr_mk _).2 (GlobalTheory.WeilDeligne.WDRep.unr_diag _))
  refine ⟨hu, ?_⟩
  rw [P.T.frobEig _ _ hu, h3, GlobalTheory.WeilDeligne.WD.frobEig_diag]
end GlobalTheory.LlcSplit
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unr_and_frobEig_eq_inv_satake : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q : D.naut.AV i) (sp : SplitPlace D.host.E) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (sp.w.adicCompletion D.host.E))) (α : Fin D.R.nV → ℂˣ), IsLocS (P.H.av.S i Q) sp σ → GlobalTheory.SmGL.HasSatake σ.ρ α → D.naut.unr (D.naut.locV i Q sp.w) ∧ D.naut.frobEig (D.naut.locV i Q sp.w) = Finset.univ.val.map (fun k => (((α k)⁻¹ : ℂˣ) : ℂ)) := by
  atlas_forward_decl _root_.GlobalTheory.LlcSplit.locV_unr_frobEig_of_hasSatake_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.StrSplitDict.dict_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D) (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i))) (Formalism.IndefR.Links.Vc D j).rank s B → ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → ∃ Q : D.naut.AV i, D.naut.ptV i Q = some x ∧ D.naut.unr (D.naut.locV i Q w) ∧ (B w).map (fun a : ℂˣ => (a : ℂ)) = (D.naut.frobEig (D.naut.locV i Q w)).map (fun a : ℂ => a⁻¹) := by
  intro hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 h hh s B hs hB w hw hsp
  have hrank : (Formalism.IndefR.Links.Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  obtain ⟨sp, hspw, hJ⟩ := _root_.GlobalTheory.T.isSplit_of_hk3_good hAF hL D P X hA h41 h7 htl i w hw hsp
  have hv : w.under (𝓞 D.host.F) ∉ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i)) :=
    (GlobalTheory.DownLift.Params.good_iff _ _ _).1 hw
  rcases hB _ hv w rfl with ⟨-, hcard, heq⟩ | ⟨hin, -⟩
  swap
  · exact absurd hsp (GlobalTheory.LFun.not_isSplit_of_isInertAt hin)
  rw [hrank] at hcard heq
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hy0
    have h1 : X.R.extV j (X.tupT (D.nd.mu i)) y = 0 := by
      rw [hy]
      show (X.IL.jMt (D.nd.mu i) hμ j 0).1 = 0
      simp only [map_zero, ZeroMemClass.coe_zero, Submodule.coe_zero]
    exact X.hinj j (X.tupT (D.nd.mu i)) (h1.trans (LinearMap.map_zero _).symm)
  have hf'0 := GlobalTheory.StrSplitDict.cast_ne_zero D _ _ _ hj f hf0
  subst hspw
  have htr := _root_.GlobalTheory.T.extension_vector_theta_compatible_alt hAF hL D P X hA h41 h7 htl i hμ j hj f y hy h hh s hs sp hw hJ
  obtain ⟨Q, hQx, F, hFi, hFt, hF0, hFe⟩ := _root_.GlobalTheory.T.exists_automorphic_vector_satake_alt hL D P i x _ hf hf'0 sp
    (fun k => s sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0)) htr
  obtain ⟨σ, α, hloc, hsat, hα⟩ := _root_.GlobalTheory.T.iso_type_space_maximal_compact_alt hAF hL D P i Q sp hJ (B sp.w) hcard F hFi hFt hF0
    (fun ϖ hϖ k hk => by rw [hFe ϖ hϖ k hk, heq k hk])
  obtain ⟨hu, hfr⟩ := _root_.GlobalTheory.T.unr_and_frobEig_eq_inv_satake hL D P i Q sp σ α hloc hsat
  refine ⟨Q, hQx, hu, ?_⟩
  rw [hfr, ← hα]
  simp [Multiset.map_map, Function.comp_def]
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_eigen_compatibility_eighth_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D) (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i))) (Formalism.IndefR.Links.Vc D j).rank s B → ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → ∃ Q : D.naut.AV i, D.naut.ptV i Q = some x ∧ D.naut.unr (D.naut.locV i Q w) ∧ (B w).map (fun a : ℂˣ => (a : ℂ)) = (D.naut.frobEig (D.naut.locV i Q w)).map (fun a : ℂ => a⁻¹) := by
  atlas_forward_decl _root_.GlobalTheory.StrSplitDict.dict_alt
end
end
