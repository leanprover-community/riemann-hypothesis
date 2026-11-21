import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenHeckeMatchStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenHeckeMatch
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtOfBuiltStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ContainsWithLocStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvOLawsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteChosenSetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteChosenSet
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.JointConditionOfConstituentConditionSplit

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
end
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.CrysFromGTwo
end GlobalTheory.CrysFromGTwo
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.DualTwistCrys
end GlobalTheory.DualTwistCrys
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.CrysChiOne
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}
end GlobalTheory.CrysChiOne
end
section
namespace Formalism.MainNotions.N
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open NumberField IsDedekindDomain
end Formalism.MainNotions.N
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices
namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
theorem residual_charpoly_eq_alt_alt (hC : GlobalTheory.TwSys.Cheb) (D : D7) (h32 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (i : D.nd.Loc)
    (rep : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i rep)
    (x π : D.nd.X i) (ρx ρ0 : GE D.nd →* GL (Fin D.R.r) (D.nd.O i))
    (hx : ∃ e, IsDecomp (t := D.R.t) (rep x) ρx (D.nd.chi i) e)
    (r0 : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)) (hr0 : IsHeckeGalois D.nd i π r0)
    (h0 : ∃ e, IsDecomp (t := D.R.t) r0 ρ0 (D.nd.chi i) e) (g : GE D.nd) :
    ((mat ρx g).map (IsLocalRing.residue (D.nd.O i))).charpoly =
      ((mat ρ0 g).map (IsLocalRing.residue (D.nd.O i))).charpoly := by
  classical
  have hG3 := (_root_.UpperTheory.GalS.g3' ((h32 i).2.2 rep hr).2.2.1).2 x π g
  obtain ⟨ex, hex⟩ := hx
  obtain ⟨e0, he0⟩ := h0
  have dx := charpoly_of_decomp D i rep (fun _ => ρx) x ⟨ex, hex⟩ g
  have d0 := charpoly_of_decomp D i (fun _ => r0) (fun _ => ρ0) π ⟨e0, he0⟩ g
  have hc := charpoly_eq_of_isHeckeGalois hC D i rep hr π r0 hr0 g
  set res := IsLocalRing.residue (D.nd.O i)
  set P : (D.nd.O i)[X] := ∏ c ∈ Finset.Icc 1 D.R.t, (X - C ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i))
  have hP : (P.map res) ≠ 0 := by
    apply Polynomial.Monic.ne_zero
    apply Polynomial.Monic.map
    exact Polynomial.monic_prod_of_monic _ _ fun c _ => Polynomial.monic_X_sub_C _
  have e1 : ((mat ρx g).map res).charpoly * P.map res = ((mat ρ0 g).map res).charpoly * P.map res := by
    rw [Matrix.charpoly_map, Matrix.charpoly_map, ← Polynomial.map_mul, ← Polynomial.map_mul]
    have ex' : (rO D.nd i rep x g).charpoly = (mat ρx g).charpoly * P := dx
    have e0' : (mat r0 g).charpoly = (mat ρ0 g).charpoly * P := d0
    rw [← ex', ← e0', ← hc, ← Matrix.charpoly_map, ← Matrix.charpoly_map]
    exact hG3
  exact mul_right_cancel₀ hP e1
end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end
section
end
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
end
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.CrysFromGTwo
end GlobalTheory.CrysFromGTwo
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.DualTwistCrys
end GlobalTheory.DualTwistCrys
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.CrysChiOne
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}
end GlobalTheory.CrysChiOne
end
section
namespace Formalism.MainNotions.N
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open NumberField IsDedekindDomain
end Formalism.MainNotions.N
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices
namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
theorem setting_of_live_alt_alt : GlobalTheory.TwSys.Cheb → ∀ (D : D7), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → GlobalTheory.SplitCoef.OSplit D → ∀ i : D.nd.Loc,
    ZDecomp D.nd i → Live D.nd i → ∃ (rep : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))),
      GoodR D.nd i rep ∧ GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.HidaSetting D.R.t (D.nd.T i) (D.nd.Z i) rep ρ (D.nd.chi i) := by
  intro hC D h32 hS i hZ hL
  classical
  obtain ⟨rep, hr⟩ := (h32 i).1.2
  have hG1 := ((h32 i).2.2 rep hr).1
  have hG3 := _root_.UpperTheory.GalS.g3' ((h32 i).2.2 rep hr).2.2.1
  have hJ := UpperTheory.GalS.jointCondition_of_constituentCondition_split D i rep hr (hG3.1 (Or.inr hL)) (hS i)
  let ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) := fun x =>
    if hx : x ∈ D.nd.Z i then Classical.choose (hZ x hx (rep x) (hr x)) else 1
  have hρ : ∀ x ∈ D.nd.Z i, ∃ e, IsDecomp (t := D.R.t) (rep x) (ρ x) (D.nd.chi i) e := by
    intro x hx
    have := Classical.choose_spec (hZ x hx (rep x) (hr x))
    simp only [ρ, dif_pos hx]
    exact this
  obtain ⟨π, hπ, r0, ρ0, hr0, h0, habs⟩ := hL
  refine ⟨rep, ρ, hr, D.nd.T_local i, D.nd.T_sep i, fun x => ?_, fun h d => ?_,
    hJ, hG3.2, hρ, fun x hx => ?_⟩
  · have hss := (hr x).2.1
    intro W hW
    obtain ⟨W', h1, h2⟩ := hss W fun g v hv => hW g v hv
    exact ⟨W', fun g v hv => h1 g v hv, h2⟩
  · obtain ⟨f, hf⟩ := hG1 h d
    have : (fun x => (mat (rep x) h).charpolyRev.coeff d) = (f : D.nd.X i → D.nd.O i) :=
      funext fun x => (hf x).symm
    rw [this]
    exact f.2
  · have hpos := pos_of_absIrrSub _ habs
    haveI : Nonempty (Fin D.R.r) := ⟨⟨0, hpos⟩⟩
    refine absIrrSub_of_span_eq_top hpos _ ?_
    refine span_eq_top_of_trace_eq _ (mapRep (IsLocalRing.residue (D.nd.O i)) ρ0) (fun g => ?_)
      (GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub _ habs)
    rw [mat_mapRep, mat_mapRep, Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff,
      _root_.GlobalTheory.AbsoluteIrreducibilityOfTraceSpan.residual_charpoly_eq_alt_alt hC D h32 i rep hr x π (ρ x) ρ0 (hρ x hx) r0 hr0 h0 g]
end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end
section
end
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial
  GlobalTheory.EtaJoin GlobalTheory.CoefDuty
namespace GlobalTheory.OChoose
theorem oChoose_alt : GlobalTheory.TwSys.Cheb → ∀ (D : D7), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → GlobalTheory.SplitCoef.OSplit D → ∀ i : D.nd.Loc,
    ZDecomp D.nd i → Live D.nd i → ∃ S : Finset ℂ, Chosen D.nd D.naut i ↑S := by
  intro hC D hP hO i hZ hL
  classical
  obtain ⟨rep, ρ, hG, hS⟩ := _root_.GlobalTheory.AbsoluteIrreducibilityOfTraceSpan.setting_of_live_alt_alt hC D hP hO i hZ hL
  obtain ⟨g0, hg0⟩ := exists_wild_inertia_cyclotomic_generator D i
  have hcont : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.RepCont D.nd i rep := fun x => (hG x).1
  have ha := (GlobalTheory.ConsExists.consExist D.nd i rep ρ (D.nd.O i) (D.nd.T i) rep ρ (D.nd.chi i) hcont
    (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.isEnlargement_self D.nd i rep ρ) hS).1
  have hch : ∀ π : D.nd.Z i, ∃ q : (D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)) ×
      (D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)) ×
      (D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)),
      GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsChoice D.R.t (D.nd.T i) rep ρ (D.nd.chi i) π g0 0 q.1 q.2.1 q.2.2 := fun π => by
    obtain ⟨eB, e1, X0, h⟩ := ha π π.2 g0 hg0.1 0
    exact ⟨(eB, e1, X0), h⟩
  choose q hq using hch
  refine ⟨Finset.univ.biUnion fun π : D.nd.Z i => Finset.univ.biUnion fun x : D.nd.X i =>
    ((GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.blockPol ((q π).1 x) ((q π).2.2 x)).map (iotaO D.nd D.naut i)).roots.toFinset,
    rep, ρ, hG, hS, fun π hπ => ?_⟩
  refine ⟨g0, 0, (q ⟨π, hπ⟩).1, (q ⟨π, hπ⟩).2.1, (q ⟨π, hπ⟩).2.2, hg0, hq ⟨π, hπ⟩, fun x => ?_⟩
  obtain ⟨hm, hd⟩ := blockPol_iota D i hS (hq ⟨π, hπ⟩) x
  obtain ⟨α, hα, he⟩ := exists_fin_roots hm hd
  refine ⟨α, fun c => Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨⟨π, hπ⟩, Finset.mem_univ _,
    Finset.mem_biUnion.2 ⟨x, Finset.mem_univ _, Multiset.mem_toFinset.2 (hα c)⟩⟩), he⟩
end GlobalTheory.OChoose
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_chosen_of_cheb_oSplit : GlobalTheory.TwSys.Cheb → ∀ (D : D7), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → GlobalTheory.SplitCoef.OSplit D → ∀ i : D.nd.Loc, ZDecomp D.nd i → Live D.nd i → ∃ S : Finset ℂ, Chosen D.nd D.naut i ↑S := by
  atlas_forward_decl _root_.GlobalTheory.OChoose.oChoose_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.CoefDuty.TakenLarge
set_option maxHeartbeats 4000000 in
theorem evO_takenAll_alt : GlobalTheory.TwSys.Cheb → HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → _root_.GlobalTheory.CoefDuty.AutomorphicSideExists A M C tp.tup → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup (fun D' => _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D' ∧ GlobalTheory.SplitCoef.OSplit D' ∧ ∀ i, ZDecomp D'.nd i) → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup TakenAll := by
  intro hCh hHS D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hstar hE hsplit hCS2 hB hQ
  classical
  obtain ⟨bigA, hA⟩ := hQ
  obtain ⟨L₀, hL₀⟩ := hB bigA
  have hQ₀ := hA L₀ hL₀
  obtain ⟨big₁, h₁⟩ :=
    _root_.GlobalTheory.T.side_eigen_integrality_alt hHS D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hstar hE hsplit hCS2 bigA L₀ hL₀
  have hc₀ := _root_.GlobalTheory.T.contains_after_localization_alt D cf jE A M C tp.tup bigA L₀ hL₀
  let S0 : L₀.X.nd.Loc → Finset ℂ := fun i =>
    if h : ∃ S : Finset ℂ, Chosen (withLoc L₀).nd (withLoc L₀).naut i ↑S then h.choose else ∅
  let big : D.what₂.places.Pl → Finset ℂ := fun w =>
    big₁ w ∪ (Finset.range (D.R.m + 1)).biUnion (fun j => (L₀.X.nd.locs j w).biUnion S0)
  refine ⟨big, fun L₁ hL₁ => ?_⟩
  have hL₁' : _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₁ L₁ :=
    (_root_.GlobalTheory.T.eventually_conjunction_mono_alt D cf jE A M C tp.tup (fun _ => True) (fun _ => True)).2.2.2 big₁ big L₁
      (fun w => Finset.subset_union_left) hL₁
  have hc₁ := _root_.GlobalTheory.T.contains_after_localization_alt D cf jE A M C tp.tup big L₁ hL₁
  intro i₁ hlive₁
  obtain ⟨i₀, hw, ⟨e⟩⟩ := h₁ L₁ hL₁' i₁
  have hc₀i := hc₀ i₀
  have hc₁i := hc₁ i₁
  have hgood₀ : ∃ r, GoodR L₀.lay.fixZ.nd i₀ r := hc₀i.2.2.2.2.2.1.1 (hQ₀.1 i₀).1.2
  have hZ₀ : ZDecomp L₀.lay.fixZ.nd i₀ := hc₀i.2.2.2.1.1 (hQ₀.2.2 i₀)
  have hlive₀ : Live L₀.lay.fixZ.nd i₀ :=
    GlobalTheory.T.irreducibleResidualPoint_descends_coefficientExtension hCh _ _ _ _ i₀ i₁ e hgood₀ hZ₀ (hc₁i.2.2.1.1 hlive₁)
  have hex : ∃ S : Finset ℂ, Chosen (withLoc L₀).nd (withLoc L₀).naut i₀ ↑S :=
    _root_.GlobalTheory.T.exists_finset_chosen_of_cheb_oSplit hCh (withLoc L₀) hQ₀.1 hQ₀.2.1 i₀ (hQ₀.2.2 i₀) (hc₀i.2.2.1.2 hlive₀)
  have hch : Chosen (withLoc L₀).nd (withLoc L₀).naut i₀ ↑(S0 i₀) := by
    simp only [S0, dif_pos hex]
    exact hex.choose_spec
  have hch' := (hc₀i.2.2.2.2.1 _).1 hch
  have hsub : S0 i₀ ⊆ big (L₁.X.nd.w i₁) := by
    intro z hz
    refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨L₀.X.nd.j i₀, ?_, Finset.mem_biUnion.2 ⟨i₀, ?_, hz⟩⟩)
    · exact Finset.mem_range.2 (Nat.lt_succ_of_le (L₀.X.nd.j_range i₀).2)
    · exact (L₀.X.nd.locs_mem _ _ _).2 ⟨rfl, hw⟩
  have hcont : Contains L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ ↑(S0 i₀) := fun z hz => hc₁i.2.1 z (hsub hz)
  exact (hc₁i.2.2.2.2.2.2).2 (GlobalTheory.T.exists_coefRingTaken_of_localisationCoefficientExtension _ _ _ _ i₀ i₁ e _ hch' hcont)
end GlobalTheory.CoefDuty.TakenLarge
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_eigen_hecke_match_alt : GlobalTheory.TwSys.Cheb → HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → _root_.GlobalTheory.CoefDuty.AutomorphicSideExists A M C tp.tup → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup (fun D' => _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D' ∧ GlobalTheory.SplitCoef.OSplit D' ∧ ∀ i, ZDecomp D'.nd i) → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup TakenAll := by
  atlas_forward_decl _root_.GlobalTheory.CoefDuty.TakenLarge.evO_takenAll_alt
end
end
