import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCanonicalModuleSuccessor
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowsAOfJumpCount
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralLocalStableIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySizesCongruencesHostFactsColumnChoices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTiedRealizationPlace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsTerTer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsTerBis

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.ZetaSer

theorem coeffRings_contain_rootsOfUnity_of_groupOrder (D : D7) (h : RootsLL D) : GlobalTheory.PendOf.CoeffRingsHaveRootsOfUnity D := by
  obtain ⟨ζ, hζ⟩ := h
  intro i
  have hpos := D.what₂.restRowsFiniteGroupCard_pos
  have hz : IsPrimitiveRoot (D.nd.embK i ζ) D.what₂.restRowsFiniteGroupCard := hζ.map_of_injective (D.nd.embK i).injective
  have hint : IsIntegral (D.nd.O i) (D.nd.embK i ζ) := ⟨Polynomial.X ^ D.what₂.restRowsFiniteGroupCard - Polynomial.C 1,
    Polynomial.monic_X_pow_sub_C 1 hpos.ne', by simp [hz.pow_eq_one]⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨y, ?_⟩
  rw [← hy] at hz
  exact hz.of_map_of_injective (IsFractionRing.injective _ _)

theorem trace_mem_fieldRange {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {L : Type} [Field L] (e : L →+* ℂ) {n : ℕ} (hn : 0 < n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (f : Module.End ℂ V) (hf : f ^ n = 1) : LinearMap.trace ℂ V f ∈ e.fieldRange := by
  classical
  let b := Module.finBasis ℂ V
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace_eq_sum_roots_charpoly]
  refine multiset_sum_mem _ fun μ hμ => ?_
  have hroot : (LinearMap.charpoly f).IsRoot μ := by
    rw [← LinearMap.charpoly_toMatrix f b]
    exact (Polynomial.mem_roots'.mp hμ).2
  obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).2 hroot).exists_hasEigenvector
  have hpow : μ ^ n = 1 := by
    have h1 := hv.pow_apply n
    rw [hf, Module.End.one_apply] at h1
    have h2 : (μ ^ n - 1) • v = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv.2)
  have hζc := hζ.map_of_injective e.injective
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨j, -, hj⟩ := hζc.eq_pow_of_pow_eq_one hpow
  exact ⟨ζ ^ j, by rw [map_pow, hj]⟩

end GlobalTheory.ZetaSer

namespace GlobalTheory.ZetaSer

theorem card_GL_residue_typePrime_dvd_card_typeGroup (D : D7) (k : Fin 2) :
    Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) ∣ D.what₂.restRowsFiniteGroupCard := by
  rw [D.nd.restN_card_levelGroup_eq]
  have hf : D.R.f ≠ 0 := by
    unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n
    positivity
  exact (dvd_pow_self _ hf).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ k))

theorem coeff_zIdem_mem {Γ : Type} [Group Γ] [Fintype Γ] {L : Type} [Field L] (e : L →+* ℂ) {n : ℕ} (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (hΓ : Nat.card Γ ∣ n) (τ : FDRep ℂ Γ) (γ : Γ) :
    (Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ).coeff γ ∈ e.fieldRange := by
  rw [Formalism.IrreducibleCountingLemmas.TYPES.zIdem_coeff]
  refine mul_mem (div_mem (natCast_mem _ _) (natCast_mem _ _)) (trace_mem_fieldRange e hn hζ _ ?_)
  obtain ⟨c, hc⟩ := hΓ
  rw [← map_pow, hc, pow_mul, pow_card_eq_one', one_pow, map_one]

theorem serLL_of_rootsLL (D : D7) (h : RootsLL D) (G : GrpSide D) : GlobalTheory.PendOf.SerLL D := by
  obtain ⟨ζ, hζ⟩ := h
  intro k f γ
  apply RingHom.mem_fieldRange.mp
  rw [G.eSer_def k f]
  unfold eSerO
  refine finsum_induction (fun x : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))) => x.coeff γ ∈ D.what₂.embLL.fieldRange) ?_ ?_ fun z => ?_
  · simp
  · intro x y hx hy
    simpa using add_mem hx hy
  · refine finsum_induction (fun x : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))) => x.coeff γ ∈ D.what₂.embLL.fieldRange) ?_ ?_ fun hz => ?_
    · simp
    · intro x y hx hy
      simpa using add_mem hx hy
    · obtain ⟨τ, -, rfl, -⟩ := hz
      exact coeff_zIdem_mem _ D.what₂.restRowsFiniteGroupCard_pos hζ (card_GL_residue_typePrime_dvd_card_typeGroup D k) τ γ

theorem rootsOfUnity_and_seriesIdempotent_rational : ∀ D : D7, RootsLL D → GlobalTheory.PendOf.CoeffRingsHaveRootsOfUnity D ∧ (GrpSide D → GlobalTheory.PendOf.SerLL D) :=
  fun D h => ⟨coeffRings_contain_rootsOfUnity_of_groupOrder D h, serLL_of_rootsLL D h⟩

end GlobalTheory.ZetaSer
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.HeightCounting.Up.PendLayer

variable {hL : GlobalTheory.Published.LocalLanglandsGL}

theorem atMem_imp {p q : LayP hL} (h : AtMem hL p)
    (hpq : ∀ K B f T w Z Wt p0 t nch n c, p K B f T w Z Wt p0 t nch n c → q K B f T w Z Wt p0 t nch n c) : AtMem hL q :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c a b d =>
    hpq _ B f T w Z Wt p0 t nch n c (H kp w Z Wt p0 t nch n xd c a b d)

theorem atMem_and {p q : LayP hL} (h : AtMem hL p) (h' : AtMem hL q) :
    AtMem hL fun K B f T w Z Wt p0 t nch n c => p K B f T w Z Wt p0 t nch n c ∧ q K B f T w Z Wt p0 t nch n c :=
  EvG.imp (EvG.inter h h') fun _ _ _ _ _ hK => large₂.imp (large₂.inter hK.1 hK.2) fun _ _ _ _ H kp w Z Wt p0 t nch n xd c a b d =>
    ⟨H.1 kp w Z Wt p0 t nch n xd c a b d, H.2 kp w Z Wt p0 t nch n xd c a b d⟩

theorem atMem_of_evLgG {q : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), w.Lt → Prop}
    (h : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), q B f T w Z) :
    AtMem hL fun _ B f T w Z _ _ _ _ _ _ => q B f T w Z :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun _ _ T _ H kp w Z _ _ _ _ _ _ _ _ _ _ => H kp T w Z

theorem at_pin (hP : PrN) (hW : GlobalTheory.Published.DepthZeroWild) (hS : GlobalTheory.Published.DepthZeroSupport) (D : D7) (P : GlobalTheory.NPin.Pin hL D)
    (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (hX : GlobalTheory.NJoin.Agree X P.M P.rep) (hJ : JumpsCard D.nd D.naut)
    (hlab : GlobalTheory.PendOf.LabAll D P.T) (hgreen : GlobalTheory.PendOf.GreenLab P.ty.grp) (hchi : ChiTOk D P.cf)
    (hcen : CenLoc D P.M) (hzl : GlobalTheory.PendOf.ZLStable D) (hci : GlobalTheory.PendOf.CenInt D) (hroots : RootsLL D) :
    PairedCharacterCondition.tieChi (D := D) ∧ ∃ Q : PairedCharacterCondition.Pend D, PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q := by
  have hrow : ∀ i : D.nd.Loc, Nonempty (GlobalTheory.NPin.RowMod D P.rep (D.nd.j i)) := by
    intro i
    have h1 := (D.nd.j_range i).1
    have h2 := (D.nd.j_range i).2
    obtain ⟨Y, -⟩ := GlobalTheory.RowModCanon.main hP.hc hP.decay hL D P X hX ⟨D.nd.j i - 1, by omega⟩ (D.nd.j i) (by simp; omega)
    exact ⟨Y⟩
  have hA := GlobalTheory.RowsAClose.main hP.what₂ hL D P hJ
  have hZ := GlobalTheory.ZetaSer.rootsOfUnity_and_seriesIdempotent_rational D hroots
  exact ⟨GlobalTheory.TieChiPin.main hP.what₂ hP.dz hL D P hrow hlab hchi,
    GlobalTheory.PinClose.main hP.what₂ hP.dz hW hS hL D P hrow hlab hcen hgreen hchi hA.tie0 hA.a5 hzl hci (hZ.2 P.ty.grp) hZ.1⟩

theorem main : HtCard → PrN → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport → ∀ hL : GlobalTheory.Published.LocalLanglandsGL,
    AtMem hL fun _ _ _ _ w Z _ _ t nch n c => PairedCharacterCondition.tieChi (D := w.D Z) ∧ ∃ Q : PairedCharacterCondition.Pend (w.D Z), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q := by
  intro hH hP hW hS hL
  have h1 := atMem_and (GlobalTheory.T.central_local_stable_integral hL) (atMem_and (GlobalTheory.HeightCounting.JumpsAt.jumpsCard_atMem hH hL)
    (atMem_and (GlobalTheory.HeightCounting.Up.tied_of_layer hP hL) (atMem_of_evLgG (hL := hL) GlobalTheory.HeightCounting.Up.sizes_host_at_record)))
  refine atMem_imp h1 fun K B f T w Z Wt p0 t nch n c h => ?_
  obtain ⟨⟨hcen, hzl, hci⟩, hJ, ⟨X, hpin, -⟩, -, -, hroots, -⟩ := h
  have hM : X.P.M = c.a.all.gal.mt := hpin.M_eq
  exact at_pin hP hW hS (w.D Z) X.P X.X X.agree hJ hpin.lab hpin.green hpin.chiT (hM ▸ hcen) hzl hci hroots

end GlobalTheory.HeightCounting.Up.PendLayer

end
end
