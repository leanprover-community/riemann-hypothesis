import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.GrowthWeightBounds.WeightExtensions.WeightExtensionExistence.WeightExD
import Development.WeilBound.CoreStatements.PadicHodgeComparison.UniqueSaturation.DescentOffPrescribedPlaces
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ExistsEigv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PeakCone
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadSplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivContraLocComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentsThetaPull
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.GlobFix

section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open GlobalTheory.SplitPts

namespace GlobalTheory.CompanionTheory.CompConjPlace

section Rep

variable {G X V : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]

theorem exists_embed_fin (ρ : Representation ℂ G X) (τ : Representation ℂ G V) (hτ : τ.IsIrreducible) :
    ∀ (r : ℕ) (N : Submodule ℂ X) (T : Fin r → X →ₗ[ℂ] V), (∀ g, ∀ z ∈ N, ρ g z ∈ N) → N ≠ ⊥ →
      (∀ j g x, T j (ρ g x) = τ g (T j x)) → (∀ z ∈ N, (∀ j, T j z = 0) → z = 0) →
      ∃ Φ : V →ₗ[ℂ] X, Φ ≠ 0 ∧ ∀ g v, Φ (τ g v) = ρ g (Φ v) := by
  intro r
  induction r with
  | zero =>
    intro N T _ hne _ hinj
    exact absurd ((Submodule.eq_bot_iff N).2 fun z hz => hinj z hz fun j => j.elim0) hne
  | succ r ih =>
    intro N T hN hne hT hinj
    by_cases hK : N ⊓ LinearMap.ker (T 0) = ⊥
    · obtain ⟨-, hirr⟩ := (GlobalTheory.CuspRep.isIrreducible_iff τ).1 hτ
      let S : N →ₗ[ℂ] V := (T 0).comp N.subtype
      have hker : ∀ z : N, S z = 0 → z = 0 := fun z hz => by
        have h : (z : X) ∈ N ⊓ LinearMap.ker (T 0) := ⟨z.2, hz⟩
        rw [hK] at h
        exact Subtype.ext h
      have hSinj : Function.Injective S := (injective_iff_map_eq_zero S).2 hker
      obtain ⟨z₀, hz₀, hz₀'⟩ := (Submodule.ne_bot_iff N).1 hne
      have hrange : LinearMap.range S = ⊤ := by
        refine (hirr (LinearMap.range S) ?_).resolve_left fun h => ?_
        · rintro g _ ⟨z, rfl⟩
          exact ⟨⟨ρ g z, hN g z z.2⟩, hT 0 g z⟩
        · have h0 : S ⟨z₀, hz₀⟩ = 0 := (Submodule.mem_bot ℂ).1 (h ▸ LinearMap.mem_range_self S ⟨z₀, hz₀⟩)
          exact hz₀' (congrArg Subtype.val (hker _ h0))
      let e : N ≃ₗ[ℂ] V := LinearEquiv.ofBijective S ⟨hSinj, LinearMap.range_eq_top.1 hrange⟩
      refine ⟨N.subtype ∘ₗ e.symm.toLinearMap, fun h => hz₀' ?_, fun g v => ?_⟩
      · have h1 := LinearMap.congr_fun h (e ⟨z₀, hz₀⟩)
        simpa using h1
      · have h1 : e.symm (τ g v) = ⟨ρ g (e.symm v), hN g _ (e.symm v).2⟩ := by
          rw [LinearEquiv.symm_apply_eq]
          change τ g v = T 0 (ρ g (e.symm v))
          rw [hT]
          exact congrArg (τ g) (e.apply_symm_apply v).symm
        change ((e.symm (τ g v) : N) : X) = _
        rw [h1]
        rfl
    · refine ih (N ⊓ LinearMap.ker (T 0)) (fun j => T j.succ) (fun g z hz => ⟨hN g z hz.1, ?_⟩) hK
        (fun j => hT j.succ) fun z hz h => hinj z hz.1 fun j => ?_
      · change T 0 (ρ g z) = 0
        rw [hT, show T 0 z = 0 from hz.2, map_zero]
      · refine Fin.cases hz.2 h j

theorem exists_embed (ρ : Representation ℂ G X) (τ : Representation ℂ G V) (hτ : τ.IsIrreducible) {ι : Type*}
    (T : ι → X →ₗ[ℂ] V) (hT : ∀ i g x, T i (ρ g x) = τ g (T i x)) (hinj : ∀ x, (∀ i, T i x = 0) → x = 0)
    (y : X) (hy : y ≠ 0) (hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun i => T i y))) :
    ∃ Φ : V →ₗ[ℂ] X, Φ ≠ 0 ∧ ∀ g v, Φ (τ g v) = ρ g (Φ v) := by
  classical
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1
    (Module.Finite.iff_fg.1 hfd)
  have hidx : ∀ j : Fin s.card, ∃ i, T i y = (s.equivFin.symm j : V) := fun j =>
    hs (s.equivFin.symm j).2
  choose idx hidx using hidx
  have hmem : ∀ i, T i y ∈ Submodule.span ℂ (Set.range fun j => T (idx j) y) := fun i => by
    have h1 : T i y ∈ Submodule.span ℂ (s : Set V) := hspan ▸ Submodule.subset_span ⟨i, rfl⟩
    refine Submodule.span_mono ?_ h1
    intro x hx
    refine ⟨s.equivFin ⟨x, hx⟩, ?_⟩
    simp [hidx]
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hmem i)
  let N : Submodule ℂ X := ⨅ i, LinearMap.ker (T i - ∑ j, c i j • T (idx j))
  have hNmem : ∀ z, z ∈ N ↔ ∀ i, T i z = ∑ j, c i j • T (idx j) z := fun z => by
    simp [N, Submodule.mem_iInf, LinearMap.sum_apply, sub_eq_zero]
  refine exists_embed_fin ρ τ hτ s.card N (fun j => T (idx j)) (fun g z hz => ?_) ?_ (fun j => hT _)
    fun z hz h => hinj z fun i => ?_
  · rw [hNmem] at hz ⊢
    intro i
    simp only [hT, hz i, map_sum, map_smul]
  · refine (Submodule.ne_bot_iff N).2 ⟨y, (hNmem y).2 fun i => (hc i).symm, hy⟩
  · rw [(hNmem z).1 hz i]
    simp [h]

end Rep

section Global

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E}

abbrev sLoc (n : ℕ) (w : Pl E) : GLw n (conjSrc (conjE E) w) →* GLw n w :=
  GeneralLinearGroup.map (conjLoc (conjE E) w)

theorem continuous_sLoc (w : Pl E) : Continuous (sLoc n w) :=
  Continuous.units_map _ (continuous_id.matrix_map (conjLoc_spec _ w).1)

theorem surjective_invTranspose (R : Type) [CommRing R] : Function.Surjective (invTranspose n R) :=
  fun g => ⟨invTranspose n R g, GlobalTheory.GelfandKazhdan.invTranspose_invTranspose n R g⟩

def conjRep (τ : SmIrr (GLw n w)) : SmIrr (GLw n (conjSrc (conjE E) w)) where
  V := τ.V
  ρ := τ.ρ.comp (sLoc n w)
  smooth x := (τ.smooth x).preimage (continuous_sLoc w)
  irred := GlobalTheory.ConjPairLoc.irred_comp _ _ (GlobalTheory.ConjPairLoc.map_conjLoc_surjective w) τ.irred

def conjDual (τ : SmIrr (GLw n w)) : SmIrr (GLw n (conjSrc (conjE E) w)) where
  V := τ.V
  ρ := (conjRep τ).ρ.comp (invTranspose n _)
  smooth x := ((conjRep τ).smooth x).preimage (GlobalTheory.GelfandKazhdan.continuous_invTranspose n _)
  irred := GlobalTheory.ConjPairLoc.irred_comp _ _ (surjective_invTranspose _) (conjRep τ).irred

theorem isLocComp_conjDual (π : CuspSub E n) (hπ : GlobalTheory.ContraPair.DualIsConj π) {τ : SmIrr (GLw n w)}
    (hτ : π.IsLocComp w τ) : π.IsLocComp (conjSrc (conjE E) w) (conjDual τ) := by
  obtain ⟨B, hL, -, hB, -⟩ := hπ
  have hadm : ∀ σ : SmIrr (GLw n (conjSrc (conjE E) w)), IsAdmissible σ.ρ := fun σ =>
    PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top _ n σ.V σ.ρ σ.smooth σ.irred
  obtain ⟨e⟩ := GlobalTheory.GelfandKazhdan.equiv_contra _ n (conjRep τ).V (conjRep τ).ρ (hadm _) (conjRep τ).irred
  have hloc : IsLocCompGL π.V w τ := by
    obtain ⟨f, h0, hf⟩ := hτ
    refine ⟨π.V.subtype ∘ₗ f, fun h => h0 (LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun h v)),
      fun v => (f v).2, fun g v => ?_⟩
    exact congrArg Subtype.val (hf g v)
  let Bf (f : GlobalTheory.LocDual.Maps π.V w τ) : (conjRep τ).V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ :=
    B.flip.comp (f.1.codRestrict π.V f.2.1)
  have hBf : ∀ f g a ψ, Bf f ((conjRep τ).ρ g a) (π.locRep (conjSrc (conjE E) w) g ψ) = Bf f a ψ := by
    intro f g a ψ
    have h1 : f.1.codRestrict π.V f.2.1 ((conjRep τ).ρ g a) =
        π.op (.fin (GeneralLinearGroup.map (conjFin (conjE E)) (locGL E n _ g))) (f.1.codRestrict π.V f.2.1 a) := by
      refine Subtype.ext ?_
      rw [GlobalTheory.ConjPairLoc.conjFin_locGL]
      exact f.2.2 _ a
    change B (π.locRep _ g ψ) (f.1.codRestrict π.V f.2.1 ((conjRep τ).ρ g a)) = B ψ (f.1.codRestrict π.V f.2.1 a)
    rw [h1, CuspSub.locRep_eq]
    exact hB _ ψ _
  let P (f : GlobalTheory.LocDual.Maps π.V w τ) := GlobalTheory.InvPairing.pairMap (conjRep τ).ρ (π.isSmooth_locRep _) (Bf f) (hBf f)
  let T (f : GlobalTheory.LocDual.Maps π.V w τ) : π.V →ₗ[ℂ] (conjDual τ).V := e.symm.toLinearEquiv.toLinearMap ∘ₗ (P f).toLinearMap
  have hT : ∀ f g ψ, T f (π.locRep _ g ψ) = (conjDual τ).ρ g (T f ψ) := fun f g ψ => by
    have h1 := LinearMap.congr_fun ((P f).isIntertwining' g) ψ
    change e.symm.toLinearEquiv ((P f).toLinearMap (π.locRep _ g ψ)) = _
    rw [show (P f).toLinearMap (π.locRep _ g ψ) = _ from h1]
    exact GlobalTheory.ConjPairLoc.equiv_apply e.symm g _
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff π.V).1 π.ne_bot
  obtain ⟨K, hKo, hKc, hK⟩ := GlobalTheory.SqIntUnit.compactOpen_basis _ n _
    ((π.isSmooth_locRep (conjSrc (conjE E) w) ⟨y, hy⟩).mem_nhds (by simp))
  haveI := (hadm (conjDual τ)).2 K hKo hKc
  have hle : Submodule.span ℂ (Set.range fun f => T f ⟨y, hy⟩) ≤ fixed (conjDual τ).ρ K := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, rfl⟩
    refine LocEx.mem_fix.2 fun k hk => ?_
    change (conjDual τ).ρ k (T f ⟨y, hy⟩) = T f ⟨y, hy⟩
    rw [← hT, show π.locRep _ k ⟨y, hy⟩ = ⟨y, hy⟩ from hK hk]
  have hfd := Submodule.finiteDimensional_of_le hle
  have hinj : ∀ ψ, (∀ f, T f ψ = 0) → ψ = 0 := fun ψ hψ => by
    by_contra hne
    have hβ : B ψ ≠ 0 := fun h => hne (hL ψ fun φ => LinearMap.congr_fun h φ)
    obtain ⟨f, hf⟩ := GlobalTheory.LocDual.exists_comp_ne_zero π.V π.stable π.irred w τ hloc (B ψ) hβ
    refine hf (LinearMap.ext fun a => ?_)
    have h1 : (P f).toLinearMap ψ = 0 := e.symm.toLinearEquiv.map_eq_zero_iff.1 (hψ f)
    exact LinearMap.congr_fun (congrArg Subtype.val h1) a
  obtain ⟨Φ, h0, hΦ⟩ := exists_embed (π.locRep _) (conjDual τ).ρ (conjDual τ).irred T hT hinj ⟨y, hy⟩
    (fun h => hy0 (congrArg Subtype.val h)) hfd
  exact ⟨Φ, h0, hΦ⟩

end Global

end GlobalTheory.CompanionTheory.CompConjPlace

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B
open PositivityTheory.Rg.BcB.Desc PositivityTheory.AutomorphicGaloisHodgeTate.D
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.FrE PositivityTheory.Rg.BcB.F.FrE.FrameLocalData

namespace GlobalTheory.CompanionTheory.LFixDPf

attribute [local instance] borelG borelF borelA borelH GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

open PositivityTheory.Rg.BcB.F.F5.Bo PositivityTheory.Rg.BcB.F.F5.Bo.GlobalFixedVectorsAlt in

theorem exists_fixAll_cusp (π : CuspSub E n) (Kf : ∀ w : Pl E, Subgroup (GLw n w))
    (hc : ∀ w, IsCompact (Kf w : Set (GLw n w)))
    (hv : ∀ w, ∃ φ : π.V, φ ≠ 0 ∧ φ ∈ fixed (π.locRep w) (Kf w)) (S : Finset (Pl E)) :
    ∀ ψ : π.V, ψ ≠ 0 → (∀ u ∉ S, FixAt Kf u ψ.1) → ∃ χ : π.V, χ ≠ 0 ∧ ∀ u, FixAt Kf u χ.1 := by
  induction S using Finset.induction_on with
  | empty => exact fun ψ h0 hF => ⟨ψ, h0, fun u => hF u (Finset.notMem_empty u)⟩
  | insert w S hwS ih =>
    intro ψ h0 hF
    let Y : Submodule ℂ π.V :=
      { carrier := {χ | ∀ u ∉ insert w S, FixAt Kf u χ.1}
        add_mem' := fun {a b} ha hb u hu k hk => by
          show finRep E n _ (a.1 + b.1) = a.1 + b.1
          rw [map_add, ha u hu k hk, hb u hu k hk]
        zero_mem' := fun u _ k _ => map_zero _
        smul_mem' := fun c a ha u hu k hk => by
          show finRep E n _ (c • a.1) = c • a.1
          rw [map_smul, ha u hu k hk] }
    have hY : ∀ g, ∀ y ∈ Y, π.locRep w g y ∈ Y := fun g y hy u hu =>
      fixAt_locGL (fun e => hu (by rw [e]; exact Finset.mem_insert_self w S)) (hy u hu) g
    obtain ⟨φ, hφ0, hφ⟩ := hv w
    have hne : Y ⊓ fixed (π.locRep w) (Kf w) ≠ ⊥ := fun h => h0 (by
      have h1 := GlobalTheory.CuspRep.LocEx.eq_bot_of_fixed π w (hc w) hφ0 hφ Y hY h
      have h2 : ψ ∈ Y := hF
      rw [h1] at h2
      exact (Submodule.mem_bot ℂ).1 h2)
    obtain ⟨y, ⟨hy1, hy2⟩, hy0⟩ := (Submodule.ne_bot_iff _).1 hne
    refine ih y hy0 fun u hu => ?_
    by_cases e : u = w
    · subst e
      exact fun k hk => congrArg Subtype.val (GlobalTheory.CuspRep.LocEx.mem_fix.1 hy2 k hk)
    · exact hy1 u (by simp [e, hu])

open PositivityTheory.Rg.BcB.F.F5.Bo PositivityTheory.Rg.BcB.F.F5.Bo.GlobalFixedVectorsAlt in

theorem exists_global_fix (π : CuspSub E n) (Kf : ∀ w : Pl E, Subgroup (GLw n w))
    (hc : ∀ w, IsCompact (Kf w : Set (GLw n w)))
    (hv : ∀ w, ∃ φ : π.V, φ ≠ 0 ∧ φ ∈ fixed (π.locRep w) (Kf w))
    (hcof : ∀ᶠ w in Filter.cofinite, Kf w = GlobalTheory.LFun.KGL w n) :
    ∃ ψ ∈ π.V, ψ ≠ 0 ∧ ∀ v ∈ globL Kf, finRep E n v ψ = ψ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have hev : ∀ᶠ w in Filter.cofinite, FixAt Kf w φ := by
    filter_upwards [hcof, GlobalTheory.CuspRep.LocSph.eventually_mem ((π.cusp φ hφ).1.level.mem_nhds (by simp))] with w h1 h2
    intro k hk
    rw [h1] at hk
    obtain ⟨g, rfl⟩ := hk
    exact h2 g
  have hfin := Filter.eventually_cofinite.1 hev
  obtain ⟨χ, hχ0, hχ⟩ := exists_fixAll_cusp π Kf hc hv hfin.toFinset ⟨φ, hφ⟩
    (fun e => h0 (congrArg Subtype.val e)) fun u hu => by simpa using hu
  exact ⟨χ.1, χ.2, fun e => hχ0 (Subtype.ext e), fix_of_fixAll hcof (π.cusp χ.1 χ.2).1 hχ⟩

section Conj

open GlobalTheory.SplitPts GlobalTheory.CompanionTheory.CompConjPlace GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws

def thAt (n : ℕ) (w u : Pl E) : GLw n w →* GLw n u :=
  (GeneralLinearGroup.map (pLoc E u)).comp ((thF E n).comp (locGL E n w))

theorem map_pLoc_thF (u : Pl E) (k : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map (pLoc E u) (thF E n k) = PhiU n _ * invT n _ (GeneralLinearGroup.map (conjLoc (conjE E) u)
      (GeneralLinearGroup.map (pLoc E (conjSrc (conjE E) u)) k)) * (PhiU n _)⁻¹ :=
  map_thetaGL (pLoc E u) _ (pLoc E _) (conjLoc (conjE E) u) (fun _ => rfl) k

theorem thAt_apply (u : Pl E) (g : GLw n (conjSrc (conjE E) u)) :
    thAt n (conjSrc (conjE E) u) u g =
      PhiU n _ * invT n _ (GeneralLinearGroup.map (conjLoc (conjE E) u) g) * (PhiU n _)⁻¹ := by
  show GeneralLinearGroup.map (pLoc E u) (thF E n (locGL E n _ g)) = _
  rw [map_pLoc_thF, pLoc_locGL]

theorem map_pLoc_thF_eq (u : Pl E) (k : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map (pLoc E u) (thF E n k) =
      thAt n (conjSrc (conjE E) u) u (GeneralLinearGroup.map (pLoc E _) k) := by
  rw [thAt_apply, map_pLoc_thF]

theorem exists_fixed_conj (π : CuspSub E n) (hd : GlobalTheory.ContraPair.DualIsConj π) {u : Pl E} {τ : SmIrr (GLw n u)}
    (hτ : π.IsLocComp u τ) (M : Subgroup (GLw n u)) {y : τ.V} (hy : y ∈ fixed τ.ρ M) (h0 : y ≠ 0) :
    ∃ φ : π.V, φ ≠ 0 ∧ φ ∈ fixed (π.locRep (conjSrc (conjE E) u)) (M.comap (thAt n (conjSrc (conjE E) u) u)) := by
  obtain ⟨f, hf0, hf⟩ := isLocComp_conjDual π hd hτ
  have hi := GlobalTheory.BcSpehCompare.injective_of_irred (conjDual τ).irred (τ := fun g => π.locRep _ g)
    (fun _ => map_zero _) hf0 hf
  set P : GLw n u := PhiU n _ with hP
  have hy' : τ.ρ P⁻¹ y ≠ 0 := fun e => h0 (by
    have h1 : τ.ρ P (τ.ρ P⁻¹ y) = y := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← h1, e, map_zero])
  refine ⟨f (τ.ρ P⁻¹ y), (map_ne_zero_iff f hi).2 hy', GlobalTheory.CuspRep.LocEx.mem_fix.2 fun g hg => ?_⟩
  refine (hf g (τ.ρ P⁻¹ y)).symm.trans (congrArg f ?_)
  have h2 := GlobalTheory.CuspRep.LocEx.mem_fix.1 hy _ (Subgroup.mem_comap.1 hg)
  rw [thAt_apply] at h2
  have e : (conjDual τ).ρ g = τ.ρ (invT n _ (GeneralLinearGroup.map (conjLoc (conjE E) u) g)) := rfl
  show (conjDual τ).ρ g (τ.ρ P⁻¹ y) = τ.ρ P⁻¹ y
  rw [e]
  generalize invT n _ (GeneralLinearGroup.map (conjLoc (conjE E) u) g) = j at h2
  have key : j * P⁻¹ = P⁻¹ * (P * j * P⁻¹) := by group
  calc τ.ρ j (τ.ρ P⁻¹ y) = τ.ρ (j * P⁻¹) y := by rw [map_mul]; rfl
    _ = τ.ρ (P⁻¹ * (P * j * P⁻¹)) y := by rw [key]
    _ = τ.ρ P⁻¹ (τ.ρ (P * j * P⁻¹) y) := by rw [map_mul]; rfl
    _ = τ.ρ P⁻¹ y := by rw [h2]

end Conj

section Int

open GlobalTheory.SplitPts GlobalTheory.CompanionTheory.CompConjPlace GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws

theorem mem_KGL_map_conj (u : Pl E) (g : GLw n (conjSrc (conjE E) u)) :
    GeneralLinearGroup.map (conjLoc (conjE E) u) g ∈ GlobalTheory.LFun.KGL u n ↔ g ∈ GlobalTheory.LFun.KGL (conjSrc (conjE E) u) n := by
  have hv : ∀ x : (conjSrc (conjE E) u).adicCompletion E,
      conjLoc (conjE E) u x ∈ u.adicCompletionIntegers E ↔ x ∈ (conjSrc (conjE E) u).adicCompletionIntegers E := fun x => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers, (conjLoc_spec (conjE E) u).2.2 x]
  rw [GlobalTheory.AdelicU.mem_GLint_iff, GlobalTheory.AdelicU.mem_GLint_iff]
  refine and_congr (forall₂_congr fun a b => hv _) (forall₂_congr fun a b => ?_)
  rw [← map_inv]
  exact hv _

theorem mem_KGL_invT (u : Pl E) (x : GLw n u) : invT n _ x ∈ GlobalTheory.LFun.KGL u n ↔ x ∈ GlobalTheory.LFun.KGL u n := by
  rw [GlobalTheory.AdelicU.mem_GLint_iff, GlobalTheory.AdelicU.mem_GLint_iff]
  have e1 : ∀ a b, (invT n _ x).val a b = (x⁻¹).val b a := fun _ _ => rfl
  have e2 : ∀ a b, ((invT n _ x)⁻¹).val a b = x.val b a := fun _ _ => rfl
  simp only [e1, e2]
  exact ⟨fun h => ⟨fun a b => h.2 b a, fun a b => h.1 b a⟩, fun h => ⟨fun a b => h.2 b a, fun a b => h.1 b a⟩⟩

end Int

section Int2

open GlobalTheory.SplitPts GlobalTheory.CompanionTheory.CompConjPlace GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws

theorem phiU_mem_KGL (u : Pl E) : PhiU n (u.adicCompletion E) ∈ GlobalTheory.LFun.KGL u n := by
  let p : u.adicCompletionIntegers E →+* u.adicCompletion E := (u.adicCompletionIntegers E).subtype
  have e : GeneralLinearGroup.map p (PhiU n (u.adicCompletionIntegers E)) = PhiU n (u.adicCompletion E) :=
    Units.ext (Matrix.ext fun i k => by
      change p (GlobalTheory.Tw.Phi n _ i k) = GlobalTheory.Tw.Phi n _ i k
      simp [GlobalTheory.Tw.Phi, apply_ite p])
  rw [GlobalTheory.AdelicU.mem_GLint_iff, ← e]
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · exact ((PhiU n (u.adicCompletionIntegers E)).val a b).2
  · rw [← map_inv]
    exact (((PhiU n (u.adicCompletionIntegers E))⁻¹).val a b).2

theorem mem_KGL_thAt (u : Pl E) (g : GLw n (conjSrc (conjE E) u)) :
    thAt n (conjSrc (conjE E) u) u g ∈ GlobalTheory.LFun.KGL u n ↔ g ∈ GlobalTheory.LFun.KGL (conjSrc (conjE E) u) n := by
  have hP := phiU_mem_KGL (n := n) u
  rw [thAt_apply, Subgroup.mul_mem_cancel_right _ (inv_mem hP), Subgroup.mul_mem_cancel_left _ hP, mem_KGL_invT,
    mem_KGL_map_conj]

theorem continuous_thAt (u : Pl E) : Continuous (thAt n (conjSrc (conjE E) u) u) := by
  have e : (thAt n (conjSrc (conjE E) u) u : _ → _) = fun g =>
      PhiU n _ * invT n _ (GeneralLinearGroup.map (conjLoc (conjE E) u) g) * (PhiU n _)⁻¹ := funext (thAt_apply u)
  rw [e]
  have h1 : Continuous (invT n (u.adicCompletion E)) := GlobalTheory.GelfandKazhdan.continuous_invTranspose n _
  exact (continuous_const.mul (h1.comp (continuous_sLoc u))).mul continuous_const

theorem isCompact_comap_thAt (u : Pl E) (M : Subgroup (GLw n u)) (hM : IsCompact (M : Set (GLw n u)))
    (hK : M ≤ GlobalTheory.LFun.KGL u n) :
    IsCompact ((M.comap (thAt n (conjSrc (conjE E) u) u) : Subgroup _) : Set (GLw n (conjSrc (conjE E) u))) :=
  GlobalTheory.BcSpehCompare.isCompact_KGL.of_isClosed_subset (hM.isClosed.preimage (continuous_thAt u))
    fun g hg => (mem_KGL_thAt u g).1 (hK hg)

theorem blk_self (w : Pl E) (x : GLw n w) (z : GLw (n - n) w) (h : n + (n - n) = n) : blk h w (x, z) 0 = x := by
  have he : ∀ i : Fin n, (finSumFinEquiv.trans (finCongr h)).symm i = Sum.inl i := fun i =>
    (Equiv.symm_apply_eq _).2 (Fin.ext (by simp))
  have hM : ∀ X : Matrix (Fin n) (Fin (n - n)) (w.adicCompletion E),
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks x.val (x.val * X) 0 z.val) = x.val := fun X => by
    ext i j
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, he, he]
    rfl
  have hU : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks x.val (x.val * (0 : Matrix (Fin n) (Fin (n - n)) (w.adicCompletion E))) 0 z.val)) := by
    rw [hM]; exact x.isUnit
  exact (dif_pos hU).trans (Units.ext (hM 0))

end Int2

section Main

open GlobalTheory.SplitPts GlobalTheory.CompanionTheory.CompConjPlace GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws
open PositivityTheory.Rg.BcB.F.F5.Bo

def Mlev (d : LocData E n) (w : Pl E) : Subgroup (GLw n w) :=
  if w ∈ d.S₀ then d.K' w else GlobalTheory.LFun.KGL w n

def Kfam (Sec : Set (Pl E)) (d : LocData E n) (w : Pl E) : Subgroup (GLw n w) :=
  if w ∈ Sec then Mlev d w else (Mlev d (conjSrc (conjE E) w)).comap (thAt n w (conjSrc (conjE E) w))

theorem Kfam_of_mem {Sec : Set (Pl E)} (d : LocData E n) {w : Pl E} (hw : w ∈ Sec) : Kfam Sec d w = Mlev d w := if_pos hw

theorem Kfam_of_notMem {Sec : Set (Pl E)} (d : LocData E n) {w u : Pl E} (hw : w ∉ Sec) (h : conjSrc (conjE E) w = u) :
    Kfam Sec d w = (Mlev d u).comap (thAt n w u) := by
  subst h
  exact if_neg hw

theorem exists_conj_of_notMem {Sec : Set (Pl E)} (hSec : IsSection Sec) {w : Pl E} (hw : w ∉ Sec) :
    ∃ u ∈ Sec, IsSplitAt u ∧ w = conjSrc (conjE E) u ∧ conjSrc (conjE E) w = u := by
  obtain ⟨u, ⟨hu, hun⟩, -⟩ := hSec w
  have hne : w ≠ u := fun e => hw (e ▸ hu)
  have hs : IsSplitAt u := ⟨w, hne, hun.symm⟩
  have h1 : w = conjSrc (conjE E) u := ((over_split hs).2.2 w hun.symm).resolve_left hne
  exact ⟨u, hu, hs, h1, by rw [h1, conjSrc_conjSrc_cm]⟩

variable {d : LocData E n}

theorem Mlev_compact (hd : d.Ok) (w : Pl E) : IsCompact (Mlev d w : Set (GLw n w)) ∧ Mlev d w ≤ GlobalTheory.LFun.KGL w n := by
  unfold Mlev
  split_ifs with h
  · obtain ⟨h1, h2, -⟩ := hd.K' w h
    exact ⟨GlobalTheory.BcSpehCompare.isCompact_KGL.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ h1) h2, h2⟩
  · exact ⟨GlobalTheory.BcSpehCompare.isCompact_KGL, le_rfl⟩

theorem fixed_of_comp {π : CuspSub E n} {w : Pl E} {σ : SmIrr (GLw n w)} (h : π.IsLocComp w σ) (M : Subgroup (GLw n w))
    {y : σ.V} (hy : y ∈ fixed σ.ρ M) (h0 : y ≠ 0) : ∃ φ : π.V, φ ≠ 0 ∧ φ ∈ fixed (π.locRep w) M := by
  obtain ⟨f, hf0, hf⟩ := h
  have hi := GlobalTheory.BcSpehCompare.injective_of_irred σ.irred (τ := fun g => π.locRep w g) (fun _ => map_zero _) hf0 hf
  refine ⟨f y, (map_ne_zero_iff f hi).2 h0, GlobalTheory.CuspRep.LocEx.mem_fix.2 fun g hg => ?_⟩
  rw [← hf, GlobalTheory.CuspRep.LocEx.mem_fix.1 hy g hg]

theorem Kfam_eq_of_notMem {Sec : Set (Pl E)} (hSec : IsSection Sec) {w : Pl E}
    (h1 : w ∉ d.S₀) (h2 : conjSrc (conjE E) w ∉ d.S₀) : Kfam Sec d w = GlobalTheory.LFun.KGL w n := by
  by_cases hw : w ∈ Sec
  · rw [Kfam_of_mem d hw, Mlev, if_neg h1]
  · obtain ⟨u, -, -, rfl, e⟩ := exists_conj_of_notMem hSec hw
    rw [Kfam_of_notMem d hw e]
    rw [e] at h2
    ext g
    rw [Subgroup.mem_comap, Mlev, if_neg h2]
    exact mem_KGL_thAt u g

theorem lev_mem {w : Pl E} (hd : d.Ok) (T₀ : d.T = ∅) (B₀ : d.Bad = ∅) {x : GLw n w} {z : GLw (n - n) w}
    (h : (x, z) ∈ d.lev n w) : x ∈ Mlev d w := by
  have hT : w ∉ d.T := by simp [T₀]
  rw [LocData.lev, if_neg hT] at h
  unfold Mlev
  by_cases hs : w ∈ d.S₀
  · rw [if_pos (Finset.mem_union_left _ hs)] at h
    have h1 := (hd.LS n le_rfl w hs _ h).1
    rw [if_pos hs]
    have h2 : blk (Nat.add_sub_of_le le_rfl) w (x, z) 0 ∈ d.K' w := h1
    rwa [blk_self] at h2
  · rw [if_neg (by simp [B₀, hs])] at h
    rw [if_neg hs]
    exact h.1

theorem lev₂_mem {w : Pl E} (hd : d.Ok) (B₀ : d.Bad = ∅) {x : GLw n w} {z : GLw (n - n) w}
    (h : (x, z) ∈ d.lev₂ n w) : x ∈ Mlev d w := by
  rw [LocData.lev₂] at h
  unfold Mlev
  by_cases hs : w ∈ d.S₀
  · rw [if_pos (Finset.mem_union_left _ hs)] at h
    have h1 := (hd.LS n le_rfl w hs _ h).1
    rw [if_pos hs]
    have h2 : blk (Nat.add_sub_of_le le_rfl) w (x, z) 0 ∈ d.K' w := h1
    rwa [blk_self] at h2
  · rw [if_neg (by simp [B₀, hs])] at h
    rw [if_neg hs]
    exact h.1

theorem lev₁_le {Sec : Set (Pl E)} (hSec : IsSection Sec) (hd : d.Ok) (T₀ : d.T = ∅) (B₀ : d.Bad = ∅) :
    lev₁ Sec d n ≤ globL (Kfam Sec d) := by
  refine (Subgroup.closure_le _).2 fun g hg => ?_
  have hg' : (g, 1) ∈ levSet Sec d n := hg
  simp only [SetLike.mem_coe, globL, Subgroup.mem_iInf, Subgroup.mem_comap]
  intro w
  by_cases hw : w ∈ Sec
  · rw [Kfam_of_mem d hw]
    exact lev_mem hd T₀ B₀ (hg' w hw).1
  · obtain ⟨u, hu, hs, rfl, e⟩ := exists_conj_of_notMem hSec hw
    rw [Kfam_of_notMem d hw e, Subgroup.mem_comap, ← map_pLoc_thF_eq]
    exact lev₂_mem hd B₀ ((hg' u hu).2 hs)

end Main

section Core

open GlobalTheory.SplitPts GlobalTheory.CompanionTheory.CompConjPlace GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws
open PositivityTheory.Rg.BcB.F.F5.Bo

theorem exists_lev₁_fix (π : CuspSub E n) (hd : GlobalTheory.ContraPair.DualIsConj π) {Sec : Set (Pl E)} {d : LocData E n}
    {τ : ∀ w : Pl E, SmIrr (GLw n w)} (hSec : IsSection Sec) (ok₀ : d.Ok) (T₀ : d.T = ∅) (B₀ : d.Bad = ∅)
    (good : ∀ w ∈ Sec, w ∉ d.S₀ → ∃ B, (CG.mk π).HasSat w B) (hτ : ∀ w, π.IsLocComp w (τ w))
    (τ_fix : ∀ w ∈ d.S₀, ∃ y ∈ fixed (τ w).ρ (d.K' w), y ≠ 0) :
    ∃ ψ ∈ π.V, ψ ≠ 0 ∧ ∀ k ∈ lev₁ Sec d n, finRep E n k ψ = ψ := by
  have hy : ∀ u ∈ Sec, ∃ y ∈ fixed (τ u).ρ (Mlev d u), y ≠ 0 := by
    intro u hu
    by_cases hs : u ∈ d.S₀
    · rw [Mlev, if_pos hs]
      exact τ_fix u hs
    · obtain ⟨B, hB⟩ := good u hu hs
      rw [Mlev, if_neg hs]
      exact (Submodule.ne_bot_iff _).1 ((GlobalTheory.BcSpehCompare.hasSat_iff (hτ u) B).1 hB).1
  have hc : ∀ w, IsCompact (Kfam Sec d w : Set (GLw n w)) := by
    intro w
    by_cases hw : w ∈ Sec
    · rw [Kfam_of_mem d hw]
      exact (Mlev_compact ok₀ w).1
    · obtain ⟨u, -, -, rfl, e⟩ := exists_conj_of_notMem hSec hw
      rw [Kfam_of_notMem d hw e]
      exact isCompact_comap_thAt u _ (Mlev_compact ok₀ u).1 (Mlev_compact ok₀ u).2
  have hv : ∀ w, ∃ φ : π.V, φ ≠ 0 ∧ φ ∈ fixed (π.locRep w) (Kfam Sec d w) := by
    intro w
    by_cases hw : w ∈ Sec
    · obtain ⟨y, h1, h2⟩ := hy w hw
      rw [Kfam_of_mem d hw]
      exact fixed_of_comp (hτ w) _ h1 h2
    · obtain ⟨u, hu, -, rfl, e⟩ := exists_conj_of_notMem hSec hw
      obtain ⟨y, h1, h2⟩ := hy u hu
      rw [Kfam_of_notMem d hw e]
      exact exists_fixed_conj π hd (hτ u) _ h1 h2
  have hfin : (↑(d.S₀ ∪ d.S₀.image (conjSrc (conjE E))) : Set (Pl E)).Finite := Finset.finite_toSet _
  have hcof : ∀ᶠ w in Filter.cofinite, Kfam Sec d w = GlobalTheory.LFun.KGL w n := by
    filter_upwards [hfin.compl_mem_cofinite] with w hw
    have hw' : w ∉ d.S₀ ∪ d.S₀.image (conjSrc (conjE E)) := fun h => hw (Finset.mem_coe.2 h)
    refine Kfam_eq_of_notMem hSec (fun h => hw' (Finset.mem_union_left _ h)) fun h => hw' (Finset.mem_union_right _ ?_)
    exact Finset.mem_image.2 ⟨_, h, conjSrc_conjSrc_cm w⟩
  obtain ⟨ψ, h1, h2, h3⟩ := exists_global_fix π _ hc hv hcof
  exact ⟨ψ, h1, h2, fun k hk => h3 k (lev₁_le hSec ok₀ T₀ B₀ hk)⟩

end Core

end GlobalTheory.CompanionTheory.LFixDPf

end
end
