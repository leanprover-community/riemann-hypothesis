import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechDSq
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PDegLocExact
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechExact
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechFlat
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechCone
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechTransport
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerrePolyLaurent
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerrePolyLaurentCohom
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsSerrePoly
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreFree
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGradedPres
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsPres
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreOnto
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreTail
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGenerated
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistFiniteness.CoeffPsiMulSingle
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistSections
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PProjDegreePositive
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPositive
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPoint
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleTwistGenerated
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleCover
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleTwistLocal
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsAmple
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeAway
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeOnWLift
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeOnWGen
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThree
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationExists
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationRestrict
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestriction
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrictTwist
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepDataJProper
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSubvarDrop
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefRestrict
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsTwistSplit
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsFibreHilbertFlat
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsFibreCycleDegree
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsNefGeneric
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PFiniteSections
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PDomination
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSurjectiveClosed
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDrop
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountTopSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropSt

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

theorem CechTop.idx_isEmpty (N i : ℕ) (hi : N < i) :
    IsEmpty (Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) := by
  refine ⟨fun I => ?_⟩
  have h1 : I.1.1.card ≤ N + 1 := by
    simpa using Finset.card_le_univ I.1.1
  have h2 := I.2
  omega

theorem CechTop.proof : CechTop.Statement := by
  intro S _ _ N M _ _ _ _ 𝓜 i c hi
  have := CechTop.idx_isEmpty N i hi
  have hC : Subsingleton (Cech.Cochain (locSys S N M) i) := inferInstance
  constructor
  intro a b
  change (a : Cech.Hdeg _ _ _ i) = b
  induction a using Submodule.Quotient.induction_on with
  | H x =>
    induction b using Submodule.Quotient.induction_on with
    | H y =>
      congr 1
      exact Subtype.ext (hC.elim _ _)

end GroundTheory.Heights₂.Heights.Kleiman
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u

theorem SerrePoly.proof (hL : SerrePoly.Laurent.Statement.{u}) (hT : Cech.Transport.Statement.{u, u, u})
    (hC : SerrePoly.LaurentCohom.Statement.{u}) : SerrePoly.Statement.{u} := by
  intro S _ _ N
  obtain ⟨hinj, hpiece, ι, hι, hres, hmk, hdeg⟩ := hL S N
  obtain ⟨hfin, hvan, hconst⟩ := hC S N
  have hφ : ∀ (I J : StdCell N) (h : I.1 ⊆ J.1) (m : LocMod S N (Poly S N) I.1),
      ι J (locResS I J h m) = Cech.idRes S (Laurent S N) Finset.univ I J h (ι I m) :=
    fun I J h m => hres I J h m
  have hd : ∀ (c : ℤ) (I : StdCell N) (m : LocMod S N (Poly S N) I.1),
      m ∈ degLoc (polyGraded S N) c I → ι I m ∈ laurentDeg S N c I := fun c I m hm => by
    rw [← hdeg c I]; exact Submodule.mem_map_of_mem hm
  have hb : ∀ (i : ℕ) (c : ℤ), Function.Bijective
      (Cech.mapHdeg (degLoc (polyGraded S N) c) (laurentDeg S N c) ι hφ (hd c) i) :=
    fun i c => hT (N + 1) Finset.univ S _ _ _ _ (degLoc (polyGraded S N) c) (laurentDeg S N c) ι hφ
      (hd c) hι (hdeg c) i
  let E : ∀ (i : ℕ) (c : ℤ), cohom (polyGraded S N) i c ≃ₗ[S] laurentCohom S N i c :=
    fun i c => LinearEquiv.ofBijective _ (hb i c)
  refine ⟨fun i c => Module.Finite.equiv (E i c).symm, fun c hc => ⟨fun i hi => ?_, ?_, ?_⟩⟩
  · have := hvan c hc i hi
    exact (E i c).toEquiv.subsingleton
  ·
    intro m m' hmm
    have h0 : (constCochain (S := S) (N := N) (M := Poly S N) (m : Poly S N)) =
        constCochain (S := S) (N := N) (M := Poly S N) (m' : Poly S N) := by
      have hmem := (Submodule.Quotient.eq _).mp hmm
      change _ ∈ (⊥ : Submodule S _).comap _ at hmem
      rw [Submodule.mem_comap, Submodule.mem_bot] at hmem
      exact sub_eq_zero.mp hmem
    let I0 : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 :=
      ⟨⟨{0}, Finset.singleton_nonempty _, Finset.subset_univ _⟩, Finset.card_singleton _⟩
    have h1 := congrArg (ι I0.1) (congrFun h0 I0)
    change ι I0.1 (locMk (Poly S N) I0.1.1 m) = ι I0.1 (locMk (Poly S N) I0.1.1 m') at h1
    rw [hmk, hmk] at h1
    exact Subtype.ext (hinj h1)
  ·
    intro y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hw : (Cech.mapC ι 0 (z : Cech.Cochain (locSys S N (Poly S N)) 0)) ∈
        Cech.cocyDeg (fun _ : StdCell N => Laurent S N) (laurentDeg S N c)
          (Cech.idRes S (Laurent S N) Finset.univ) 0 := by
      refine Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr ?_, fun I _ => ?_⟩
      · rw [← Cech.mapC_d ι hφ, LinearMap.mem_ker.mp (Submodule.mem_inf.mp z.2).1, map_zero]
      · exact hd c I.1 _ ((Submodule.mem_inf.mp z.2).2 I (Set.mem_univ _))
    obtain ⟨f, hf, hzf⟩ := hconst c hc _ hw
    rw [← hpiece c] at hf
    obtain ⟨m, hm, rfl⟩ := hf
    refine ⟨⟨m, hm⟩, ?_⟩
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    funext I
    apply hι I.1
    change ι I.1 (locMk (Poly S N) I.1.1 m) = _
    rw [hmk]
    exact (hzf I).symm

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

theorem GradedULift.proof : GradedULift.Statement.{u, v} := by
  intro S _ N M _ _ _ _ 𝓜
  let e : M ≃ₗ[S] ULift.{u} M := (ULift.moduleEquiv (R := S)).symm
  let eP : M ≃ₗ[Poly S N] ULift.{u} M := (ULift.moduleEquiv (R := Poly S N)).symm
  let pc : ℤ → Submodule S (ULift.{u} M) := fun c => (𝓜.piece c).map (e : M →ₗ[S] ULift.{u} M)
  have hpc : ∀ c, pc c = Submodule.orderIsoMapComap e (𝓜.piece c) := fun _ => rfl
  have hint : DirectSum.IsInternal pc := by
    have h0 := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1 𝓜.isInternal
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2 ⟨?_, ?_⟩
    · have : pc = (Submodule.orderIsoMapComap e) ∘ 𝓜.piece := funext hpc
      rw [this]
      exact h0.1.map_orderIso _
    · have h1 : (⨆ c, pc c) = Submodule.orderIsoMapComap e (⨆ c, 𝓜.piece c) := by
        rw [OrderIso.map_iSup]
        rfl
      rw [h1, h0.2]
      exact (Submodule.orderIsoMapComap e).map_top
  let 𝓜' : GradedPMod S N (ULift.{u} M) :=
    { piece := pc
      isInternal := hint
      smul_mem := by
        intro d c p m hp hm
        obtain ⟨x, hx, rfl⟩ := hm
        refine ⟨p • x, 𝓜.smul_mem d c p x hp hx, ?_⟩
        rfl }
  refine ⟨ULift.{u} M, inferInstance, inferInstance, inferInstance, inferInstance, 𝓜',
    ⟨eP.toLinearMap, fun c m hm => ⟨m, hm, rfl⟩⟩,
    ⟨eP.symm.toLinearMap, fun c m hm => ?_⟩, fun m => rfl, fun m => rfl⟩
  obtain ⟨x, hx, rfl⟩ := hm
  exact hx

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Retract

variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']

theorem locMap_retract (f : M →ₗ[Poly S N] M') (g : M' →ₗ[Poly S N] M)
    (hgf : Function.LeftInverse g f) (I : Finset (Fin (N + 1))) :
    Function.LeftInverse (locMap g I) (locMap f I) := by
  intro x
  induction x using LocalizedModule.induction_on with
  | h m s => rw [locMap_mk, locMap_mk, hgf m]

theorem cohomMap_retract {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'}
    (f : GradedHom 𝓜 𝓜') (g : GradedHom 𝓜' 𝓜) (hgf : Function.LeftInverse g.toLin f.toLin)
    (i : ℕ) (c : ℤ) : Function.LeftInverse (cohomMap g i c) (cohomMap f i c) := by
  intro x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk
    (Subtype.ext (funext fun I => locMap_retract f.toLin g.toLin hgf I.1.1 (z.1 I)))

theorem CohomRetract.proof : CohomRetract.Statement.{u, v, w} := by
  intro S _ N M M' _ _ _ _ _ _ _ _ 𝓜 𝓜' f g hgf i c
  exact (cohomMap_retract f g hgf i c).injective

end Retract

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

theorem SerreFinite.proof (hExact : CechExact.Statement.{u, max u v})
    (hTop : CechTop.Statement.{u, max u v}) (hFree : SerreFree.Statement.{u, max u v})
    (hPres : GradedPres.Statement.{u, v}) (hLift : GradedULift.Statement.{u, v})
    (hRet : CohomRetract.Statement.{u, v, max u v}) : SerreFinite.Statement.{u, v} := by
  intro S _ _ N

  have key : ∀ (k : ℕ) (M : Type (max u v)) [AddCommGroup M] [Module (Poly S N) M] [Module S M]
      [IsScalarTower S (Poly S N) M] (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M →
      ∀ i, N + 1 ≤ i + k → ∀ c : ℤ, Module.Finite S (cohom 𝓜 i c) := by
    intro k
    induction k with
    | zero =>
      intro M _ _ _ _ 𝓜 _ i hi c
      have := hTop S N M 𝓜 i c (by omega)
      exact ⟨by rw [Subsingleton.elim (⊤ : Submodule S (cohom 𝓜 i c)) ⊥]; exact Submodule.fg_bot⟩
    | succ k ih =>
      intro M _ _ _ _ 𝓜 hM i hi c
      obtain ⟨F, _, _, _, _, K, _, _, _, _, 𝓕, 𝓚, r, b, d, f, g, hb, hK, hf, hg, hfg⟩ :=
        hPres S N M 𝓜 hM
      have hF : Module.Finite S (cohom 𝓕 i c) := (hFree S N F 𝓕 r b d hb).1 i c
      have hKf : Module.Finite S (cohom 𝓚 (i + 1) c) := ih K 𝓚 hK (i + 1) (by omega) c
      obtain ⟨-, δ, hδ, -⟩ := (hExact S N K F M 𝓚 𝓕 𝓜 f g hf hg hfg c).2 i
      refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker δ (IsNoetherian.noetherian _) ?_⟩
      rw [top_inf_eq, LinearMap.exact_iff.mp hδ, LinearMap.range_eq_map]
      exact hF.fg_top.map _
  intro M _ _ _ _ 𝓜 hM i c
  obtain ⟨M', _, _, _, _, 𝓜', f, g, hgf, hfg⟩ := hLift S N M 𝓜
  have hM' : Module.Finite (Poly S N) M' :=
    Module.Finite.of_surjective f.toLin fun y => ⟨g.toLin y, hfg y⟩
  have := key (N + 1) M' 𝓜' hM' i (by omega) c
  exact Module.Finite.of_injective (cohomMap f i c) (hRet S N M M' 𝓜 𝓜' f g hgf i c)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

theorem SerreVanish.proof (hExact : CechExact.Statement.{u, max u v})
    (hTop : CechTop.Statement.{u, max u v}) (hFree : SerreFree.Statement.{u, max u v})
    (hPres : GradedPres.Statement.{u, v}) (hLift : GradedULift.Statement.{u, v})
    (hRet : CohomRetract.Statement.{u, v, max u v}) : SerreVanish.Statement.{u, v} := by
  intro S _ _ N

  have key : ∀ (k : ℕ) (M : Type (max u v)) [AddCommGroup M] [Module (Poly S N) M] [Module S M]
      [IsScalarTower S (Poly S N) M] (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M →
      ∃ c₀ : ℤ, ∀ i, N + 1 ≤ i + k → 1 ≤ i → ∀ c ≥ c₀, Subsingleton (cohom 𝓜 i c) := by
    intro k
    induction k with
    | zero =>
      intro M _ _ _ _ 𝓜 _
      exact ⟨0, fun i hi _ c _ => hTop S N M 𝓜 i c (by omega)⟩
    | succ k ih =>
      intro M _ _ _ _ 𝓜 hM
      obtain ⟨F, _, _, _, _, K, _, _, _, _, 𝓕, 𝓚, r, b, d, f, g, hb, hK, hf, hg, hfg⟩ :=
        hPres S N M 𝓜 hM
      obtain ⟨c₁, hc₁⟩ := ih K 𝓚 hK
      refine ⟨max c₁ (∑ j, |d j|), fun i hi hi1 c hc => ?_⟩
      have hdc : ∀ j, d j ≤ c := fun j =>
        ((le_abs_self (d j)).trans (Finset.single_le_sum (fun j _ => abs_nonneg (d j))
          (Finset.mem_univ j))).trans ((le_max_right _ _).trans hc)
      have hF := ((hFree S N F 𝓕 r b d hb).2 c hdc).1 i hi1
      have hKv := hc₁ (i + 1) (by omega) (by omega) c ((le_max_left _ _).trans hc)
      obtain ⟨δ, hδ, -⟩ := ((hExact S N K F M 𝓚 𝓕 𝓜 f g hf hg hfg c).2 i).2
      refine ⟨fun x y => ?_⟩
      have hx : ∀ z : cohom 𝓜 i c, z = 0 := fun z => by
        obtain ⟨w, hw⟩ := (hδ z).mp (Subsingleton.elim _ _)
        rw [← hw, Subsingleton.elim w 0, map_zero]
      rw [hx x, hx y]
  intro M _ _ _ _ 𝓜 hM
  obtain ⟨M', _, _, _, _, 𝓜', f, g, hgf, hfg⟩ := hLift S N M 𝓜
  have hM' : Module.Finite (Poly S N) M' :=
    Module.Finite.of_surjective f.toLin fun y => ⟨g.toLin y, hfg y⟩
  obtain ⟨c₀, hc₀⟩ := key N M' 𝓜' hM'
  refine ⟨c₀, fun i hi c hc => ?_⟩
  have := hc₀ i (by omega) hi c hc
  exact (hRet S N M M' 𝓜 𝓜' f g hgf i c).subsingleton

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial AddMonoidAlgebra TwistFin

universe u w

theorem TwistFinite.proof (hE : Extension.Statement.{u, w, w}) (hSF : SerreFinite.Statement.{u, w}) :
    TwistFinite.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x G B r η hx _ hgen
  classical
  obtain ⟨M0, -, hG⟩ := hE S Ω N x Ω G.toSubFamily G.fg
  obtain ⟨n0, d0, g0, -, hspan⟩ := M0.fg
  obtain ⟨i0, hi0⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have hfin : Module.Finite (Sy S r) (cohom (tgraded x η S n0 d0 g0) 0 0) :=
    hSF (Sy S r) N _ (tgraded x η S n0 d0 g0) inferInstance 0 0
  let Γ : Set (Amb x η) := {γ | ∃ (b : ℕ) (s : Ω), s ∈ (G.twist (B.pow b)).secs ∧
    γ = (toA x η).symm (single ((0 : ℤ), (b : ℤ)) s)}
  have hΓ : Γ ⊆ LinearMap.range (readChartH0 x η S n0 d0 g0 i0 hi0) := by
    rintro _ ⟨b, s, hs, rfl⟩
    refine mem_range_readChartH0 x η S n0 d0 g0 i0 hi0 _ fun I hI => ?_
    refine chart_pre x η S M0 G B hgen hG hspan I hI b ?_
    rw [SubSystem.secs, Submodule.mem_iInf] at hs
    exact hs (toChart x I hI)
  have hfg : (Submodule.span (Sy S r) Γ).FG := by
    have : IsNoetherian (Sy S r) (LinearMap.range (readChartH0 x η S n0 d0 g0 i0 hi0)) :=
      isNoetherian_of_fg_of_noetherian _ (Module.Finite.iff_fg.mp inferInstance)
    exact isNoetherian_submodule.mp this _ (Submodule.span_le.mpr hΓ)
  obtain ⟨t, ht⟩ := hfg
  obtain ⟨T, hTΓ, htT⟩ := Submodule.subset_span_finite_of_subset_span
    (R := Sy S r) (s := Γ) (t := t) (by rw [← ht]; exact Submodule.subset_span)
  have hle : Submodule.span (Sy S r) Γ ≤ Submodule.span (Sy S r) (T : Set (Amb x η)) := by
    rw [← ht, Submodule.span_le]
    exact htT
  have hT : ∀ γ : T, ∃ (b : ℕ) (s : Ω), s ∈ (G.twist (B.pow b)).secs ∧
      (γ : Amb x η) = (toA x η).symm (single ((0 : ℤ), (b : ℤ)) s) := fun γ => hTΓ γ.2
  choose bT sT hsT hγT using hT
  let e := T.equivFin
  refine ⟨T.card, fun k => bT (e.symm k), fun k => sT (e.symm k), fun k => hsT _, ?_⟩
  intro b s hs
  have hmem : (toA x η).symm (single ((0 : ℤ), (b : ℤ)) s) ∈
      Submodule.span (Sy S r) (T : Set (Amb x η)) :=
    hle (Submodule.subset_span ⟨b, s, hs, rfl⟩)
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hmem
  have hcoef := congrArg (fun a => (toA x η a).coeff ((0 : ℤ), (b : ℤ))) hc
  simp only [AddEquiv.apply_symm_apply, map_sum, toA_smulSy, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, coeff_single, Finsupp.single_eq_same] at hcoef
  rw [← hcoef]
  refine Submodule.sum_mem _ fun γ hγ => ?_
  have h1 : toA x η γ = single ((0 : ℤ), ((bT ⟨γ, hγ⟩ : ℕ) : ℤ)) (sT ⟨γ, hγ⟩) := by
    have := congrArg (toA x η) (hγT ⟨γ, hγ⟩)
    rwa [AddEquiv.apply_symm_apply] at this
  rw [h1, coeff_psi_mul_single]
  refine Submodule.sum_mem _ fun d _ => ?_
  split_ifs with hdb
  · refine Submodule.subset_span ⟨e ⟨γ, hγ⟩, homogeneousComponent d (c γ), d,
      homogeneousComponent_isHomogeneous _ _, ?_, ?_⟩
    · simp only [Equiv.symm_apply_apply]
      exact hdb
    · simp only [Equiv.symm_apply_apply]
  · exact zero_mem _

end GroundTheory.Heights₂.Heights.Kleiman
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u w

theorem FiniteTwists.proof (hT1 : TwistFinite.Statement.{u, w}) : FiniteTwists.Statement.{u, w} :=
  hT1

end GroundTheory.Heights₂.Heights.Kleiman
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

theorem GeneratedAmple.proof (hCover : AmpleCover.Statement.{u, w})
    (hLocal : AmpleTwistLocal.Statement.{u, w}) : GeneratedAmple.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x H A Q
  choose n₀ hn₀ using fun (b : Fin A.m) (j : Fin (A.r + 1)) => hLocal S Ω N x H A Q b j
  let M : ℕ := Finset.univ.sup fun p : Fin A.m × Fin (A.r + 1) => n₀ p.1 p.2
  refine ⟨A.m * M, fun c hc => hCover S Ω N x H A _ fun j I y hy => ?_⟩
  have hm := A.m_pos
  have hc' : c % A.m + A.m * (c / A.m) = c := Nat.mod_add_div c A.m
  have hM : M ≤ c / A.m := (Nat.le_div_iff_mul_le hm).mpr (by rw [mul_comm]; exact hc)
  have hn : n₀ ⟨c % A.m, Nat.mod_lt c hm⟩ j ≤ c / A.m :=
    le_trans (Finset.le_sup (f := fun p : Fin A.m × Fin (A.r + 1) => n₀ p.1 p.2)
      (Finset.mem_univ (⟨c % A.m, Nat.mod_lt c hm⟩, j))) hM
  have key := hn₀ ⟨c % A.m, Nat.mod_lt c hm⟩ j (c / A.m) hn I y
  simp only [hc'] at key
  exact key hy

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem StepThree.OnW.proof (hL : StepThree.OnW.Lift.Statement.{u, w})
    (hG : StepThree.OnW.Gen.Statement.{u, w}) : StepThree.OnW.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK pp hpp
  obtain ⟨c₁, h₁⟩ := hL k Ω N x T hK pp hpp
  obtain ⟨c₂, h₂⟩ := hG k Ω N x T hK pp hpp
  refine ⟨max c₁ c₂, fun b c hb hc I => ?_⟩
  refine (h₂ b c hb (le_of_max_le_right hc) I).trans (sup_le ?_ le_sup_right)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨s, hs, hcomp, rfl⟩
  obtain ⟨t, ht, hts⟩ := h₁ b c hb (le_of_max_le_left hc) s hs hcomp
  have he : s I = t - (t - s I) := by abel
  rw [SetLike.mem_coe, he]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.subset_span (SetLike.mem_coe.mpr ht)))
    (Submodule.mem_sup_right (hts I))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u v w

theorem PrimeFiltration.proof (hE : PrimeFiltration.Exists.Statement.{u, v, w}) :
    PrimeFiltration.Statement.{u, v, w} :=
  ⟨hE, PrimeFiltration.Irrelevant.proof, PrimeFiltration.Point.proof,
    PrimeFiltration.Restrict.proof⟩

end GroundTheory.Heights₂.Heights.Kleiman
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem TwistVanish.proof (hE : Extension.Statement.{u, w, w}) (hV : SerreVanish.Statement.{u, w})
    (hT : TwistSplit.Statement.{u, w}) : TwistVanish.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x G B r η hη hspan
  obtain ⟨M₀, -, hM₀⟩ := hE S Ω N x Ω G.toSubFamily G.fg
  obtain ⟨M, _, _, _, _, 𝓜, hfin, hsplit⟩ :=
    hT S Ω N x M₀ G.toSubSystem B.toSubSystem r η hM₀ hη hspan
  obtain ⟨c₀, hc₀⟩ := hV (MvPolynomial (Fin (r + 1)) S) N M 𝓜 hfin
  refine ⟨c₀, fun b c hc => ?_⟩
  obtain ⟨ι, π, hπ⟩ := hsplit b c 1
  have := hc₀ 1 le_rfl c hc
  exact ⟨fun z z' => by rw [← hπ z, ← hπ z', Subsingleton.elim (ι z) (ι z')]⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

universe u w

theorem ConservationOfDegree.proof (hA : FibreHilbertFlat.Statement.{u, w})
    (hB : FibreCycleDegree.Statement.{u, w}) : ConservationOfDegree.Statement.{u, w} := by
  intro S _ _ F _ _ _ Ω _ _ _ _ N x M 𝔪 h𝔪 qq hq hconst hsub
  have h1 := hA S F Ω N x M 𝔪 h𝔪 qq hq hconst hsub
  have h2 := hB S F Ω N x M 𝔪 h𝔪 qq hq hconst hsub
  rw [interNum]
  refine Tendsto.limUnder_eq (tendsto_const_nhds.congr' ?_)
  filter_upwards [h1, h2] with c e1 e2
  rw [e1, e2]

end GroundTheory.Heights₂.Heights.Kleiman
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

universe u w

theorem curveClosure {S : Type u} [CommRing S] [IsDomain S] {F : Type u} [Field F] [Algebra S F]
    [IsFractionRing S F] {N : ℕ} (pp : Ideal (Poly F N)) [pp.IsPrime] :
    (∀ s : S, (C s : Poly S N) ∈ pp.comap (MvPolynomial.map (algebraMap S F)) → s = 0) ∧
      (pp.comap (MvPolynomial.map (algebraMap S F))).map (MvPolynomial.map (algebraMap S F)) = pp := by
  refine ⟨fun s hs => ?_, ?_⟩
  · by_contra h0
    have hs' : (C (algebraMap S F s) : Poly F N) ∈ pp := by
      rw [Ideal.mem_comap, map_C] at hs; exact hs
    have hu : IsUnit (C (algebraMap S F s) : Poly F N) :=
      (IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective S F)).mpr h0)).map C
    exact Ideal.IsPrime.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem _ hs' hu)
  · let _ : Algebra (Poly S N) (Poly F N) := MvPolynomial.algebraMvPolynomial
    have : IsLocalization ((nonZeroDivisors S).map (C : S →+* Poly S N)) (Poly F N) :=
      MvPolynomial.isLocalization (nonZeroDivisors S) F
    exact IsLocalization.map_under ((nonZeroDivisors S).map (C : S →+* Poly S N)) (Poly F N) pp

theorem NefGeneric.proof (hC : ConservationOfDegree.Statement.{u, w}) :
    NefGeneric.Statement.{u, w} := by
  intro S _ _ F _ _ _ Ω _ _ _ _ N x M 𝔪 h𝔪 hM pp _ hpp
  have : pp.IsPrime := hpp.isPrime
  obtain ⟨hconst, hmap⟩ := curveClosure (S := S) pp
  have hpp' := hpp
  rw [← hmap] at hpp'
  have key := hC S F Ω N x M 𝔪 h𝔪 _ inferInstance hconst hpp'
  rw [hmap] at key
  rw [key]
  refine finsum_nonneg fun G => ?_
  split_ifs with hG
  · exact mul_nonneg (Int.natCast_nonneg _) (hM G (le_sup_right.trans hG.1.1.2) hG.2)
  · exact le_rfl

end GroundTheory.Heights₂.Heights.Kleiman
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

universe u w

theorem SectionCount.proof (hT : SectionCount.Top.Statement.{u, w})
    (hD : SectionCount.Drop.Statement.{u, w}) : SectionCount.Statement.{u, w} := by
  intro k _ Ω _ _ N x d Nb b hZ hN hb
  obtain ⟨C₁, h₁⟩ := hT k Ω N x d Nb hZ hN
  obtain ⟨C₂, h₂⟩ := hD k Ω N x d Nb b hZ hN hb
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂, eventually_ge_atTop 1] with n hn₁ hn₂ hn
  set f : ℕ → ℝ := fun i =>
    (Module.finrank k (twistMul Nb.toSubSystem n (-((i : ℤ) * b))).secs : ℝ) with hf
  set Y : ℝ := (interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) : ℝ) with hY
  set X : ℝ := (interNum (primeOf (S := k) x) (Fin.cons (α := fun _ => SubSystem k x Ω)
    (twistSys k x (b : ℤ)) (fun _ : Fin d => Nb.toSubSystem)) : ℝ) with hX
  have h0 : f 0 = (Module.finrank k (twistMul Nb.toSubSystem n 0).secs : ℝ) :=
    congrArg (fun m : ℤ => (Module.finrank k (twistMul Nb.toSubSystem n m).secs : ℝ)) (by simp)
  have htel : f 0 - f n = ∑ i ∈ Finset.range n, (f i - f (i + 1)) := by
    rw [Finset.sum_range_sub']
  have hsum : ∑ i ∈ Finset.range n, (f i - f (i + 1)) ≤
      ∑ _i ∈ Finset.range n, (X * (n : ℝ) ^ d / (d.factorial : ℝ) + C₂ * (n : ℝ) ^ d / n) :=
    Finset.sum_le_sum fun i hi => hn₂ i (Finset.mem_range.mp hi)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : ((d + 1).factorial : ℝ) = ((d : ℝ) + 1) * (d.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hdf : (0 : ℝ) < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
  have key : (n : ℝ) * (X * (n : ℝ) ^ d / (d.factorial : ℝ) + C₂ * (n : ℝ) ^ d / n) =
      ((d : ℝ) + 1) * X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) + C₂ * (n : ℝ) ^ d := by
    rw [hfac]; field_simp; ring
  rw [key] at hsum
  rw [← h0] at hn₁
  have hgoal : f n = (Module.finrank k (twistMul Nb.toSubSystem n (-((n : ℤ) * b))).secs : ℝ) := rfl
  rw [← hgoal]
  push_cast
  have e1 : (Y - ((d : ℝ) + 1) * X) * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) =
      Y * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) -
        ((d : ℝ) + 1) * X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) := by ring
  rw [e1]
  linarith

end GroundTheory.Heights₂.Heights.Kleiman
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u v w

theorem CechDSq.full : CechDSq.Statement.{u, v} := CechDSq.proof
theorem DegLocExact.full : DegLocExact.Statement.{u, v} := DegLocExact.proof
theorem CechExact.full : CechExact.Statement.{u, v} := CechExact.proof CechDSq.full DegLocExact.full
theorem CechTop.full : CechTop.Statement.{u, v} := CechTop.proof
theorem CechFlat.full : CechFlat.Statement.{u, v} := CechFlat.proof
theorem Cech.Cone.full : Cech.Cone.Statement.{u, v} := Cech.Cone.proof
theorem Cech.Transport.full : Cech.Transport.Statement.{u, v, w} := Cech.Transport.proof
theorem SerrePoly.Laurent.full : SerrePoly.Laurent.Statement.{u} := SerrePoly.Laurent.proof
theorem SerrePoly.LaurentCohom.full : SerrePoly.LaurentCohom.Statement.{u} :=
  SerrePoly.LaurentCohom.proof Cech.Cone.full
theorem SerrePoly.full : SerrePoly.Statement.{u} :=
  SerrePoly.proof SerrePoly.Laurent.full Cech.Transport.full SerrePoly.LaurentCohom.full
theorem SerreFree.full : SerreFree.Statement.{u, v} := SerreFree.proof SerrePoly.full
theorem GradedPres.full : GradedPres.Statement.{u, v} := GradedPres.proof
theorem GradedULift.full : GradedULift.Statement.{u, v} := GradedULift.proof
theorem CohomRetract.full : CohomRetract.Statement.{u, v, w} := CohomRetract.proof

theorem SerreFinite.full : SerreFinite.Statement.{u, v} :=
  SerreFinite.proof CechExact.full CechTop.full SerreFree.full GradedPres.full GradedULift.full
    CohomRetract.full

theorem SerreVanish.full : SerreVanish.Statement.{u, v} :=
  SerreVanish.proof CechExact.full CechTop.full SerreFree.full GradedPres.full GradedULift.full
    CohomRetract.full

theorem SerreOnto.full : SerreOnto.Statement.{u, v} :=
  SerreOnto.proof CechExact.full SerreFree.full SerreVanish.full

theorem SerreTail.full : SerreTail.Statement.{u, v} := SerreTail.proof SerreFinite.full SerreOnto.full

theorem Extension.full : Extension.Statement.{u, v, w} := Extension.proof
theorem Generated.full : Generated.Statement.{u, w} := Generated.proof Extension.full
theorem TwistFinite.full : TwistFinite.Statement.{u, w} := TwistFinite.proof Extension.full SerreFinite.full
theorem FiniteTwists.full : FiniteTwists.Statement.{u, w} := FiniteTwists.proof TwistFinite.full
theorem TwistSections.full : TwistSections.Statement.{u, w} := TwistSections.proof SerreOnto.full
theorem ProjDegreePositive.full : ProjDegreePositive.Statement.{u} := ProjDegreePositive.proof
theorem HilbertPositive.full : HilbertPositive.Statement.{u, w} :=
  HilbertPositive.proof ProjDegreePositive.full TwistSections.full
theorem HilbertPoint.full : HilbertPoint.Statement.{u, w} := HilbertPoint.proof
theorem PrimeFiltration.Exists.full : PrimeFiltration.Exists.Statement.{u, v, w} :=
  PrimeFiltration.Exists.proof
theorem PrimeFiltration.full : PrimeFiltration.Statement.{u, v, w} :=
  PrimeFiltration.proof PrimeFiltration.Exists.full
theorem PrimeFiltration.Irrelevant.full : PrimeFiltration.Irrelevant.Statement.{u} :=
  PrimeFiltration.Irrelevant.proof
theorem PrimeFiltration.Point.full : PrimeFiltration.Point.Statement.{u, w} := PrimeFiltration.Point.proof
theorem PrimeFiltration.Restrict.full : PrimeFiltration.Restrict.Statement.{u, w} :=
  PrimeFiltration.Restrict.proof
theorem Restriction.full : Restriction.Statement.{u, w} := Restriction.proof

theorem VeryAmpleTwistGenerated.full : VeryAmpleTwistGenerated.Statement.{u, w} :=
  VeryAmpleTwistGenerated.proof
theorem AmpleCover.full : AmpleCover.Statement.{u, w} := AmpleCover.proof
theorem StepThree.Away.full : StepThree.Away.Statement.{u, w} := StepThree.Away.proof
theorem RestrictTwist.full : RestrictTwist.Statement.{u, w} := RestrictTwist.proof
theorem StepData.JProper.full : StepData.JProper.Statement.{u, w} := StepData.JProper.proof
theorem SubvarDrop.full : SubvarDrop.Statement.{u, w} := SubvarDrop.proof

theorem AmpleTwistLocal.assembled (hA : AmpleAffineGen.Statement.{u, w}) :
    AmpleTwistLocal.Statement.{u, w} :=
  AmpleTwistLocal.proof hA

theorem GeneratedAmple.assembled (hA : AmpleAffineGen.Statement.{u, w}) :
    GeneratedAmple.Statement.{u, w} :=
  GeneratedAmple.proof AmpleCover.full (AmpleTwistLocal.assembled hA)

theorem TwistVanish.assembled (hS : TwistSplit.Statement.{u, w}) : TwistVanish.Statement.{u, w} :=
  TwistVanish.proof Extension.full SerreVanish.full hS

theorem NefRestrict.assembled (hRL : RestrLenRestrict.Statement.{u, w}) : NefRestrict.Statement.{u, w} :=
  NefRestrict.proof RestrictTwist.full hRL

theorem FiniteSections.assembled (hT : TildeTail.Statement.{u, w}) : FiniteSections.Statement.{u, w} :=
  FiniteSections.proof Extension.full hT

theorem Domination.assembled (hT : TildeTail.Statement.{w, w}) : Domination.Statement.{u, w} :=
  Domination.proof (FiniteSections.assembled hT)

theorem SurjectiveClosed.assembled (hFam : IdealTwistFamily.Statement.{u, w})
    (hVan : TildeVanish.Statement.{u, w, w}) : SurjectiveClosed.Statement.{u, w} :=
  SurjectiveClosed.proof Extension.full hFam hVan

theorem ConservationOfDegree.assembled (hA : FibreHilbertFlat.Statement.{u, w})
    (hB : FibreCycleDegree.Statement.{u, w}) : ConservationOfDegree.Statement.{u, w} :=
  ConservationOfDegree.proof hA hB

theorem NefGeneric.assembled (hA : FibreHilbertFlat.Statement.{u, w})
    (hB : FibreCycleDegree.Statement.{u, w}) : NefGeneric.Statement.{u, w} :=
  NefGeneric.proof (ConservationOfDegree.assembled hA hB)

theorem SectionCount.Drop.assembled (hF : SectionCount.Drop.Filt.Statement.{u, w})
    (hT : SectionCount.Drop.Term.Statement.{u, w}) (hH : SectionCount.Drop.HilbW.Statement.{u, w})
    (hR : GenericPointSectionInput.Statement.{u, w}) : SectionCount.Drop.Statement.{u, w} :=
  SectionCount.Drop.proof hF hT hH hR

theorem SectionCount.assembled (hTop : SectionCount.Top.Statement.{u, w})
    (hF : SectionCount.Drop.Filt.Statement.{u, w}) (hT : SectionCount.Drop.Term.Statement.{u, w})
    (hH : SectionCount.Drop.HilbW.Statement.{u, w}) (hR : GenericPointSectionInput.Statement.{u, w}) :
    SectionCount.Statement.{u, w} :=
  SectionCount.proof hTop (SectionCount.Drop.assembled hF hT hH hR)

theorem StepThree.assembled (hL : StepThree.OnW.Lift.Statement.{u, w})
    (hG : StepThree.OnW.Gen.Statement.{u, w}) : StepThree.Statement.{u, w} :=
  StepThree.proof StepThree.Away.full (StepThree.OnW.proof hL hG)

end GroundTheory.Heights₂.Heights.Kleiman
end
