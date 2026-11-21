import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelKernelBoundedRepresentableOfCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSiegelObjectPolarisationKernelKilled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToSiegAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyNoetherianOfIsQProjOverNoeth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorStructuresRepresentableSiegelBaseChaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepresentingFamilyOfAuxiliaryRepresentatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionStatement

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_siegelObject_polarisationKernel_killed : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (h M : ℕ) (t₁ : S ⟶ Sp (cycAway M)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ lev) (e : ℕ), e.Coprime p → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → SiegKerBy (o.toSieg hl) e := by
  first | (exact @GlobalTheory.UPel.HT.KerBy.siegKerBy_toSieg) | (exact GlobalTheory.UPel.HT.KerBy.siegKerBy_toSieg) | (intros; apply GlobalTheory.UPel.HT.KerBy.siegKerBy_toSieg <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.CycAwayQProj

theorem finiteType_closure {K : Type} [CommRing K] {s : Set K} (hs : s.Finite) :
    (Int.castRingHom (Subring.closure s)).FiniteType := by
  have h : Algebra.FiniteType ℤ (Algebra.adjoin ℤ s) :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨s, hs, rfl⟩)
  have e : Algebra.adjoin ℤ s ≃+* Subring.closure s :=
    RingEquiv.subringCongr (s := (Algebra.adjoin ℤ s).toSubring) (by rw [Algebra.adjoin_int]; rfl)
  have h' : Algebra.FiniteType ℤ (Subring.closure s) := h.equiv (AlgEquiv.ofRingEquiv (f := e) fun x => by simp)
  have := RingHom.finiteType_algebraMap.2 h'
  rwa [RingHom.eq_intCast' (algebraMap ℤ (Subring.closure s))] at this

theorem finiteType_cycAway (M : ℕ) : (Int.castRingHom (cycAway M)).FiniteType :=
  finiteType_closure (Set.toFinite _)

theorem isQProjOver_comp_spMap {A B : Type} [CommRing A] [CommRing B] {f : A →+* B} (hf : f.FiniteType)
    {Y : Scheme.{0}} {s : Y ⟶ Sp B} (h : IsQProjOver s) : IsQProjOver (s ≫ spMap f) := by
  obtain ⟨_, hL⟩ := (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB s).1 h
  have : LocallyOfFiniteType (spMap f) := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 hf
  exact (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB _).2 ⟨inferInstance, hL⟩

theorem isQProjOver_of_isFinite_pullback : ∀ (M : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R], IsUnit ((M : ℕ) : R) → ∀ (Y : Scheme.{0}) (s : Y ⟶ Sp (cycAway M)), IsQProjOver s → ∀ (Z : Scheme.{0}) (π : Z ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))), IsFinite π → IsQProjOver (π ≫ pullback.snd _ _) :=
  fun M _ _ _ _ _ _ hs _ π _ =>
    isQProjOver_comp_of_isFinite π
      (isQProjOver_of_isPullback (IsPullback.of_hasPullback _ _) (isQProjOver_comp_spMap (finiteType_cycAway M) hs))

end GlobalTheory.CycAwayQProj
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQuasiProjective_of_finite_over_cyclotomicAway_pullback : ∀ (M : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R], IsUnit ((M : ℕ) : R) → ∀ (Y : Scheme.{0}) (s : Y ⟶ Sp (cycAway M)), IsQProjOver s → ∀ (Z : Scheme.{0}) (π : Z ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))), IsFinite π → IsQProjOver (π ≫ pullback.snd _ _) := by
  first | (exact @GlobalTheory.CycAwayQProj.isQProjOver_of_isFinite_pullback) | (exact GlobalTheory.CycAwayQProj.isQProjOver_of_isFinite_pullback) | (intros; apply GlobalTheory.CycAwayQProj.isQProjOver_of_isFinite_pullback  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyNoetherian_of_isQProjOver_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (f : X ⟶ Sp R), IsQProjOver f → IsLocallyNoetherian X := by
  first | exact @GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth | exact GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth | (intros; apply GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

theorem harrisTaylorModuli_symplecticLevel_representable : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → SDRep (Module.finrank ℤ D.La / 2) M e → HasLevelStructureOfLevel b N (Module.finrank ℤ D.La / 2) M := by
  intro p _ D R _ _ b N M e hN hNp hM hMo hMp hep _ hdual hSD
  obtain ⟨X, s, u, hku, -, hqs, huniv⟩ := hSD
  have hMR : IsUnit ((M : ℕ) : R) := b.unit M hMp
  have hqP : IsQProjOver (𝟙 _ ≫ pullback.snd (s ≫ spMap (Int.castRingHom (cycAway M)))
      (spMap (Int.castRingHom R))) :=
    GlobalTheory.T.isQuasiProjective_of_finite_over_cyclotomicAway_pullback M R hMR X s hqs _ (𝟙 _) inferInstance
  rw [Category.id_comp] at hqP
  have hLN := GlobalTheory.T.isLocallyNoetherian_of_isQProjOver_noetherian R _ _ hqP
  obtain ⟨Z, π, v, lev, hlev, hfin, hfwd, hback⟩ :=
    GlobalTheory.T.harrisTaylor_structures_representable_siegel_baseChange p D R b N (Module.finrank ℤ D.La / 2) M e hN hNp hM hMo hMp hep X s u hku hLN
  refine ⟨Z, π ≫ pullback.snd _ _, π ≫ pullback.fst _ _ ≫ s, v, lev, hlev,
    GlobalTheory.T.isQuasiProjective_of_finite_over_cyclotomicAway_pullback M R hMR X s hqs Z π hfin, ?_⟩
  intro S t t₁ o l hl
  have heS : IsUnit ((e : ℕ) : Γ(S, ⊤)) := by
    have h := (b.unit e hep).map ((t.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    simpa using h
  obtain ⟨f₀, ⟨hf₀s, hf₀pb⟩, hf₀u⟩ :=
    huniv S t₁ (o.toSieg hl) heS (GlobalTheory.T.harrisTaylor_siegelObject_polarisationKernel_killed p D R b N S t o _ M t₁ l hl e hep hdual)
  obtain ⟨g, ⟨hg₁, hg₂, hgm⟩, hgu⟩ := hback S f₀ t t₁ o l hl hf₀pb
  refine ⟨g, ⟨hg₂, ?_, hgm⟩, ?_⟩
  · rw [← hf₀s, ← hg₁]
    simp only [Category.assoc]
  · rintro g' ⟨hg's, hg's₁, hg'm⟩
    have hfst : g' ≫ π ≫ pullback.fst _ _ = f₀ :=
      hf₀u _ ⟨by simpa only [Category.assoc] using hg's₁, hfwd S g' t t₁ o l hl hg'm⟩
    exact hgu g' ⟨hfst, hg's, hg'm⟩

end GlobalTheory.UPel.HT
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_auxiliary_symplectic_level_representable : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → SDRep (Module.finrank ℤ D.La / 2) M e → HasLevelStructureOfLevel b N (Module.finrank ℤ D.La / 2) M := by
  first | (exact @GlobalTheory.UPel.HT.harrisTaylorModuli_symplecticLevel_representable) | (exact GlobalTheory.UPel.HT.harrisTaylorModuli_symplecticLevel_representable) | (intros; apply GlobalTheory.UPel.HT.harrisTaylorModuli_symplecticLevel_representable  <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

theorem exists_repFam_qproj : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∃ F : RepFam b N, IsQProjOver F.s := by
  intro p _ D R _ _ b N hN hNp
  obtain ⟨e, hep, he⟩ := D.perfP
  have hp := (Fact.out : p.Prime)
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      rw [Nat.coprime_zero_left] at hep
      exact absurd hep hp.one_lt.ne'
    · exact h
  obtain ⟨M, hMge, hMp⟩ := Nat.exists_infinite_primes (p + e + 3)
  have hM3 : 3 ≤ M := by omega
  have hModd : Odd M := hMp.odd_of_ne_two (by omega)
  have hMcp : M.Coprime p := (Nat.coprime_primes hMp hp).2 (by omega)
  have hMe : M.Coprime e := (Nat.Prime.coprime_iff_not_dvd hMp).2 fun h => by
    have := Nat.le_of_dvd he0 h
    omega
  have hg : 1 ≤ Module.finrank ℤ D.La / 2 := by
    have := D.two_le_finrank_La
    omega
  exact GlobalTheory.T.exists_representingFamily_of_auxiliaryRepresentation p D R b N M e hN hNp hM3 hModd hMcp hep hMe he
    (GlobalTheory.T.harrisTaylor_auxiliary_symplectic_level_representable p D R b N M e hN hNp hM3 hModd hMcp hep hMe he
      (GlobalTheory.T.siegelKernelBoundedRepresentable_of_coprime _ M e hg hM3 hModd he0 hMe))

end GlobalTheory.UPel.HT
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quasiProjective_harrisTaylor_family : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∃ F : RepFam b N, IsQProjOver F.s := by
  first | (exact @GlobalTheory.UPel.HT.exists_repFam_qproj) | (exact GlobalTheory.UPel.HT.exists_repFam_qproj) | (intros; apply GlobalTheory.UPel.HT.exists_repFam_qproj  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem model_nonempty : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → Nonempty (Model b N) := by
  intro p _ D R _ _ b N hN hp
  obtain ⟨F, q⟩ := GlobalTheory.T.exists_quasiProjective_harrisTaylor_family p D R b N hN hp
  exact ⟨⟨F.X, F.s, q, GlobalTheory.T.smoothOfRelativeDimension_repFam_of_isQProjOver p D R b N hN hp F q, F.univ, F.rep⟩⟩

end GlobalTheory.UPel.HT
end
