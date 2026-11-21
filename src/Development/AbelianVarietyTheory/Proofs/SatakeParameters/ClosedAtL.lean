import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamGaloisSideIffDeRhamAtLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedOfCover
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverExists
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverPull
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisRepConjInvariant

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong
open TensorProduct Module GlobalTheory.CoeffExt

namespace GlobalTheory.SstModel

section Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L L' : FinExt l}
  {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  {V' : Type} [AddCommGroup V'] [Module ↥L.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L.1 V']
  [Module ↥L'.1 V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  {ρ : Representation ↥L.1 ↥(GK K) V} {ρ' : Representation ↥L'.1 ↥(GK K) V'}
  {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[↥L.1] (ι → V)}

theorem isSst_of_coord_rev [Nonempty ι] (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (h : IsSst P ρ') :
    IsSst P ρ := by
  have hm : ∀ x : V' ⊗[ℚ_[l]] Bst P, x ∈ Dst P ρ' ↔ ∀ i, tensCoord E (Bst P) x i ∈ Dst P ρ := fun x => by
    simp only [mem_Dst]
    refine ⟨fun hx i g => by rw [← GlobalTheory.PstExt.tensCoord_stRep P hE, hx g], fun hx g => ?_⟩
    exact (tensCoord E (Bst P)).injective (funext fun i => by rw [GlobalTheory.PstExt.tensCoord_stRep P hE, hx i g])
  let e : ↥(Dst P ρ') ≃ₗ[ℚ_[l]] (ι → ↥(Dst P ρ)) :=
    { toFun := fun x i => ⟨tensCoord E (Bst P) x.1 i, (hm _).1 x.2 i⟩
      invFun := fun y => ⟨(tensCoord E (Bst P)).symm fun i => (y i).1, (hm _).2 fun i => by
        rw [LinearEquiv.apply_symm_apply]; exact (y i).2⟩
      map_add' := fun x y => funext fun i => Subtype.ext (congrFun (map_add (tensCoord E (Bst P)) x.1 y.1) i)
      map_smul' := fun c x => funext fun i =>
        Subtype.ext (congrFun (((tensCoord E (Bst P)).restrictScalars ℚ_[l]).map_smul c x.1) i)
      left_inv := fun x => Subtype.ext ((tensCoord E (Bst P)).symm_apply_apply x.1)
      right_inv := fun y => funext fun i =>
        Subtype.ext (congrFun ((tensCoord E (Bst P)).apply_symm_apply fun i => (y i).1) i) }
  rw [GlobalTheory.AboveL.RepConj.isSst_iff] at h ⊢
  rw [e.finrank_eq, (E.restrictScalars ℚ_[l]).finrank_eq, GlobalTheory.AboveL.RepConj.finrank_pi_card,
    GlobalTheory.AboveL.RepConj.finrank_pi_card, mul_left_comm] at h
  exact Nat.eq_of_mul_eq_mul_left Fintype.card_pos h

end Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {m : ℕ}

theorem isSst_of_enlarge {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {L₁ L₂ : FinExt l}
    (hL : L₁.1 ≤ L₂.1) (r₁ : ↥Gw →* GL (Fin m) ↥L₁.1)
    (h : IsSst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁))) :
    IsSst P (Bw.repE L₁ r₁) := by
  let _ : Algebra ↥L₁.1 ↥L₂.1 := (IntermediateField.inclusion hL).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] ↥L₁.1 ↥L₂.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := L₂.2
  have : FiniteDimensional ↥L₁.1 ↥L₂.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  have : Nonempty (Fin (finrank ↥L₁.1 ↥L₂.1)) := ⟨⟨0, finrank_pos⟩⟩
  have hρ : ∀ g, ∃ M : Matrix (Fin m) (Fin m) ↥L₁.1, (∀ x, Bw.repE L₁ r₁ g x = M.mulVec x) ∧
      ∀ x, Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x =
        (M.map (algebraMap ↥L₁.1 ↥L₂.1)).mulVec x :=
    fun g => ⟨r₁ (Bw.e.symm g), fun _ => rfl, fun _ => rfl⟩
  exact isSst_of_coord_rev P (E := vecCoord ↥L₁.1 ↥L₂.1 m) (vecCoord_rep hρ) h

theorem isSst_of_isModel {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {Bw : LocBridge l E Ω Gw O} {r : ↥Gw →* GL (Fin m) (Om l)}
    {L : FinExt l} {r' : ↥Gw →* GL (Fin m) ↥L.1} (hm : IsModel Bw r L r') (hs : IsSstAt P Bw r) :
    IsSst P (Bw.repE L r') := by
  obtain ⟨L₁, r₁, h₁, hp⟩ := hs
  have l₁ : L₁.1 ≤ (supExt L₁ L).1 := le_sup_left
  have l₂ : L.1 ≤ (supExt L₁ L).1 := le_sup_right
  have e := IsModel.unique Bw r (h₁.enlarge l₁) (hm.enlarge l₂)
  have h3 := GlobalTheory.AboveL.RepConj.isSst_enlarge P Bw l₁ r₁ hp
  rw [e] at h3
  exact isSst_of_enlarge P Bw l₂ r' h3

end GlobalTheory.SstModel

namespace GlobalTheory.SstModel

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r : ↥Gw →* GL (Fin a) (Om l)) (LL' : FinExt l) (r' : ↥Gw →* GL (Fin a) ↥LL'.1), IsModel Bw r LL' r' → IsSstAt P Bw r → IsSst P (Bw.repE LL' r') := by
  intro l _ P AI _ E Ω _ _ _ Gw O _ _ _ Bw a r LL' r' hm hs
  exact isSst_of_isModel P hm hs

end GlobalTheory.SstModel

end
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

noncomputable section

namespace GlobalTheory.LimitTop

open Matrix Formalism.WeaklyAdmissibleFiltrations

theorem closedAtL : ClosedAtL := by
  intro E Ω _ _ _ _ _ l _ a ha P AI hT w A hA O _ _ _ Bw hBw J r hr hss C hC hρ
  classical
  obtain ⟨T⟩ := hT

  let jl : ↥(GK Bw.Kw) →* Formalism.ConjugateSelfDual.G E Ω := (ReciprocityTheory.Gal.Dec (F := E) A).subtype.comp Bw.e.symm.toMonoidHom
  have hjl : Continuous jl := continuous_subtype_val.comp Bw.e_symm_cont

  let jE : E →+* ↥Bw.Kw.1 := (Bw.j.comp (algebraMap E Ω)).codRestrict Bw.Kw.1 Bw.j_E
  let J' : (↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l) → Multiset ℤ := fun τ'' => J (τ''.toRingHom.comp jE)
  obtain ⟨Cv⟩ := GlobalTheory.TraceConjugationCover.cover_exists l (Formalism.ConjugateSelfDual.G E Ω) a Bw.LL r hr hss C (fun ρ hm => (hρ ρ hm).1) hC
  obtain ⟨Cv'⟩ := GlobalTheory.BKLim.cover_pull l (Formalism.ConjugateSelfDual.G E Ω) ↥(GK Bw.Kw) jl hjl a Bw.LL r C Cv

  have tr : ∀ (ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)) (L : FinExt l) (r' : ↥(GK Bw.Kw) →* GL (Fin a) ↥L.1)
      (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)), Bw.LL.1 ≤ L.1 →
      (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i k, (((r' g).val i k : ↥L.1) : Om l) = ((ρ.comp jl) g).val i k) →
      IsModel Bw (ρ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) L (r'.comp Bw.e.toMonoidHom) ∧
        Bw.repE L (r'.comp Bw.e.toMonoidHom) = R := by
    intro ρ L r' R hle hR he
    refine ⟨⟨hle, ?_⟩, ?_⟩
    · ext g i k
      have := he (Bw.e g) i k
      simpa [jl, mapRep] using this
    · refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
      rw [hR]
      simp [LocBridge.repE, Matrix.toLin'_apply]

  have hCl : ∀ ρ₁ ∈ (fun ρ => ρ.comp jl) '' C, ∀ (L : FinExt l) (r' : ↥(GK Bw.Kw) →* GL (Fin a) ↥L.1)
      (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)), Bw.LL.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) →
      (∀ g i k, (((r' g).val i k : ↥L.1) : Om l) = (ρ₁ g).val i k) →
      IsSst P R ∧ ∀ (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1) (n : ℤ), multV (P.PD Bw.Kw) R τ n = ((J' (L.1.val.comp τ)).count n : ℤ) := by
    rintro _ ⟨ρ, hm, rfl⟩ L r' R hle hR he
    obtain ⟨hmod, hrep⟩ := tr ρ L r' R hle hR he
    refine ⟨hrep ▸ GlobalTheory.SstModel.main l P AI ⟨T⟩ E Ω (ReciprocityTheory.Gal.Dec (F := E) A) O Bw a _ L _ hmod (hρ ρ hm).2.1, fun τ n => ?_⟩
    have hi : IsInduced Bw ((L.1.val.comp τ).toRingHom.comp jE) τ := fun x => rfl
    have := IsJumpsAt.count_eq P hmod hi ((hρ ρ hm).2.2 _ L τ hi) n
    rw [← hrep]
    exact this.symm
  have hcr : (∀ ρ ∈ C, IsCrysAt P Bw (ρ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) → ∀ ρ₁ ∈ (fun ρ => ρ.comp jl) '' C,
      ∀ (L : FinExt l) (r' : ↥(GK Bw.Kw) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)),
      Bw.LL.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) →
      (∀ g i k, (((r' g).val i k : ↥L.1) : Om l) = (ρ₁ g).val i k) → IsCrys (P.PD Bw.Kw) R := by
    intro hc
    rintro _ ⟨ρ, hm, rfl⟩ L r' R hle hR he
    obtain ⟨hmod, hrep⟩ := tr ρ L r' R hle hR he
    rw [← hrep]
    exact (hmod.isCrysAt_iff P).1 (hc ρ hm)

  have hcont : Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Om l))) := Units.continuous_val.comp hr
  have model : ∀ L₀ : FinExt l, ∃ (L : FinExt l) (r₁ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) ↥L.1), L₀.1 ≤ L.1 ∧ Bw.LL.1 ≤ L.1 ∧
      mapRep (algebraMap ↥L.1 (Om l)) r₁ = r := by
    intro L₀
    haveI := L₀.2
    haveI := Bw.LL.2
    obtain ⟨L, hL, hmem⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (Formalism.ConjugateSelfDual.G E Ω) a r hcont
      ⟨L₀.1 ⊔ Bw.LL.1, IntermediateField.finiteDimensional_sup _ _⟩
    obtain ⟨r₁, -, hr₁⟩ := GlobalTheory.DeRhamRead.exists_model_of_mem r hcont L hmem
    exact ⟨L, r₁, le_sup_left.trans hL, le_sup_right.trans hL, hr₁⟩

  have top : ∀ (L : FinExt l) (r₁ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) ↥L.1), Bw.LL.1 ≤ L.1 → mapRep (algebraMap ↥L.1 (Om l)) r₁ = r →
      IsModel Bw (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧
      Bw.IsdRE P L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧
      (∀ (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1) (n : ℤ),
        Bw.multE P L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) τ n = ((J' (L.1.val.comp τ)).count n : ℤ)) ∧
      ((∀ ρ ∈ C, IsCrysAt P Bw (ρ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) →
        Bw.IsCrysE P L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) := by
    intro L r₁ hle hr₁
    have hmod : IsModel Bw (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) :=
      ⟨hle, by rw [← hr₁]; rfl⟩
    obtain ⟨hdr, hmu, hcy⟩ := GlobalTheory.CovClose.closed_of_cover l Bw.Kw Bw.LL P AI T a ha Bw.LL_split (r.comp jl) _ Cv' J' hCl L
      (r₁.comp jl) (Bw.repE L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) hle
      (fun g v => by simp [LocBridge.repE, jl, Matrix.toLin'_apply]) (fun g i k => by rw [← hr₁]; rfl)
    refine ⟨hmod, ?_, hmu, fun hc => hcy (hcr hc)⟩
    have h := hdr
    unfold Formalism.MainNotions.N.IsDR at h
    rw [Module.finrank_fin_fun] at h
    exact h
  refine ⟨⟨?_, fun τ LL' τ' hi => ?_⟩, fun hc => ?_⟩
  · obtain ⟨L, r₁, -, hle, hr₁⟩ := model Bw.LL
    obtain ⟨hmod, hdr, -, -⟩ := top L r₁ hle hr₁
    exact ⟨L, _, hmod, hdr⟩
  · obtain ⟨L, r₁, hL', hle, hr₁⟩ := model LL'
    obtain ⟨hmod, hdr, hmu, -⟩ := top L r₁ hle hr₁
    let τ'' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1 := (IntermediateField.inclusion hL').comp τ'
    have hi' : IsInduced Bw τ τ'' := fun x => hi x
    have hτ : (L.1.val.comp τ'').toRingHom.comp jE = τ := RingHom.ext fun x => (hi x).symm
    refine ⟨L, _, hmod, hdr, τ'', hi', fun n => ?_⟩
    rw [hmu τ'' n]
    show ((J τ).count n : ℤ) = ((J ((L.1.val.comp τ'').toRingHom.comp jE)).count n : ℤ)
    rw [hτ]
  · obtain ⟨L, r₁, -, hle, hr₁⟩ := model Bw.LL
    obtain ⟨hmod, -, -, hcy⟩ := top L r₁ hle hr₁
    exact ⟨L, _, hmod, hcy hc⟩

end GlobalTheory.LimitTop
end
end
