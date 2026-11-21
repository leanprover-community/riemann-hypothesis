import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.CosetGroupMembership
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ClassesDoubleCosets
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryMassLatticeEqGenusMass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND

section
noncomputable section

namespace GlobalTheory.Proof.CosetGroupEquiv

open NumberField IsDedekindDomain Formalism.UG Formalism.BasicNotions Formalism.L2.Herm
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke

section Abstract

variable {G : Type} [Group G]

def cosetGrpEquiv (Γ K : Subgroup G) (y : G) : CosetGroupMembership.cosetGrp Γ K y ≃ stabAt Γ K y where
  toFun x := ⟨⟨x.1, ((CosetGroupMembership.mem_cosetGrp Γ K y x.1).1 x.2).1⟩, ((CosetGroupMembership.mem_cosetGrp Γ K y x.1).1 x.2).2⟩
  invFun x := ⟨x.1.1, (CosetGroupMembership.mem_cosetGrp Γ K y x.1.1).2 ⟨x.1.2, x.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_cosetGrp (Γ K : Subgroup G) (y : G) :
    Nat.card (CosetGroupMembership.cosetGrp Γ K y) = Nat.card (stabAt Γ K y) :=
  Nat.card_congr (cosetGrpEquiv Γ K y)

theorem sum_clause_iff (Γ K : Subgroup G) (m : ℝ) :
    (∀ (ι : Type) [Fintype ι] (y : ι → G),
      Function.Bijective (fun i => (DoubleCoset.mk Γ K (y i) : ClassSet Γ K)) →
      ∑ i, ((Nat.card (CosetGroupMembership.cosetGrp Γ K (y i)) : ℕ) : ℝ)⁻¹ = m) ↔
    (∀ [Fintype (ClassSet Γ K)] (s : ClassSet Γ K → G), (∀ c, DoubleCoset.mk Γ K (s c) = c) →
      ∑ c, ((Nat.card (stabAt Γ K (s c)) : ℕ) : ℝ)⁻¹ = m) := by
  constructor
  · intro h _ s hs
    have hb : Function.Bijective (fun c => (DoubleCoset.mk Γ K (s c) : ClassSet Γ K)) := by
      have : (fun c => (DoubleCoset.mk Γ K (s c) : ClassSet Γ K)) = id := funext hs
      rw [this]
      exact Function.bijective_id
    rw [← h _ s hb]
    simp only [card_cosetGrp]
  · intro h ι _ y hy
    let e : ι ≃ ClassSet Γ K := Equiv.ofBijective _ hy
    letI : Fintype (ClassSet Γ K) := Fintype.ofEquiv ι e
    have hs : ∀ c : ClassSet Γ K, DoubleCoset.mk Γ K (y (e.symm c)) = c := fun c => e.apply_symm_apply c
    rw [← h (fun c => y (e.symm c)) hs, ← e.symm.sum_comp]
    simp only [card_cosetGrp]

theorem cosetSum_iff (Γ K : Subgroup G) (m : ℝ) : CosetGroupMembership.CosetSum Γ K m ↔ ClassesDoubleCosets.CosetMass Γ K m :=
  and_congr Iff.rfl (and_congr (forall_congr' fun y => (cosetGrpEquiv Γ K y).finite_iff)
    (sum_clause_iff Γ K m))

end Abstract

section Obj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem stabHat_eq (hc : CMData F E) (S : HSpace E) (N : Submodule (𝓞 E) S.V) :
    CosetGroupMembership.stabHat hc S N = ClassesDoubleCosets.stabHat hc S N := rfl

theorem stabHat0_eq {R : Ranks} (sp : Spaces R F E) (N : Submodule (𝓞 E) (sp.X 0).V) :
    CosetGroupMembership.stabHat0 sp N = (levelAfL sp.cm.sig sp.gram0 (sp.crdLat0 N)).subgroupOf
      (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)) := by
  ext x
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

def InCoords (hc : CMData F E) {k : ℕ} (J : Matrix (Fin k) (Fin k) E) (Λ : Submodule (𝓞 E) (Fin k → E))
    (m : ℝ) : Prop :=
  CosetGroupMembership.CosetSum ((ratPts hc.sig J (Af F)).subgroupOf (UPts hc.sig J (Af F)))
    ((stabGL (hatL (F := F) Λ)).subgroupOf (UPts hc.sig J (Af F))) m

theorem inCoords_cast (hc : CMData F E) (S : HSpace E) {k : ℕ} (h : S.rank = k) (N : Submodule (𝓞 E) S.V)
    (m : ℝ) :
    InCoords hc S.gram (crdLat S N) m ↔
    InCoords hc (S.gram.reindex (finCongr h) (finCongr h))
      (N.map (((S.frame.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm) :
        S.V ≃ₗ[E] (Fin k → E)) : S.V →ₗ[E] (Fin k → E)).restrictScalars (𝓞 E))) m := by
  subst h
  rfl

theorem general_clause_iff {R : Ranks} (sp : Spaces R F E) (N : Submodule (𝓞 E) (sp.X 0).V) (m : ℝ) :
    CosetGroupMembership.CosetSum (UFin sp.cm (sp.X 0)) (CosetGroupMembership.stabHat sp.cm (sp.X 0) N) m ↔
    CosetGroupMembership.CosetSum (CosetGroupMembership.rat0 sp) (CosetGroupMembership.stabHat0 sp N) m :=
  inCoords_cast sp.cm (sp.X 0) sp.rank0 N m

end Obj

theorem general_iff : CosetGroupMembership.GeneralForm ↔ ClassesDoubleCosets.General := by
  unfold CosetGroupMembership.GeneralForm ClassesDoubleCosets.General
  simp only [cosetSum_iff, stabHat_eq]

theorem column_iff (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    CosetGroupMembership.ColumnForm D ↔ ClassesDoubleCosets.DefiniteSpaceClassStatement D Lv u := by
  letI := D.host.cmStar
  unfold CosetGroupMembership.ColumnForm ClassesDoubleCosets.DefiniteSpaceClassStatement
  refine forall_congr' fun N => forall_congr' fun _ => forall_congr' fun _ => ?_
  rw [cosetSum_iff, stabHat0_eq]
  rfl

theorem column_of_general (h : CosetGroupMembership.GeneralForm) (D : D7) : CosetGroupMembership.ColumnForm D := by
  letI := D.host.cmStar
  intro N hN hU
  exact (general_clause_iff D.sp N _).1
    (h D.host.F D.host.E D.sp.cm (D.sp.X 0) (D.sp.X_sig 0) (baseSpace_posDef D.R D.host.F D.sp) N hN hU)

theorem massAsCosetSum_iff : CosetGroupMembership.MassAsCosetSum ↔ ClassesDoubleCosets.ClassesAsDoubleCosets :=
  ⟨fun h => ⟨general_iff.1 h.1, fun D Lv u => (column_iff D Lv u).1 (h.2 D)⟩,
    fun h => ⟨general_iff.2 h.1, column_of_general (general_iff.2 h.1)⟩⟩

end GlobalTheory.Proof.CosetGroupEquiv

end
end

section
noncomputable section

namespace GlobalTheory.Proof.TotallyDefiniteMass

open NumberField IsDedekindDomain Formalism.UG Formalism.UG.CS Formalism.BasicNotions Formalism.L2.Herm
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke

theorem mass_tMap {K V V' : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V']
    [IsScalarTower (𝓞 K) K V'] {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
    (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.mass h L = Formalism.HermitianLatticesTheory.mass h' (Formalism.MainNotions.StandardLattice.tMap e L) := by
  by_cases hex : ∃ s', Formalism.ThetaLiftIndependence.IsClassReps h' (Formalism.MainNotions.StandardLattice.tMap e L) s'
  · refine Formalism.MainNotions.StandardLattice.mass_transport e he L hex fun s hs => ?_
    rw [Formalism.HermitianLatticesTheory.massBasic_mass_eq h' _ hex]
    apply Complex.ofReal_injective
    rw [Formalism.HermitianLatticesTheory.massBasic_sum_cast, Formalism.HermitianLatticesTheory.massBasic_sum_cast]
    exact Formalism.ThetaLiftIndependence.latLiftIndep K V' h' _ _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) _ _ hex.choose_spec hs
  · have hex' : ¬ ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s := fun ⟨s, hs⟩ => hex ⟨_, Formalism.MainNotions.StandardLattice.tMap_reps e he L s hs⟩
    unfold Formalism.HermitianLatticesTheory.mass
    rw [dif_neg hex, dif_neg hex']

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem isTotDef_gram (hc : CMData F E) (S : HSpace E) (h1 : S.SigOK) (h2 : S.IsPosDef) :
    IsTotDef hc.sig S.gram := by
  obtain ⟨hσ, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND F E hc
  refine ⟨hc.totReal, fun ι => ?_⟩
  letI : Algebra F ℂ := ((algebraMap ℝ ℂ).comp ι).toAlgebra
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let τ : E →ₐ[F] ℂ := IsAlgClosed.lift
  refine (Formalism.UG.Final.DefSig F E _ hc.sig S.gram ι (τ : E →+* ℂ) (RingHom.ext (hσ.2.2.2 (τ : E →+* ℂ)))
    (RingHom.ext fun a => τ.commutes a) (fun e he => (hc.fixed e).1 he)
    (Matrix.ext fun i j => (hJ S).1 i j) (hJ S).2.isUnit).2 (Or.inl ?_)
  have := h1 (τ : E →+* ℂ)
  rw [h2] at this
  simpa using this

theorem cosetSum (hc : CMData F E) (S : HSpace E) (h1 : S.SigOK) (h2 : S.IsPosDef)
    (N : Submodule (𝓞 E) S.V) (hN : Submodule.IsLattice E N) :
    CosetGroupMembership.CosetSum (UFin hc S) (CosetGroupMembership.stabHat hc S N) (Formalism.HermitianLatticesTheory.mass S.hT N) := by
  obtain ⟨hσ, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND F E hc
  have hd := isTotDef_gram hc S h1 h2
  have hτ : ∀ τ : E →+* ℂ, τ.comp (hc.sig : E →+* E) = (starRingEnd ℂ).comp τ :=
    fun τ => RingHom.ext (hσ.2.2.2 τ)
  have hH : IsHerm (hc.sig : E →+* E) S.gram := Matrix.ext fun i j => (hJ S).1 i j
  have hL : Submodule.IsLattice E (crdLat S N) := Formalism.MainNotions.StandardLattice.tMap_lattice (crd S) N hN
  have hf : Module.Finite (𝓞 E) (crdLat S N) := Module.Finite.iff_fg.2 hL.fg
  have hs : ∀ e, (hc.sig : E →+* E) ((hc.sig : E →+* E) e) = e := fun e => star_star e
  have hm := GlobalTheory.Mass.classMass_lattice_eq_genus_mass hσ (hJ S) hd hs (crdLat S N) hf hL.span_eq_top
  have ht : Formalism.HermitianLatticesTheory.mass S.hT N =
      Formalism.HermitianLatticesTheory.mass (formJ (hc.sig : E →+* E) hs S.gram 1 :
        (Fin S.rank → E) →ₗ⋆[E] (Fin S.rank → E) →ₗ[E] E) (crdLat S N) := by
    refine mass_tMap (crd S) (fun x y => ?_) N
    rw [hT_crd hc]
    change Matrix.toLinearMapₛₗ₂' E (starRingEnd E) (RingHom.id E) ((1 : E) • S.gram) (crd S x) (crd S y) = _
    unfold hform
    rw [Matrix.toLinearMapₛₗ₂'_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [one_smul, smul_eq_mul, RingHom.id_apply]
    change star _ * _ = star _ * _ * _
    ring
  rw [CosetGroupMembership.stabHat_eq]
  refine ⟨Formalism.UG.Final.ClassSetFiniteL F E _ hc.sig S.gram hτ hH (hJ S).2.isUnit hd _ hf hL.span_eq_top,
    fun y => (CosetGroupEquiv.cosetGrpEquiv _ _ y).finite_iff.2
      (Formalism.UG.Final.AdelicStabFiniteL F E _ hc.sig S.gram hτ hH (hJ S).2.isUnit hd _ hf hL.span_eq_top y),
    fun ι _ y hy => ?_⟩
  simp only [CosetGroupEquiv.card_cosetGrp]
  exact (GlobalTheory.Mass.classMass_eq_sum_of_bijective y hy).symm.trans (hm.trans ht.symm)

theorem generalForm : CosetGroupMembership.GeneralForm :=
  fun _ _ _ _ _ _ _ _ hc S h1 h2 N hN _ => cosetSum hc S h1 h2 N hN

theorem massAsCosetSum : CosetGroupMembership.MassAsCosetSum :=
  ⟨generalForm, CosetGroupEquiv.column_of_general generalForm⟩

end GlobalTheory.Proof.TotallyDefiniteMass

end
end
