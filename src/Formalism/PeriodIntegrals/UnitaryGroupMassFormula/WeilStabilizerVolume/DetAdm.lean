import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.NuInvSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoPolish

section
noncomputable section

namespace PI.VolStabW.DeterminantAdmissible

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabW.PositiveNearLattice MeasurableSpace
open scoped TensorProduct ENNReal RestrictedProduct

section Borel

variable {F : Type} [Field F] [NumberField F]

instance borel_Ainf : BorelSpace (Ainf F) := ⟨rfl⟩
instance borel_Af : BorelSpace (Af F) := ⟨rfl⟩
instance borel_AF : BorelSpace (AF F) := ⟨rfl⟩
instance borel_Fv (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (Fv F v) := ⟨rfl⟩
instance borel_tens {E : Type} [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] : BorelSpace (R ⊗[F] E) := ⟨rfl⟩

end Borel

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem isCompact_intV : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
  ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v

theorem isClopen_intV : IsClopen (v.adicCompletionIntegers F : Set (Fv F v)) :=
  ⟨(isCompact_intV v).isClosed, ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v⟩

instance lc_Fv : LocallyCompactSpace (Fv F v) :=
  (isCompact_intV v).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((isClopen_intV v).isOpen.mem_nhds (zero_mem (v.adicCompletionIntegers F)))

theorem isClopen_translate (t : Fv F v) :
    IsClopen ((Homeomorph.subRight t) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))) :=
  (isClopen_intV v).preimage (Homeomorph.subRight t).continuous

theorem isCompact_translate (t : Fv F v) :
    IsCompact ((Homeomorph.subRight t) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))) :=
  (Homeomorph.subRight t).isCompact_preimage.2 (isCompact_intV v)

theorem mem_translate (t : Fv F v) :
    t ∈ (Homeomorph.subRight t) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by
  show t - t ∈ (v.adicCompletionIntegers F : Set (Fv F v))
  rw [sub_self]
  exact zero_mem _

theorem exists_cc {W : Set (Fv F v)} (hW : IsOpen W) {t : Fv F v} (ht : t ∈ W) :
    ∃ C, IsClopen C ∧ IsCompact C ∧ t ∈ C ∧ C ⊆ W := by
  obtain ⟨V, hV, htV, hVs⟩ :=
    (loc_compact_Haus_tot_disc_of_zero_dim (H := Fv F v)).exists_subset_of_mem_open
      (⟨ht, mem_translate v t⟩ : t ∈ W ∩
        (Homeomorph.subRight t) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))) (hW.inter (isClopen_translate v t).isOpen)
  exact ⟨V, hV, (isCompact_translate v t).of_isClosed_subset hV.isClosed
    (hVs.trans inter_subset_right), htV, hVs.trans inter_subset_left⟩

theorem open_eq_sUnion {W : Set (Fv F v)} (hW : IsOpen W) :
    ∃ T : Set (Set (Fv F v)), T.Countable ∧ (∀ C ∈ T, IsClopen C ∧ IsCompact C) ∧ W = ⋃₀ T := by
  obtain ⟨T, hT, he⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun i : {C : Set (Fv F v) // IsClopen C ∧ IsCompact C ∧ C ⊆ W} => (i.1 : Set (Fv F v)))
    fun i => i.2.1.isOpen
  refine ⟨Subtype.val '' T, hT.image _, ?_, ?_⟩
  · rintro _ ⟨i, -, rfl⟩
    exact ⟨i.2.1, i.2.2.1⟩
  · rw [sUnion_image, he]
    ext t
    constructor
    · intro ht
      obtain ⟨C, h1, h2, h3, h4⟩ := exists_cc v hW ht
      exact mem_iUnion.2 ⟨⟨C, h1, h2, h4⟩, h3⟩
    · intro ht
      obtain ⟨i, hi⟩ := mem_iUnion.1 ht
      exact i.2.2.2 hi

end Local

section Box1

variable {F : Type} [Field F] [NumberField F]

theorem isCompact_finite_adele_box {D : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hc : ∀ v, IsCompact (D v))
    (hf : ∀ᶠ v in cofinite, D v = (v.adicCompletionIntegers F : Set (Fv F v))) :
    IsCompact {x : Af F | ∀ v, x v ∈ D v} := by
  let S : Set (HeightOneSpectrum (𝓞 F)) := {v | D v = (v.adicCompletionIntegers F : Set (Fv F v))}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.2 hf
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) =>
    (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  let K : Set (Πʳ v, [R v, A v]_[𝓟 S]) := {x | ∀ v, x v ∈ D v}
  have hK : IsCompact K := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]
    have e : ((↑) : Πʳ v, [R v, A v]_[𝓟 S] → ∀ v, R v) '' K = Set.pi univ D := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩ v _
        exact hx v
      · intro hg
        refine ⟨⟨g, ?_⟩, fun v => hg v (mem_univ v), rfl⟩
        rw [eventually_principal]
        intro v hv
        have h := hg v (mem_univ v)
        rwa [show D v = _ from hv] at h
    rw [e]
    exact isCompact_univ_pi hc
  have e : {x : Af F | ∀ v, x v ∈ D v} = RestrictedProduct.inclusion R A hS '' K := by
    ext x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, hx, rfl⟩
      rw [eventually_principal]
      intro v hv
      have h := hx v
      rwa [show D v = _ from hv] at h
    · rintro ⟨y, hy, rfl⟩ v
      exact hy v
  rw [e]
  exact hK.image (RestrictedProduct.continuous_inclusion hS)

theorem isOpen_finite_adele_box {D : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)} (ho : ∀ v, IsOpen (D v))
    (hf : ∀ᶠ v in cofinite, D v = (v.adicCompletionIntegers F : Set (Fv F v))) :
    IsOpen {x : Af F | ∀ v, x v ∈ D v} := by
  classical
  have hfin : {v | ¬ D v = (v.adicCompletionIntegers F : Set (Fv F v))}.Finite := hf
  set S := hfin.toFinset
  have e : {x : Af F | ∀ v, x v ∈ D v} =
      {x : Af F | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F} ∩
        ⋂ v ∈ S, {x : Af F | x v ∈ D v} := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
    constructor
    · intro h
      refine ⟨fun v hv => ?_, fun v _ => h v⟩
      have hv' : D v = (v.adicCompletionIntegers F : Set (Fv F v)) := by
        by_contra hc
        exact hv (hfin.mem_toFinset.2 hc)
      have := h v
      rwa [hv'] at this
    · rintro ⟨h1, h2⟩ v
      by_cases hv : v ∈ S
      · exact h2 v hv
      · have hv' : D v = (v.adicCompletionIntegers F : Set (Fv F v)) := by
          by_contra hc
          exact hv (hfin.mem_toFinset.2 hc)
        rw [hv']
        exact h1 v hv
  rw [e]
  refine IsOpen.inter ?_ (isOpen_biInter_finset fun v _ =>
    (ho v).preimage (RestrictedProduct.continuous_eval v))
  exact RestrictedProduct.isOpen_forall_imp_mem (TopoAF.isOpen_integers F) (p := fun v => v ∉ S)

end Box1

end PI.VolStabW.DeterminantAdmissible
end
end

section
noncomputable section

namespace PI.VolStabW.DeterminantAdmissible

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  MeasurableSpace
open scoped TensorProduct ENNReal RestrictedProduct

section Boxes

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]

def boxS (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) : Set (ι → Af F) :=
  {y | ∀ c v, y c v ∈ D c v}

def IsBoxD (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) : Prop :=
  (∀ c v, IsClopen (D c v) ∧ IsCompact (D c v)) ∧
    ∀ᶠ v in cofinite, ∀ c, D c v = (v.adicCompletionIntegers F : Set (Fv F v))

variable (F ι) in

def boxes : Set (Set (ι → Af F)) := {s | ∃ D, IsBoxD D ∧ s = boxS D}

theorem boxS_eq (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) :
    boxS D = Set.pi univ fun c => {x : Af F | ∀ v, x v ∈ D c v} := by
  ext y
  simp [boxS]

theorem isCompact_boxS {D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)} (hD : IsBoxD D) :
    IsCompact (boxS D) := by
  rw [boxS_eq]
  exact isCompact_univ_pi fun c => isCompact_finite_adele_box (fun v => (hD.1 c v).2)
    (by filter_upwards [hD.2] with v hv using hv c)

theorem isOpen_boxS {D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)} (hD : IsBoxD D) :
    IsOpen (boxS D) := by
  rw [boxS_eq]
  exact isOpen_set_pi finite_univ fun c _ => isOpen_finite_adele_box (fun v => (hD.1 c v).1.isOpen)
    (by filter_upwards [hD.2] with v hv using hv c)

theorem boxes_inter {s t : Set (ι → Af F)} (hs : s ∈ boxes F ι) (ht : t ∈ boxes F ι) :
    s ∩ t ∈ boxes F ι := by
  obtain ⟨D, hD, rfl⟩ := hs
  obtain ⟨D', hD', rfl⟩ := ht
  refine ⟨fun c v => D c v ∩ D' c v, ⟨fun c v => ⟨(hD.1 c v).1.inter (hD'.1 c v).1,
    (hD.1 c v).2.inter_right (hD'.1 c v).1.isClosed⟩, ?_⟩, ?_⟩
  · filter_upwards [hD.2, hD'.2] with v h1 h2 c
    rw [h1 c, h2 c, inter_self]
  · ext y
    simp only [boxS, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩ c v
      exact ⟨h1 c v, h2 c v⟩
    · intro h
      exact ⟨fun c v => (h c v).1, fun c v => (h c v).2⟩

theorem exists_box_mem (y : ι → Af F) : ∃ D, IsBoxD D ∧ y ∈ boxS D := by
  classical
  let D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v) := fun c v =>
    if y c v ∈ v.adicCompletionIntegers F then (v.adicCompletionIntegers F : Set (Fv F v))
    else (Homeomorph.subRight (y c v)) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))
  refine ⟨D, ⟨fun c v => ?_, ?_⟩, fun c v => ?_⟩
  · by_cases h : y c v ∈ v.adicCompletionIntegers F
    · rw [show D c v = _ from if_pos h]
      exact ⟨isClopen_intV v, isCompact_intV v⟩
    · rw [show D c v = _ from if_neg h]
      exact ⟨isClopen_translate v _, isCompact_translate v _⟩
  · filter_upwards [eventually_all.2 fun c => (y c).eventually] with v hv c
    exact if_pos (hv c)
  · by_cases h : y c v ∈ v.adicCompletionIntegers F
    · rw [show D c v = _ from if_pos h]
      exact h
    · rw [show D c v = _ from if_neg h]
      exact mem_translate v _

theorem boxes_seq : ∃ bs : ℕ → Set (ι → Af F), (∀ n, bs n ∈ boxes F ι) ∧ ⋃ n, bs n = univ := by
  obtain ⟨T, hT, he⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun s : {s // s ∈ boxes F ι} => (s.1 : Set (ι → Af F)))
    (fun s => by obtain ⟨D, hD, e⟩ := s.2; rw [e]; exact isOpen_boxS hD)
  have hU : ⋃ s ∈ T, (s.1 : Set (ι → Af F)) = univ := by
    rw [he]
    refine eq_univ_of_forall fun y => ?_
    obtain ⟨D, hD, hy⟩ := exists_box_mem y
    exact mem_iUnion.2 ⟨⟨boxS D, D, hD, rfl⟩, hy⟩
  have hne : T.Nonempty := by
    have h0 : (0 : ι → Af F) ∈ ⋃ s ∈ T, (s.1 : Set (ι → Af F)) := by
      rw [hU]
      trivial
    obtain ⟨s, hs, -⟩ := mem_iUnion₂.1 h0
    exact ⟨s, hs⟩
  obtain ⟨g, hg⟩ := hT.exists_eq_range hne
  refine ⟨fun n => (g n).1, fun n => (g n).2, ?_⟩
  rw [← hU, hg]
  ext y
  simp

open Classical in

def upd (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (c : ι)
    (v : HeightOneSpectrum (𝓞 F)) (C : Set (Fv F v)) : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v) :=
  fun c' => if c' = c then Function.update (D c) v (D c v ∩ C) else D c'

open Classical in
theorem upd_self (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (c : ι)
    (v : HeightOneSpectrum (𝓞 F)) (C : Set (Fv F v)) :
    upd D c v C c = Function.update (D c) v (D c v ∩ C) := if_pos rfl

open Classical in
theorem upd_ne (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (c : ι)
    (v : HeightOneSpectrum (𝓞 F)) (C : Set (Fv F v)) {c' : ι} (h : c' ≠ c) :
    upd D c v C c' = D c' := if_neg h

open Classical in
theorem mem_upd (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (c : ι)
    (v : HeightOneSpectrum (𝓞 F)) (C : Set (Fv F v)) (y : ι → Af F) :
    y ∈ boxS (upd D c v C) ↔ y ∈ boxS D ∧ y c v ∈ C := by
  classical
  constructor
  · intro hy
    refine ⟨fun c' w => ?_, ?_⟩
    · have h := hy c' w
      by_cases hc : c' = c
      · subst hc
        rw [upd_self] at h
        by_cases hw : w = v
        · subst hw
          rw [Function.update_self] at h
          exact h.1
        · rw [Function.update_of_ne hw] at h
          exact h
      · rw [upd_ne D c v C hc] at h
        exact h
    · have h := hy c v
      rw [upd_self, Function.update_self] at h
      exact h.2
  · rintro ⟨hy, hC⟩ c' w
    by_cases hc : c' = c
    · subst hc
      rw [upd_self]
      by_cases hw : w = v
      · subst hw
        rw [Function.update_self]
        exact ⟨hy _ _, hC⟩
      · rw [Function.update_of_ne hw]
        exact hy _ _
    · rw [upd_ne D c v C hc]
      exact hy _ _

open Classical in
theorem isBoxD_upd {D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (c : ι) (v : HeightOneSpectrum (𝓞 F)) {C : Set (Fv F v)}
    (hC : IsClopen C ∧ IsCompact C) : IsBoxD (upd D c v C) := by
  classical
  refine ⟨fun c' w => ?_, ?_⟩
  · by_cases hc : c' = c
    · subst hc
      rw [upd_self]
      by_cases hw : w = v
      · subst hw
        rw [Function.update_self]
        exact ⟨(hD.1 _ _).1.inter hC.1, (hD.1 _ _).2.inter_right hC.1.isClosed⟩
      · rw [Function.update_of_ne hw]
        exact hD.1 _ _
    · rw [upd_ne D c v C hc]
      exact hD.1 _ _
  · filter_upwards [hD.2, eventually_cofinite_ne v] with w hw hwv c'
    by_cases hc : c' = c
    · subst hc
      rw [upd_self, Function.update_of_ne hwv]
      exact hw _
    · rw [upd_ne D c v C hc]
      exact hw c'

open Classical in
theorem pre_mem (c : ι) (v : HeightOneSpectrum (𝓞 F)) (W : Set (Fv F v)) (hW : IsOpen W) :
    MeasurableSet[generateFrom (boxes F ι)] ((fun y : ι → Af F => y c v) ⁻¹' W) := by
  classical
  let m' : MeasurableSpace (ι → Af F) := generateFrom (boxes F ι)
  obtain ⟨T, hT, hTc, rfl⟩ := open_eq_sUnion v hW
  obtain ⟨bs, hbs, hbU⟩ := boxes_seq (F := F) (ι := ι)
  choose Db hDb hbe using hbs
  have e : (fun y : ι → Af F => y c v) ⁻¹' ⋃₀ T = ⋃ C ∈ T, ⋃ n, boxS (upd (Db n) c v C) := by
    ext y
    simp only [mem_preimage, mem_sUnion, mem_iUnion, mem_upd, exists_prop]
    constructor
    · rintro ⟨C, hC, hy⟩
      have hy' : y ∈ ⋃ n, bs n := by
        rw [hbU]
        trivial
      obtain ⟨n, hn⟩ := mem_iUnion.1 hy'
      exact ⟨C, hC, n, by rw [← hbe n]; exact hn, hy⟩
    · rintro ⟨C, hC, n, -, hy⟩
      exact ⟨C, hC, hy⟩
  rw [e]
  exact MeasurableSet.biUnion hT fun C hC => MeasurableSet.iUnion fun n =>
    measurableSet_generateFrom ⟨_, isBoxD_upd (hDb n) c v (hTc C hC), rfl⟩

theorem generateFrom_boxes : generateFrom (boxes F ι) = (MeasurableSpace.pi : MeasurableSpace (ι → Af F)) := by
  classical
  refine le_antisymm (generateFrom_le ?_) ?_
  · rintro _ ⟨D, hD, rfl⟩
    exact (isCompact_boxS hD).isClosed.measurableSet
  · intro s hs
    let Ev : (ι → Af F) → (ι → ∀ v : HeightOneSpectrum (𝓞 F), Fv F v) := fun y c v => y c v
    have hcont : Continuous Ev := continuous_pi fun c => continuous_pi fun v =>
      (RestrictedProduct.continuous_eval v).comp (continuous_apply c)
    have hinj : Function.Injective Ev := fun y y' h =>
      funext fun c => Subtype.ext (funext fun v => congrFun (congrFun h c) v)
    haveI : PolishSpace (ι → Af F) := TopoPolish.polish_of_lcsc _
    have hE := hcont.measurableEmbedding hinj
    have hc : ∀ c v, (borel (Fv F v)).comap (fun y : ι → Af F => y c v) ≤ generateFrom (boxes F ι) := by
      intro c v
      rw [borel, MeasurableSpace.comap_generateFrom]
      refine generateFrom_le ?_
      rintro _ ⟨W, hW, rfl⟩
      exact pre_mem c v W hW
    have hEv : (MeasurableSpace.pi : MeasurableSpace (ι → ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)).comap Ev
        ≤ generateFrom (boxes F ι) := by
      simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
      exact iSup_le fun c => iSup_le fun v => hc c v
    rw [← hinj.preimage_image s]
    exact hEv _ ⟨_, hE.measurableSet_image.2 hs, rfl⟩

end Boxes

end PI.VolStabW.DeterminantAdmissible
end
end

section
noncomputable section

namespace PI.VolStabW.DeterminantAdmissible

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabW.PositiveNearLattice MeasurableSpace PI.VolFromSW PI.VolStabW
open scoped TensorProduct ENNReal RestrictedProduct CompactlySupported

section Crd

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) {a M : ℕ}

def crdH (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    (Fin a → Fin M → R ⊗[F] E) ≃ₜ (Fin a × Fin M × Fin d → R) where
  toFun X c := crd b R (X c.1 c.2.1) c.2.2
  invFun Y x i := (Algebra.TensorProduct.basis R b).equivFun.symm (fun k => Y (x, i, k))
  left_inv X := by
    funext x i
    show (Algebra.TensorProduct.basis R b).equivFun.symm (fun k => crd b R (X x i) k) = X x i
    have e : (fun k => crd b R (X x i) k) = (Algebra.TensorProduct.basis R b).equivFun (X x i) := by
      funext k
      simp [crd, Module.Basis.equivFun_apply]
    rw [e, LinearEquiv.symm_apply_apply]
  right_inv Y := by
    funext c
    show crd b R ((Algebra.TensorProduct.basis R b).equivFun.symm (fun k => Y (c.1, c.2.1, k))) c.2.2
      = Y c
    have e : ∀ y, crd b R y c.2.2 = (Algebra.TensorProduct.basis R b).equivFun y c.2.2 := fun y => by
      simp [crd, Module.Basis.equivFun_apply]
    rw [e, LinearEquiv.apply_symm_apply]
  continuous_toFun := continuous_pi fun c =>
    (continuous_crd b R c.2.2).comp ((continuous_apply c.2.1).comp (continuous_apply c.1))
  continuous_invFun := continuous_pi fun x => continuous_pi fun i =>
    (IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap).comp
      (continuous_pi fun k => continuous_apply _)

end Crd

section Split

variable (F : Type) [Field F] [NumberField F]

def splitH (ι : Type) : (ι → AF F) ≃ₜ (ι → Ainf F) × (ι → Af F) where
  toFun Y := (fun c => fstA F (Y c), fun c => sndA F (Y c))
  invFun p c := pairA F (p.1 c) (p.2 c)
  left_inv Y := rfl
  right_inv p := rfl
  continuous_toFun := by
    refine (continuous_pi fun c => ?_).prodMk (continuous_pi fun c => ?_)
    · exact continuous_fst.comp (continuous_apply c)
    · exact continuous_snd.comp (continuous_apply c)
  continuous_invFun := continuous_pi fun c =>
    ((continuous_apply c).comp continuous_fst).prodMk ((continuous_apply c).comp continuous_snd)

end Split

section admitted

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {a M : ℕ}

def locBox (D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (v : HeightOneSpectrum (𝓞 F)) : Set (Fin a → Fin M → Fv F v ⊗[F] E) :=
  (crdH b (Fv F v)) ⁻¹' (Set.pi univ fun c => D c v)

variable {b}

theorem isClopen_locBox {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (v : HeightOneSpectrum (𝓞 F)) : IsClopen (locBox b D v) :=
  (show IsClopen (Set.pi univ fun c => D c v) from ⟨isClosed_set_pi (fun c _ => (hD.1 c v).1.isClosed),
    isOpen_set_pi finite_univ (fun c _ => (hD.1 c v).1.isOpen)⟩).preimage (crdH b (Fv F v)).continuous

theorem isCompact_locBox {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (v : HeightOneSpectrum (𝓞 F)) : IsCompact (locBox b D v) :=
  (crdH b (Fv F v)).isCompact_preimage.2 (isCompact_univ_pi fun c => (hD.1 c v).2)

theorem isSB_locBox {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (v : HeightOneSpectrum (𝓞 F)) :
    IsSB ((locBox b D v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ)) :=
  ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) (isClopen_locBox hD v)).isLocallyConstant,
    HasCompactSupport.intro' (isCompact_locBox hD v) (isClopen_locBox hD v).isClosed
      fun Y hY => Set.indicator_of_notMem hY _⟩

theorem locBox_eq_latV {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (v : HeightOneSpectrum (𝓞 F)) (hv : ∀ c, D c v = (v.adicCompletionIntegers F : Set (Fv F v))) :
    locBox b D v = latV b v := by
  ext Y
  simp only [locBox, latV, mem_preimage, Set.mem_univ_pi, Set.mem_ofPred_eq]
  constructor
  · intro h x i k
    have h1 := h (x, i, k)
    rw [hv] at h1
    exact h1
  · intro h c
    rw [hv]
    exact h c.1 c.2.1 c.2.2

theorem finprod_ite {α : Type} (P : α → Prop) [DecidablePred P] [Decidable (∀ v, P v)] (h : ∀ᶠ v in cofinite, P v) :
    ∏ᶠ v, (if P v then (1 : ℂ) else 0) = if ∀ v, P v then 1 else 0 := by
  by_cases hall : ∀ v, P v
  · rw [if_pos hall]
    exact finprod_eq_one_of_forall_eq_one fun v => if_pos (hall v)
  · rw [if_neg hall]
    push Not at hall
    obtain ⟨v0, hv0⟩ := hall
    refine finprod_eq_zero _ v0 (if_neg hv0) ?_
    refine (eventually_cofinite.1 h).subset fun v hv => ?_
    intro hP
    exact hv (if_pos hP)

theorem finprod_locBox {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (W : Fin a → Fin M → Af F ⊗[F] E) :
    ∏ᶠ v, (locBox b D v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ) (projV v W) =
      (boxS D).indicator 1 (crdH b (Af F) W) := by
  classical
  set q := crdH b (Af F) W
  have hv : ∀ v, (locBox b D v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ) (projV v W) =
      if (∀ c, q c v ∈ D c v) then 1 else 0 := by
    intro v
    have e : ∀ c, crdH b (Fv F v) (projV v W) c = q c v := fun c =>
      crd_map b (evalV F v) (W c.1 c.2.1) c.2.2
    rw [Set.indicator_apply]
    simp only [locBox, mem_preimage, Set.mem_univ_pi, e, Pi.one_apply]
  rw [finprod_congr hv, finprod_ite _ ?_]
  · rw [Set.indicator_apply]
    by_cases hq : q ∈ boxS D
    · rw [if_pos hq, if_pos (fun v c => hq c v)]
      rfl
    · rw [if_neg hq, if_neg (fun h' => hq (fun c v => h' v c))]
  · filter_upwards [hD.2, eventually_all.2 fun c => (q c).eventually] with v h1 h2 c
    rw [h1 c]
    exact h2 c

end admitted

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {a M : ℕ}

variable (F E a M) in

def psiH : (Fin a → Fin M → AF F ⊗[F] E) ≃ₜ
    (Fin a × Fin M × Fin (Module.finrank F E) → Ainf F) ×
      (Fin a × Fin M × Fin (Module.finrank F E) → Af F) :=
  (crdH (Module.finBasis F E) (AF F)).trans (splitH F _)

theorem psiH_fst (X : Fin a → Fin M → AF F ⊗[F] E) :
    (psiH F E a M X).1 = crdH (Module.finBasis F E) (Ainf F) (projInf X) := by
  funext c
  exact (crd_map (Module.finBasis F E) (fstA F) (X c.1 c.2.1) c.2.2).symm

theorem psiH_snd (X : Fin a → Fin M → AF F ⊗[F] E) :
    (psiH F E a M X).2 = crdH (Module.finBasis F E) (Af F) (projFin X) := by
  funext c
  exact (crd_map (Module.finBasis F E) (sndA F) (X c.1 c.2.1) c.2.2).symm

theorem key_int (ν1 ν2 : Measure (Fin a → Fin M → AF F ⊗[F] E))
    (h : ∀ Φ, IsAdm F E Φ → ∫ X, Φ X ∂ν1 = ∫ X, Φ X ∂ν2)
    {D : Fin a × Fin M × Fin (Module.finrank F E) → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (f : C_c(Fin a × Fin M × Fin (Module.finrank F E) → Ainf F, ℝ)) :
    ∫ X, f (psiH F E a M X).1 * (boxS D).indicator (fun _ => (1 : ℝ)) (psiH F E a M X).2 ∂ν1 =
      ∫ X, f (psiH F E a M X).1 * (boxS D).indicator (fun _ => (1 : ℝ)) (psiH F E a M X).2 ∂ν2 := by
  classical
  let b := Module.finBasis F E
  let Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ := fun Y => ((f (crdH b (Ainf F) Y) : ℝ) : ℂ)
  let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ :=
    fun v => (locBox b D v).indicator 1
  let Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ := fun W => ∏ᶠ v, Φv v (projV v W)
  let Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ := fun X => Φinf (projInf X) * Φf (projFin X)
  have hadm : IsAdm F E Φ := by
    refine ⟨_, b, Φinf, Φf, Φv, ?_, ?_, ⟨fun v => isSB_locBox hD v, ?_, fun _ => rfl⟩, fun _ => rfl⟩
    · exact Complex.continuous_ofReal.comp (f.continuous.comp (crdH b (Ainf F)).continuous)
    · exact (f.hasCompactSupport.comp_homeomorph (crdH b (Ainf F))).comp_left Complex.ofReal_zero
    · filter_upwards [hD.2] with v hv
      exact congrArg (fun s => s.indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ)) (locBox_eq_latV v hv)
  have hΦ : ∀ X, Φ X = ((f (psiH F E a M X).1 *
      (boxS D).indicator (fun _ => (1 : ℝ)) (psiH F E a M X).2 : ℝ) : ℂ) := by
    intro X
    have e2 : Φf (projFin X) = (boxS D).indicator 1 ((psiH F E a M X).2) := by
      rw [psiH_snd]
      exact finprod_locBox hD (projFin X)
    simp only [Φ, e2, psiH_fst, Φinf, b]
    rw [Complex.ofReal_mul]
    congr 1
    by_cases hq : (psiH F E a M X).2 ∈ boxS D
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
      simp
    · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]
      simp
  have := h Φ hadm
  simp only [hΦ] at this
  rw [integral_complex_ofReal, integral_complex_ofReal] at this
  exact_mod_cast this

end Main

end PI.VolStabW.DeterminantAdmissible
end
end

section
noncomputable section

namespace PI.VolStabW.DeterminantAdmissible

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabW.PositiveNearLattice MeasurableSpace PI.VolFromSW PI.VolStabW
open scoped TensorProduct ENNReal RestrictedProduct CompactlySupported

theorem detAdm_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {a M : ℕ} (ν1 ν2 : Measure (Fin a → Fin M → AF F ⊗[F] E))
    (h1 : ∀ K, IsCompact K → ν1 K < ⊤) (h2 : ∀ K, IsCompact K → ν2 K < ⊤)
    (h : ∀ Φ, IsAdm F E Φ → ∫ X, Φ X ∂ν1 = ∫ X, Φ X ∂ν2) : ν1 = ν2 := by
  classical
  let ι := Fin a × Fin M × Fin (Module.finrank F E)
  let Ψ := psiH F E a M
  let Ψm := Ψ.toMeasurableEquiv
  have hfin : ∀ ν : Measure (Fin a → Fin M → AF F ⊗[F] E), (∀ K, IsCompact K → ν K < ⊤) →
      ∀ K, IsCompact K → ν.map Ψm K < ⊤ := by
    intro ν hν K hK
    rw [Ψm.map_apply]
    exact hν _ (Ψ.isCompact_preimage.2 hK)
  suffices hμ : ν1.map Ψm = ν2.map Ψm by
    rw [← Ψm.map_symm_map (μ := ν1), ← Ψm.map_symm_map (μ := ν2), hμ]
  set μ1 := ν1.map Ψm with hμ1
  set μ2 := ν2.map Ψm with hμ2

  have hbox : ∀ D, IsBoxD D → ∀ U : Set (ι → Ainf F), MeasurableSet U →
      μ1 (U ×ˢ boxS D) = μ2 (U ×ˢ boxS D) := by
    intro D hD
    let ρ := fun μ : Measure ((ι → Ainf F) × (ι → Af F)) =>
      (μ.restrict (univ ×ˢ boxS D)).map Prod.fst
    have hβ : MeasurableSet (boxS D) := (isCompact_boxS hD).isClosed.measurableSet
    have hρ : ∀ μ U, MeasurableSet U → ρ μ U = μ (U ×ˢ boxS D) := by
      intro μ U hU
      simp only [ρ]
      rw [Measure.map_apply measurable_fst hU, Measure.restrict_apply (measurable_fst hU)]
      congr 1
      ext p
      simp
    have hint : ∀ μ (f : C_c(ι → Ainf F, ℝ)), ∫ x, f x ∂(ρ μ) =
        ∫ p, f p.1 * (boxS D).indicator (fun _ => (1 : ℝ)) p.2 ∂μ := by
      intro μ f
      simp only [ρ]
      rw [integral_map measurable_fst.aemeasurable (map_continuous f).aestronglyMeasurable,
        ← integral_indicator (MeasurableSet.univ.prod hβ)]
      congr 1
      funext p
      by_cases hp : p.2 ∈ boxS D
      · rw [Set.indicator_of_mem (mk_mem_prod (mem_univ p.1) hp : p ∈ univ ×ˢ boxS D),
          Set.indicator_of_mem hp, mul_one]
      · rw [Set.indicator_of_notMem (fun h' => hp h'.2), Set.indicator_of_notMem hp, mul_zero]
    have hfc : ∀ μ : Measure ((ι → Ainf F) × (ι → Af F)), (∀ K, IsCompact K → μ K < ⊤) →
        IsFiniteMeasureOnCompacts (ρ μ) := fun μ hμ =>
      ⟨fun K hK => by
        rw [hρ μ K hK.measurableSet]
        exact hμ _ (hK.prod (isCompact_boxS hD))⟩
    have := hfc μ1 (hfin ν1 h1)
    have := hfc μ2 (hfin ν2 h2)
    have hρeq : ρ μ1 = ρ μ2 := Measure.ext_of_integral_eq_on_compactlySupported fun f => by
      rw [hint, hint, hμ1, hμ2, integral_map_equiv, integral_map_equiv]
      exact key_int ν1 ν2 h hD f
    intro U hU
    rw [← hρ μ1 U hU, ← hρ μ2 U hU, hρeq]

  obtain ⟨bs, hbs, hbU⟩ := boxes_seq (F := F) (ι := ι)
  refine Measure.ext_of_generateFrom_of_iUnion
    (image2 (· ×ˢ ·) {U : Set (ι → Ainf F) | MeasurableSet U} (boxes F ι))
    (fun n => compactCovering (ι → Ainf F) n.unpair.1 ×ˢ bs n.unpair.2) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← generateFrom_prod_eq isCountablySpanning_measurableSet ⟨bs, hbs, hbU⟩,
      generateFrom_boxes, MeasurableSpace.generateFrom_measurableSet]
  · rintro _ ⟨U, hU, β, hβ, rfl⟩ _ ⟨U', hU', β', hβ', rfl⟩ _
    rw [prod_inter_prod]
    have hU2 : MeasurableSet U := hU
    have hU2' : MeasurableSet U' := hU'
    exact mem_image2_of_mem (hU2.inter hU2') (boxes_inter hβ hβ')
  · refine eq_univ_of_forall fun p => mem_iUnion.2 ?_
    have h1' : p.1 ∈ ⋃ m, compactCovering (ι → Ainf F) m := by
      rw [iUnion_compactCovering]
      trivial
    have h2' : p.2 ∈ ⋃ n, bs n := by
      rw [hbU]
      trivial
    obtain ⟨m, hm⟩ := mem_iUnion.1 h1'
    obtain ⟨n, hn⟩ := mem_iUnion.1 h2'
    refine ⟨Nat.pair m n, ?_⟩
    simp only [Nat.unpair_pair]
    exact ⟨hm, hn⟩
  · intro n
    exact mem_image2_of_mem (show MeasurableSet (compactCovering (ι → Ainf F) n.unpair.1) from
      (isCompact_compactCovering _ _).measurableSet) (hbs _)
  · intro n
    obtain ⟨D, hD, e⟩ := hbs n.unpair.2
    rw [e]
    exact (hfin ν1 h1 _ ((isCompact_compactCovering _ _).prod (isCompact_boxS hD))).ne
  · rintro _ ⟨U, hU, β, ⟨D, hD, rfl⟩, rfl⟩
    exact hbox D hD U hU

end PI.VolStabW.DeterminantAdmissible

namespace PI.VolStabW

theorem detAdm_holds : DetAdm := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ν1 ν2 h1 h2 h
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact DeterminantAdmissible.detAdm_gen ν1 ν2 h1 h2 h

end PI.VolStabW
end
end
