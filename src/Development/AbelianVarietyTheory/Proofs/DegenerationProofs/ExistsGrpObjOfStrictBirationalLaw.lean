import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StrictModelTranslatesTwistCompatibleStatement
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GlueModelsOverSubfield
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelMapGenericallyOpenImmersionCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TranslationBySection
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelExtensionOfDefinedAtPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GrpObjOfDenseOpen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyIntegralOfIsIntegralOfIsAlgClosed

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.GlueCompat

set_option backward.isDefEq.respectTransparency false

noncomputable def coverTwo {X U V : Scheme.{0}} (u : U ⟶ X) (v : V ⟶ X) [IsOpenImmersion u] [IsOpenImmersion v]
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v) : X.OpenCover :=
  let T : Bool → Scheme.{0} := fun i => Bool.rec U V i
  let t : ∀ i, T i ⟶ X := fun i => Bool.rec (motive := fun i => T i ⟶ X) u v i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by cases i <;> assumption
  Scheme.Cover.mkOfCovers Bool T t (fun x => by
    rcases hc x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩)

theorem target_two (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P] {X Y U V U' V' : Scheme.{0}}
    {f : X ⟶ Y} {u : U ⟶ Y} {v : V ⟶ Y} [IsOpenImmersion u] [IsOpenImmersion v]
    (hc : ∀ x : Y, x ∈ Set.range u ∨ x ∈ Set.range v) {a : U' ⟶ X} {b : U' ⟶ U} {c : V' ⟶ X} {d : V' ⟶ V}
    (h₁ : IsPullback a b f u) (h₂ : IsPullback c d f v) (hb : P b) (hd : P d) : P f := by
  refine IsZariskiLocalAtTarget.of_openCover (coverTwo u v hc) ?_
  rintro (_ | _)
  · change P (pullback.snd f u)
    rwa [← h₁.isoPullback_inv_snd, P.cancel_left_of_respectsIso]
  · change P (pullback.snd f v)
    rwa [← h₂.isoPullback_inv_snd, P.cancel_left_of_respectsIso]

theorem source_two (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtSource P] {X Y U V : Scheme.{0}}
    {f : X ⟶ Y} {u : U ⟶ X} {v : V ⟶ X} [IsOpenImmersion u] [IsOpenImmersion v]
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v) (hb : P (u ≫ f)) (hd : P (v ≫ f)) : P f := by
  refine IsZariskiLocalAtSource.of_openCover (coverTwo u v hc) ?_
  rintro (_ | _)
  · exact hb
  · exact hd

theorem qc_two {X Y U V : Scheme.{0}} [IsAffine Y] {f : X ⟶ Y} {u : U ⟶ X} {v : V ⟶ X}
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v) (hb : QuasiCompact (u ≫ f)) (hd : QuasiCompact (v ≫ f)) :
    QuasiCompact f := by
  have h1 : CompactSpace U := (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).1 hb
  have h2 : CompactSpace V := (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).1 hd
  refine (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).2 ⟨?_⟩
  have : (Set.univ : Set X) = Set.range u ∪ Set.range v := by
    ext x; simpa using hc x
  rw [this]
  exact (isCompact_range u.continuous).union (isCompact_range v.continuous)

theorem pb_mono {A X Y : Scheme.{0}} {a : A ⟶ X} {i : X ⟶ Y} [Mono i] {j : A ⟶ Y} (h : a ≫ i = j) :
    IsPullback a (𝟙 A) i j := by
  subst h
  exact IsPullback.of_vert_isIso_mono (by constructor; simp)

theorem pb_snd {S : Scheme.{0}} (N : Over S) {M G : Over S} (g : M ⟶ G) :
    IsPullback (N ◁ g).left (snd N M).left (snd N G).left g.left := by
  have : IsPullback (N ◁ g) (snd N M) (snd N G) g := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift (s.fst ≫ fst N G) s.snd) ?_ ?_ ?_⟩⟩
    · intro s; ext <;> simp [s.condition]
    · intro s; simp
    · intro s m h1 h2; ext
      · simp [← h1]
      · simp [← h2]
  exact this.map (Over.forget S)

theorem closed_two {S : Scheme.{0}} {X N G M₁ M₂ W₁ W₂ : Over S} (p : X ⟶ N) (q : X ⟶ G) {g₁ : M₁ ⟶ G} {g₂ : M₂ ⟶ G}
    [IsOpenImmersion g₁.left] [IsOpenImmersion g₂.left]
    (hc : ∀ x : G.left, x ∈ Set.range g₁.left ∨ x ∈ Set.range g₂.left)
    {a₁ : W₁ ⟶ X} {b₁ : W₁ ⟶ M₁} {a₂ : W₂ ⟶ X} {b₂ : W₂ ⟶ M₂}
    (h₁ : IsPullback a₁.left b₁.left q.left g₁.left) (h₂ : IsPullback a₂.left b₂.left q.left g₂.left)
    (c₁ : IsClosedImmersion (lift (a₁ ≫ p) b₁).left) (c₂ : IsClosedImmersion (lift (a₂ ≫ p) b₂).left) :
    IsClosedImmersion (lift p q).left := by
  have key : ∀ {M W : Over S} {g : M ⟶ G} {a : W ⟶ X} {b : W ⟶ M}, IsPullback a.left b.left q.left g.left →
      IsPullback a.left (lift (a ≫ p) b).left (lift p q).left (N ◁ g).left := by
    intro M W g a b h
    have e : a ≫ q = b ≫ g := Over.OverMorphism.ext h.w
    refine IsPullback.of_bot ?_ ?_ (pb_snd N g)
    · rwa [← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]
    · rw [← Over.comp_left, ← Over.comp_left]
      congr 1
      ext <;> simp [e]
  have : IsOpenImmersion (N ◁ g₁).left := MorphismProperty.of_isPullback (P := @IsOpenImmersion) (pb_snd N g₁).flip ‹_›
  have : IsOpenImmersion (N ◁ g₂).left := MorphismProperty.of_isPullback (P := @IsOpenImmersion) (pb_snd N g₂).flip ‹_›
  refine target_two @IsClosedImmersion ?_ (key h₁) (key h₂) c₁ c₂
  intro z
  rcases hc ((snd N G).left z) with ⟨y, hy⟩ | ⟨y, hy⟩
  · obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback (pb_snd N g₁) z y hy.symm
    exact Or.inl ⟨w, hw⟩
  · obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback (pb_snd N g₂) z y hy.symm
    exact Or.inr ⟨w, hw⟩

theorem closed_swap {S : Scheme.{0}} {X N G : Over S} {p : X ⟶ N} {q : X ⟶ G}
    (h : IsClosedImmersion (lift p q).left) : IsClosedImmersion (lift q p).left := by
  have : lift q p = lift p q ≫ (β_ N G).hom := by ext <;> simp
  rw [this, Over.comp_left]
  have : IsIso (β_ N G).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (β_ N G).hom))
  infer_instance

theorem sep_iff {S : Scheme.{0}} (G : Over S) : IsSeparated G.hom ↔ IsClosedImmersion (lift (𝟙 G) (𝟙 G)).left := by
  have : (lift (𝟙 G) (𝟙 G)).left = pullback.diagonal G.hom := by
    apply pullback.hom_ext <;> simp
  rw [this]
  exact ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem ext_of_schemeDominant {W X Y Z : Scheme.{0}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (d : W ⟶ X) [IsSchemeTheoreticallyDominant d] (hU : d ≫ f = d ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  haveI : IsSeparated Y'.hom := ‹IsSeparated s›
  let U' : Over Z := Over.mk (d ≫ f ≫ s)
  let d' : U' ⟶ X' := Over.homMk d
  have e : d' ≫ f' = d' ≫ g' := by
    ext1
    exact hU
  let l := equalizer.lift d' e
  have hd : d = l.left ≫ (equalizer.ι f' g').left := by
    rw [← Over.comp_left, equalizer.lift_ι]; rfl
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    apply le_bot_iff.1
    calc _ ≤ (l.left ≫ (equalizer.ι f' g').left).ker := Scheme.Hom.le_ker_comp _ _
      _ = ⊥ := by rw [← hd]; exact d.ker_eq_bot
  haveI : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.2 hker
  have h0 : IsIso ((Over.forget Z).map (equalizer.ι f' g')) := (inferInstance : IsIso (equalizer.ι f' g').left)
  have : IsIso (equalizer.ι f' g') := isIso_of_reflects_iso _ (Over.forget Z)
  have hfg : f' = g' := (cancel_epi (equalizer.ι f' g')).1 (equalizer.condition f' g')
  exact congrArg CommaMorphism.left hfg

theorem exists_sup {S : Scheme.{0}} {N W₁ W₂ : Over S} (p₁ : W₁ ⟶ N) (p₂ : W₂ ⟶ N) [IsOpenImmersion p₁.left]
    [IsOpenImmersion p₂.left] : ∃ (X : Over S) (p : X ⟶ N) (a₁ : W₁ ⟶ X) (a₂ : W₂ ⟶ X), IsOpenImmersion p.left ∧
      a₁ ≫ p = p₁ ∧ a₂ ≫ p = p₂ ∧ ∀ x, x ∈ Set.range a₁.left ∨ x ∈ Set.range a₂.left := by
  let U : N.left.Opens := p₁.left.opensRange ⊔ p₂.left.opensRange
  let X : Over S := Over.mk (U.ι ≫ N.hom)
  let p : X ⟶ N := Over.homMk U.ι rfl
  have op : IsOpenImmersion p.left := inferInstanceAs (IsOpenImmersion U.ι)
  have mk : ∀ {W : Over S} (p' : W ⟶ N) [IsOpenImmersion p'.left], p'.left.opensRange ≤ U →
      ∃ a : W ⟶ X, a ≫ p = p' := by
    intro W p' _ hle
    have hr : Set.range p'.left ⊆ Set.range U.ι := by rw [Scheme.Opens.range_ι]; exact hle
    refine ⟨Over.homMk (IsOpenImmersion.lift U.ι p'.left hr) ?_, Over.OverMorphism.ext ?_⟩
    · change _ ≫ U.ι ≫ N.hom = _
      rw [IsOpenImmersion.lift_fac_assoc, Over.w p']
    · exact IsOpenImmersion.lift_fac U.ι p'.left hr
  obtain ⟨a₁, e₁⟩ := mk p₁ le_sup_left
  obtain ⟨a₂, e₂⟩ := mk p₂ le_sup_right
  refine ⟨X, p, a₁, a₂, op, e₁, e₂, fun x => ?_⟩
  have hx : p.left x ∈ U := x.2
  rcases TopologicalSpace.Opens.mem_sup.1 hx with ⟨y, hy⟩ | ⟨y, hy⟩
  · refine Or.inl ⟨y, p.left.isOpenEmbedding.injective ?_⟩
    rw [← hy, ← e₁, Over.comp_left, Scheme.Hom.comp_apply]
  · refine Or.inr ⟨y, p.left.isOpenEmbedding.injective ?_⟩
    rw [← hy, ← e₂, Over.comp_left, Scheme.Hom.comp_apply]

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A : Over (Sp K)}

theorem j_isPullback (M : Model R A) : IsPullback M.j A.hom M.Y.hom (spMap (algebraMap R K)) := by
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  have h : M.e.inv.left ≫ pullback.snd M.Y.hom (spMap (algebraMap R K)) = A.hom ≫ 𝟙 _ := by
    rw [Category.comp_id]; exact Over.w M.e.inv
  have := (IsPullback.of_horiz_isIso ⟨h⟩).paste_horiz (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K)))
  rw [Category.id_comp] at this
  exact this

noncomputable def ofSquare (Y : Over (Sp R)) (h₁ : Smooth Y.hom) (h₂ : IsSeparated Y.hom) (h₃ : QuasiCompact Y.hom)
    {j : A.left ⟶ Y.left} (h : IsPullback j A.hom Y.hom (spMap (algebraMap R K))) : Model R A :=
  ⟨Y, Over.isoMk h.isoPullback.symm (h.isoPullback_inv_snd), h₁, h₂, h₃⟩

theorem ofSquare_j (Y : Over (Sp R)) (h₁ : Smooth Y.hom) (h₂ : IsSeparated Y.hom) (h₃ : QuasiCompact Y.hom)
    {j : A.left ⟶ Y.left} (h : IsPullback j A.hom Y.hom (spMap (algebraMap R K))) :
    (ofSquare Y h₁ h₂ h₃ h).j = j := h.isoPullback_hom_fst

variable [IsDomain R] [IsFractionRing R K]

theorem schDom_open (M : Model R A) {X : Scheme.{0}} (i : X ⟶ M.Y.left) [IsOpenImmersion i] {a : A.left ⟶ X}
    (h : a ≫ i = M.j) : IsSchemeTheoreticallyDominant a := by
  have := M.smooth
  have : IsSchemeTheoreticallyDominant (spMap (algebraMap R K)) := by
    have : IsDominant (spMap (algebraMap R K)) :=
      ⟨PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _ |>.2 (by
        exact ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)).le.trans bot_le)⟩
    exact IsSchemeTheoreticallyDominant.of_isDominant _
  have : IsSchemeTheoreticallyDominant M.j := IsSchemeTheoreticallyDominant.of_isPullback (j_isPullback M).flip
  have : QuasiCompact M.j := MorphismProperty.of_isPullback (P := @QuasiCompact) (j_isPullback M).flip inferInstance
  exact IsSchemeTheoreticallyDominant.of_isPullback (pb_mono h).flip

theorem pb_of_closed (N : Model R A) {X G M W : Over (Sp R)} (p : X ⟶ N.Y) [IsOpenImmersion p.left] (q : X ⟶ G)
    (g : M ⟶ G) [IsOpenImmersion g.left] (a : W ⟶ X) (b : W ⟶ M) (w : a.left ≫ q.left = b.left ≫ g.left)
    (hc : IsClosedImmersion (lift (a ≫ p) b).left) (j : A.left ⟶ W.left) (hj : j ≫ a.left ≫ p.left = N.j) :
    IsPullback a.left b.left q.left g.left := by
  let l : W.left ⟶ pullback q.left g.left := pullback.lift a.left b.left w
  let m : pullback q.left g.left ⟶ pullback N.Y.hom M.hom :=
    pullback.lift (pullback.fst _ _ ≫ p.left) (pullback.snd _ _) (by
      rw [Category.assoc, Over.w p, ← Over.w q, ← Over.w g, pullback.condition_assoc])
  have e : l ≫ m = (lift (a ≫ p) b).left := by
    apply pullback.hom_ext <;> simp [l, m]
  have : IsSeparated (m ≫ pullback.fst _ _) := by
    simp only [m, pullback.lift_fst]; infer_instance
  have : IsSeparated m := IsSeparated.of_comp m (pullback.fst _ _)
  have : IsClosedImmersion (l ≫ m) := e ▸ hc
  have : IsClosedImmersion l := IsClosedImmersion.of_comp l m
  have : IsSchemeTheoreticallyDominant (j ≫ l) :=
    schDom_open N (pullback.fst q.left g.left ≫ p.left) (by simp [l, ← hj])
  have : IsIso l := IsClosedImmersion.isIso_iff_ker_eq_bot.2
    (le_bot_iff.1 ((Scheme.Hom.le_ker_comp j l).trans (j ≫ l).ker_eq_bot.le))
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso l) (by simp [l]) (by simp [l])

theorem exists_union {M N : Model R A} (h : Compat M N) :
    ∃ (G : Model R A) (g₁ : M.Y ⟶ G.Y) (g₂ : N.Y ⟶ G.Y), IsOpenImmersion g₁.left ∧ IsOpenImmersion g₂.left ∧
      M.j ≫ g₁.left = G.j ∧ N.j ≫ g₂.left = G.j ∧ ∀ y, y ∈ Set.range g₁.left ∨ y ∈ Set.range g₂.left := by
  obtain ⟨W, a, b, ha, hb, ja, jb, hc⟩ := h
  let Y : Over (Sp R) := Over.mk (pushout.desc M.Y.hom N.Y.hom ((Over.w a).trans (Over.w b).symm))
  let g₁ : M.Y ⟶ Y := Over.homMk (pushout.inl a.left b.left) (pushout.inl_desc _ _ _)
  let g₂ : N.Y ⟶ Y := Over.homMk (pushout.inr a.left b.left) (pushout.inr_desc _ _ _)
  have o₁ : IsOpenImmersion g₁.left := GlobalTheory.GlueModels.isOpenImmersion_inl a.left b.left
  have o₂ : IsOpenImmersion g₂.left := GlobalTheory.GlueModels.isOpenImmersion_inr a.left b.left
  have cov : ∀ y, y ∈ Set.range g₁.left ∨ y ∈ Set.range g₂.left := GlobalTheory.GlueModels.pushout_cover a.left b.left
  have w : a.left ≫ g₁.left = b.left ≫ g₂.left := pushout.condition
  have ej : N.j ≫ g₂.left = M.j ≫ g₁.left := by rw [← ja, ← jb, Category.assoc, Category.assoc, w]
  have sm : Smooth Y.hom := source_two @Smooth cov (by rw [Over.w g₁]; exact M.smooth) (by rw [Over.w g₂]; exact N.smooth)
  have qc : QuasiCompact Y.hom := qc_two cov (by rw [Over.w g₁]; exact M.qc) (by rw [Over.w g₂]; exact N.qc)
  have oi : ∀ Z : Over (Sp R), IsOpenImmersion (𝟙 Z : Z ⟶ Z).left := fun Z => by rw [Over.id_left]; infer_instance
  have self : ∀ {Z : Over (Sp R)} (g : Z ⟶ Y) [IsOpenImmersion g.left],
      IsPullback (𝟙 Z : Z ⟶ Z).left (𝟙 Z : Z ⟶ Z).left g.left g.left := fun g _ => by
    rw [Over.id_left]; exact pb_mono (Category.id_comp _)
  have pb : IsPullback a.left b.left g₁.left g₂.left := by
    have := oi M.Y
    exact pb_of_closed M (𝟙 _) g₁ g₂ a b w (by rwa [Category.comp_id]) W.j (by simpa using ja)
  have c₁ : IsClosedImmersion (lift (𝟙 M.Y) g₁).left :=
    closed_two _ _ cov (self g₁) pb (by rw [Category.comp_id]; exact (sep_iff _).1 M.sep) (by rwa [Category.comp_id])
  have c₂ : IsClosedImmersion (lift (𝟙 N.Y) g₂).left :=
    closed_two _ _ cov pb.flip (self g₂) (by rw [Category.comp_id]; exact closed_swap hc)
      (by rw [Category.comp_id]; exact (sep_iff _).1 N.sep)
  have top : ∀ {Z : Over (Sp R)} (g : Z ⟶ Y),
      IsPullback g.left (𝟙 Z : Z ⟶ Z).left (𝟙 Y : Y ⟶ Y).left g.left := fun g => by
    rw [Over.id_left, Over.id_left]; exact pb_mono (Category.comp_id _)
  have sep : IsSeparated Y.hom := (sep_iff _).2 (closed_two _ _ cov (top g₁) (top g₂)
    (by rw [Category.comp_id]; exact closed_swap c₁) (by rw [Category.comp_id]; exact closed_swap c₂))
  have sq : IsPullback (M.j ≫ g₁.left) A.hom Y.hom (spMap (algebraMap R K)) :=
    GlobalTheory.GlueModels.isPullback_of_two cov (pb_mono rfl) (pb_mono ej)
      (by rw [Category.id_comp, Over.w g₁]; exact j_isPullback M)
      (by rw [Category.id_comp, Over.w g₂]; exact j_isPullback N)
  exact ⟨ofSquare Y sm sep qc sq, g₁, g₂, o₁, o₂, (ofSquare_j Y sm sep qc sq).symm,
    ej.trans (ofSquare_j Y sm sep qc sq).symm, cov⟩

theorem compat_of_cover {M₁ M₂ G N : Model R A} (g₁ : M₁.Y ⟶ G.Y) (g₂ : M₂.Y ⟶ G.Y) [IsOpenImmersion g₁.left]
    [IsOpenImmersion g₂.left] (j₁ : M₁.j ≫ g₁.left = G.j) (j₂ : M₂.j ≫ g₂.left = G.j)
    (cov : ∀ y, y ∈ Set.range g₁.left ∨ y ∈ Set.range g₂.left) (h₁ : Compat N M₁) (h₂ : Compat N M₂) :
    Compat N G := by
  obtain ⟨W₁, p₁, b₁, hp₁, hb₁, jp₁, jb₁, hc₁⟩ := h₁
  obtain ⟨W₂, p₂, b₂, hp₂, hb₂, jp₂, jb₂, hc₂⟩ := h₂
  obtain ⟨X, p, a₁, a₂, op, rfl, rfl, cx⟩ := exists_sup p₁ p₂
  rw [Over.comp_left] at hp₁ hp₂ jp₁ jp₂
  have o₁ : IsOpenImmersion a₁.left := IsOpenImmersion.of_comp _ p.left
  have o₂ : IsOpenImmersion a₂.left := IsOpenImmersion.of_comp _ p.left
  have ej : W₂.j ≫ a₂.left = W₁.j ≫ a₁.left := by
    rw [← cancel_mono p.left, Category.assoc, Category.assoc, jp₁, jp₂]
  have := G.sep
  have hab : pullback.fst a₁.left a₂.left ≫ b₁.left ≫ g₁.left = pullback.snd a₁.left a₂.left ≫ b₂.left ≫ g₂.left := by
    have : IsSchemeTheoreticallyDominant (pullback.lift W₁.j W₂.j ej.symm) :=
      schDom_open W₁ (pullback.fst a₁.left a₂.left) (pullback.lift_fst _ _ _)
    refine ext_of_schemeDominant G.Y.hom ?_ (pullback.lift W₁.j W₂.j ej.symm) ?_
    · simp only [Category.assoc, Over.w]
      rw [← Over.w a₁, ← Over.w a₂, pullback.condition_assoc]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, reassoc_of% jb₁, reassoc_of% jb₂, j₁, j₂]
  obtain ⟨φ, f₁, f₂⟩ := GlobalTheory.GlueModels.exists_glue (IsPullback.of_hasPullback a₁.left a₂.left) cx _ _ hab
  have hφ : φ ≫ G.Y.hom = X.hom := by
    refine (coverTwo a₁.left a₂.left cx).hom_ext _ _ ?_
    rintro (_ | _)
    · change a₁.left ≫ φ ≫ _ = a₁.left ≫ _
      rw [reassoc_of% f₁]; simp only [Over.w]
    · change a₂.left ≫ φ ≫ _ = a₂.left ≫ _
      rw [reassoc_of% f₂]; simp only [Over.w]
  let q : X ⟶ G.Y := Over.homMk φ hφ
  have pb₁ : IsPullback a₁.left b₁.left q.left g₁.left := pb_of_closed N p q g₁ a₁ b₁ f₁ hc₁ W₁.j jp₁
  have pb₂ : IsPullback a₂.left b₂.left q.left g₂.left := pb_of_closed N p q g₂ a₂ b₂ f₂ hc₂ W₂.j jp₂
  have := N.smooth
  have := N.sep
  have sm : Smooth X.hom := by rw [← Over.w p]; infer_instance
  have sep : IsSeparated X.hom := by rw [← Over.w p]; infer_instance
  have qc : QuasiCompact X.hom := qc_two cx (by rw [Over.w a₁]; exact W₁.qc) (by rw [Over.w a₂]; exact W₂.qc)
  have sq : IsPullback (W₁.j ≫ a₁.left) A.hom X.hom (spMap (algebraMap R K)) := by
    have := (pb_mono (a := W₁.j ≫ a₁.left) (i := p.left) (j := N.j) (by rw [Category.assoc, jp₁])).paste_vert
      (j_isPullback N)
    rwa [Category.id_comp, Over.w p] at this
  refine ⟨ofSquare X sm sep qc sq, p, q, op, target_two @IsOpenImmersion cov pb₁ pb₂ hb₁ hb₂, ?_, ?_,
    closed_two p q cov pb₁ pb₂ hc₁ hc₂⟩
  · rw [ofSquare_j, Category.assoc, jp₁]
  · rw [ofSquare_j, Category.assoc]
    change W₁.j ≫ a₁.left ≫ φ = _
    rw [f₁, reassoc_of% jb₁, j₁]

theorem glue_compat : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) (n : ℕ) (M : Fin (n + 1) → Model R A), (∀ i j, Compat (M i) (M j)) → ∃ G : Model R A, (∀ i, (M i).Le G) ∧ (∀ y : G.Y.left, ∃ (i : Fin (n + 1)) (g : (M i).Y ⟶ G.Y), IsOpenImmersion g.left ∧ (M i).j ≫ g.left = G.j ∧ y ∈ Set.range g.left) ∧ ∀ N : Model R A, (∀ i, Compat N (M i)) → Compat N G := by
  intro R K _ _ _ _ _ _ A n
  induction n with
  | zero =>
    intro M _
    refine ⟨M 0, fun i => ?_, fun y => ⟨0, 𝟙 _, ?_, by simp, by simp⟩, fun N h => h 0⟩
    · obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) _ _
      exact Model.le_refl _
    · rw [Over.id_left]; infer_instance
  | succ n ih =>
    intro M hM
    obtain ⟨G₀, le₀, cov₀, comp₀⟩ := ih (fun i => M i.succ) (fun i j => hM _ _)
    obtain ⟨G, g₁, g₂, o₁, o₂, j₁, j₂, cov⟩ := exists_union (comp₀ (M 0) (fun i => hM _ _))
    refine ⟨G, fun i => ?_, fun y => ?_, fun N hN => compat_of_cover g₁ g₂ j₁ j₂ cov (hN 0) (comp₀ N fun i => hN _)⟩
    · refine Fin.cases ⟨g₁, o₁, j₁⟩ (fun i => (le₀ i).trans ⟨g₂, o₂, j₂⟩) i
    · rcases cov y with hy | ⟨x, rfl⟩
      · exact ⟨0, g₁, o₁, j₁, hy⟩
      · obtain ⟨i, g, og, jg, z, rfl⟩ := cov₀ x
        refine ⟨i.succ, g ≫ g₂, ?_, ?_, z, ?_⟩
        · rw [Over.comp_left]; infer_instance
        · rw [Over.comp_left, reassoc_of% jg, j₂]
        · rw [Over.comp_left, Scheme.Hom.comp_apply]

end GlobalTheory.SS.GlueCompat
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_finitely_many_compatible_smoothModels : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) (n : ℕ) (M : Fin (n + 1) → Model R A), (∀ i j, Compat (M i) (M j)) → ∃ G : Model R A, (∀ i, (M i).Le G) ∧ (∀ y : G.Y.left, ∃ (i : Fin (n + 1)) (g : (M i).Y ⟶ G.Y), IsOpenImmersion g.left ∧ (M i).j ≫ g.left = G.j ∧ y ∈ Set.range g.left) ∧ ∀ N : Model R A, (∀ i, Compat N (M i)) → Compat N G := by
  atlas_forward_decl GlobalTheory.SS.GlueCompat.glue_compat
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GlobalTheory.SS.LawDef
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' : Over (Sp K)}

theorem j_comm (M : Model R A) (N : Model R A') (f : A ⟶ A') (g : M.Y ⟶ N.Y)
    (h : M.e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map g = f ≫ N.e.inv) : M.j ≫ g.left = f.left ≫ N.j := by
  have h2 := congrArg (fun q => q.left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))) h
  have h4 : ((Over.pullback (spMap (algebraMap R K))).map g).left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))
      = pullback.fst M.Y.hom (spMap (algebraMap R K)) ≫ g.left := pullback.lift_fst _ _ _
  simp only [Over.comp_left, Category.assoc] at h2
  unfold Model.j
  rw [Category.assoc]
  exact (congrArg (fun q => M.e.inv.left ≫ q) h4).symm.trans h2

theorem prod_j_fst (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (fst M.Y N.Y).left = (fst A A').left ≫ M.j := by
  exact j_comm (M.prod N) M (fst A A') (fst M.Y N.Y) (by simp [Model.prod])

theorem prod_j_snd (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (snd M.Y N.Y).left = (snd A A').left ≫ N.j := by
  exact j_comm (M.prod N) N (snd A A') (snd M.Y N.Y) (by simp [Model.prod])

theorem prod_ext (M : Model R A) (N : Model R A') {T : Scheme.{0}} {u v : T ⟶ (M.prod N).Y.left}
    (h1 : u ≫ (fst M.Y N.Y).left = v ≫ (fst M.Y N.Y).left)
    (h2 : u ≫ (snd M.Y N.Y).left = v ≫ (snd M.Y N.Y).left) : u = v :=
  pullback.hom_ext h1 h2

theorem ext_test {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {U : M.Y.left.Opens} {g : U.toScheme ⟶ N.Y.left}
    (h : Extends M N f U g) {T : Scheme.{0}} (t : T ⟶ A.left) (u : T ⟶ U.toScheme) (e : u ≫ U.ι = t ≫ M.j) :
    u ≫ g = t ≫ f.left ≫ N.j := by
  have hp := isPullback_morphismRestrict M.j U
  have e2 := hp.lift_fst u t e
  have e1 := hp.lift_snd u t e
  calc u ≫ g = hp.lift u t e ≫ (M.j ∣_ U) ≫ g := by rw [← Category.assoc, e2]
    _ = _ := by rw [h.2, ← Category.assoc, e1]

theorem defAt_mk (M : Model R A) (N : Model R A') (f : A ⟶ A') {V : Scheme.{0}} (i : V ⟶ M.Y.left)
    [IsOpenImmersion i] (g : V ⟶ N.Y.left) (h1 : g ≫ N.Y.hom = i ≫ M.Y.hom)
    (h2 : ∀ (T : Scheme.{0}) (t : T ⟶ A.left) (u : T ⟶ V), u ≫ i = t ≫ M.j → u ≫ g = t ≫ f.left ≫ N.j) (y : V) :
    DefAt M N f (i y) := by
  refine ⟨i.opensRange, i.isoOpensRange.inv ≫ g, ⟨y, rfl⟩, ?_, ?_⟩
  · rw [Category.assoc, h1, Scheme.Hom.isoOpensRange_inv_comp_assoc]
  · rw [← Category.assoc]
    apply h2
    rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]

theorem defAt_global (M : Model R A) (N : Model R A') (f : A ⟶ A') (g : M.Y ⟶ N.Y)
    (h : M.j ≫ g.left = f.left ≫ N.j) : Extends M N f ⊤ ((⊤ : M.Y.left.Opens).ι ≫ g.left) :=
  ⟨by simp, by rw [morphismRestrict_ι_assoc, h]⟩

theorem defAt_comp {M : Model R A} {N : Model R A'} {P : Model R A''} {f : A ⟶ A'} {f' : A' ⟶ A''}
    {U : M.Y.left.Opens} {g : U.toScheme ⟶ N.Y.left} (h : Extends M N f U g) (y : U.toScheme)
    (h' : DefAt N P f' (g y)) : DefAt M P (f ≫ f') (U.ι y) := by
  obtain ⟨V, g', hy, h'⟩ := h'
  refine defAt_mk M P (f ≫ f') ((g ⁻¹ᵁ V).ι ≫ U.ι) ((g ∣_ V) ≫ g') ?_ ?_ ⟨y, hy⟩
  · rw [Category.assoc, h'.1, morphismRestrict_ι_assoc, h.1, Category.assoc]
  · intro T t u e
    have e1 := ext_test h t (u ≫ (g ⁻¹ᵁ V).ι) (by rw [Category.assoc, e])
    have e2 := ext_test h' (t ≫ f.left) (u ≫ (g ∣_ V)) (by
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, e1, Category.assoc])
    rw [← Category.assoc, e2, Over.comp_left, Category.assoc, Category.assoc]

theorem defAt_comp_all {M : Model R A} {N : Model R A'} {P : Model R A''} {f : A ⟶ A'} {f' : A' ⟶ A''}
    {y : M.Y.left} (h : DefAt M N f y) (h' : ∀ w, DefAt N P f' w) : DefAt M P (f ≫ f') y := by
  obtain ⟨U, g, hy, h⟩ := h
  exact defAt_comp h ⟨y, hy⟩ (h' _)

theorem defAt_lift {M : Model R A} {N : Model R A'} {P : Model R A''} {f : A ⟶ A'} {f' : A ⟶ A''}
    {y : M.Y.left} (h : DefAt M N f y) (h' : DefAt M P f' y) : DefAt M (N.prod P) (lift f f') y := by
  obtain ⟨U, g, hy, h⟩ := h
  obtain ⟨V, g', hy', h'⟩ := h'
  let i₁ := M.Y.left.homOfLE (inf_le_left : U ⊓ V ≤ U)
  let i₂ := M.Y.left.homOfLE (inf_le_right : U ⊓ V ≤ V)
  have e₁ : i₁ ≫ U.ι = (U ⊓ V).ι := Scheme.homOfLE_ι _ _
  have e₂ : i₂ ≫ V.ι = (U ⊓ V).ι := Scheme.homOfLE_ι _ _
  have w : (i₁ ≫ g) ≫ N.Y.hom = (i₂ ≫ g') ≫ P.Y.hom := by
    rw [Category.assoc, Category.assoc, h.1, h'.1, reassoc_of% e₁, reassoc_of% e₂]
  let G : (U ⊓ V).toScheme ⟶ (N.prod P).Y.left := pullback.lift _ _ w
  have G1 : G ≫ (fst N.Y P.Y).left = i₁ ≫ g := pullback.lift_fst _ _ _
  have G2 : G ≫ (snd N.Y P.Y).left = i₂ ≫ g' := pullback.lift_snd _ _ _
  refine defAt_mk M (N.prod P) _ (U ⊓ V).ι G ?_ ?_ ⟨y, hy, hy'⟩
  · have : (N.prod P).Y.hom = (fst N.Y P.Y).left ≫ N.Y.hom := (Over.w (fst N.Y P.Y)).symm
    rw [this, reassoc_of% G1, h.1, reassoc_of% e₁]
  · intro T t u e
    apply prod_ext
    · have := ext_test h t (u ≫ i₁) (by rw [Category.assoc, e₁, e])
      simp only [Category.assoc] at this ⊢
      rw [G1, this, prod_j_fst, ← Over.comp_left_assoc, lift_fst]
    · have := ext_test h' t (u ≫ i₂) (by rw [Category.assoc, e₂, e])
      simp only [Category.assoc] at this ⊢
      rw [G2, this, prod_j_snd, ← Over.comp_left_assoc, lift_snd]

theorem defAt_twist {M : Model R A} {N : Model R A'} {f : A ⟶ A''} (t : A' ≅ A'') {y : M.Y.left}
    (h : DefAt M N (f ≫ t.inv) y) : DefAt M (N.twist t) f y := by
  obtain ⟨U, g, hy, h1, h2⟩ := h
  refine ⟨U, g, hy, h1, h2.trans ?_⟩
  simp [Model.j, Model.twist]

theorem defAt_generic [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    (M : Model R A) (N : Model R A') (f : A ⟶ A') (y : M.Y.left) (hy : y ∉ M.sp) : DefAt M N f y := by
  have := isOpenImmersion_spMap_of_isDiscreteValuationRing R K
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  have : IsOpenImmersion M.j := by unfold Model.j; infer_instance
  obtain ⟨x, rfl⟩ : y ∈ Set.range M.j := by
    have h1 : y ∈ Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K))) := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨(⊥ : PrimeSpectrum K), ?_⟩
      have hp : PrimeSpectrum.asIdeal (R := R) (M.Y.hom y) = ⊥ := by
        by_contra h
        exact hy (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ((M.Y.hom y).isPrime.isMaximal h)))
      apply PrimeSpectrum.ext
      rw [hp]
      exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)
    obtain ⟨w, rfl⟩ := h1
    obtain ⟨x, rfl⟩ := M.e.inv.left.surjective w
    exact ⟨x, rfl⟩
  refine defAt_mk M N f M.j (f.left ≫ N.j) ?_ ?_ x
  · rw [Category.assoc, N.j_hom, M.j_hom, Over.w_assoc]
  · intro T t u e
    rw [(cancel_mono _).1 e]

theorem isOpen_isoAt (M : Model R A) (N : Model R A') (f : A ⟶ A') : IsOpen {y | IsoAt M N f y} := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨U, g, hy, h⟩
  exact ⟨U, fun w hw => ⟨U, g, hw, h⟩, U.isOpen, hy⟩

def Sec (M : Model R A) (p : 𝟙_ (Over (Sp K)) ⟶ A) (s : 𝟙_ (Over (Sp R)) ⟶ M.Y) : Prop :=
  p.left ≫ M.j = spMap (algebraMap R K) ≫ s.left

theorem sec_lift {M : Model R A} {N : Model R A'} {p : 𝟙_ (Over (Sp K)) ⟶ A} {q : 𝟙_ (Over (Sp K)) ⟶ A'}
    {s : 𝟙_ (Over (Sp R)) ⟶ M.Y} {t : 𝟙_ (Over (Sp R)) ⟶ N.Y} (h : Sec M p s) (h' : Sec N q t) :
    Sec (M.prod N) (lift p q) (lift s t) := by
  apply prod_ext
  · rw [Category.assoc, Category.assoc, prod_j_fst, ← Over.comp_left_assoc, lift_fst, ← Over.comp_left, lift_fst]
    exact h
  · rw [Category.assoc, Category.assoc, prod_j_snd, ← Over.comp_left_assoc, lift_snd, ← Over.comp_left, lift_snd]
    exact h'

theorem sec_unique [IsDomain R] [IsFractionRing R K] {M : Model R A} {p : 𝟙_ (Over (Sp K)) ⟶ A}
    {s t : 𝟙_ (Over (Sp R)) ⟶ M.Y} (h : Sec M p s) (h' : Sec M p t) : s = t := by
  have := M.sep
  have := isDominant_spMap_of_isFractionRing R K
  have : IsReduced (𝟙_ (Over (Sp R))).left := inferInstanceAs (IsReduced (Sp R))
  ext1
  exact ext_of_isDominant_of_isSeparated M.Y.hom ((Over.w s).trans (Over.w t).symm) (spMap (algebraMap R K))
    (h.symm.trans h')

variable [IsLocalRing R]

def sp0 {Y : Over (Sp R)} (s : 𝟙_ (Over (Sp R)) ⟶ Y) : Y.left := s.left (IsLocalRing.closedPoint R)

theorem map_modelSectionSpecialPoint_comp {Y Z : Over (Sp R)} (s : 𝟙_ (Over (Sp R)) ⟶ Y) (g : Y ⟶ Z) : g.left (sp0 s) = sp0 (s ≫ g) := by
  unfold sp0
  rw [Over.comp_left, Scheme.Hom.comp_apply]

theorem modelSectionSpecialPoint_mem_specialFibre (M : Model R A) (s : 𝟙_ (Over (Sp R)) ⟶ M.Y) : sp0 s ∈ M.sp := by
  show M.Y.hom (s.left _) = _
  rw [← Scheme.Hom.comp_apply, Over.w s]
  rfl

theorem sec_exists {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {U : M.Y.left.Opens} {g : U.toScheme ⟶ N.Y.left}
    (h : Extends M N f U g) {p : 𝟙_ (Over (Sp K)) ⟶ A} {s : 𝟙_ (Over (Sp R)) ⟶ M.Y} (hs : Sec M p s)
    (y : U.toScheme) (hy : U.ι y = sp0 s) : ∃ t, Sec N (p ≫ f) t ∧ g y = sp0 t := by
  have hr : Set.range s.left ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    refine range_subset_opens_of_isLocalRing (B := CommRingCat.of R) s.left ?_
    show sp0 s ∈ U
    rw [← hy]; exact y.2
  let s' := IsOpenImmersion.lift U.ι s.left hr
  have e : s' ≫ U.ι = s.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk (s' ≫ g) (by rw [Category.assoc, h.1, reassoc_of% e, Over.w s]), ?_, ?_⟩
  · have := ext_test h p.left (spMap (algebraMap R K) ≫ s') (by rw [Category.assoc, e]; exact hs.symm)
    show (p ≫ f).left ≫ N.j = spMap (algebraMap R K) ≫ s' ≫ g
    rw [← Category.assoc (spMap _), this, Over.comp_left, Category.assoc]
  · have : y = s' (IsLocalRing.closedPoint R) := by
      apply U.ι.isOpenEmbedding.injective
      rw [hy, ← Scheme.Hom.comp_apply, e]; rfl
    rw [this, ← Scheme.Hom.comp_apply]; rfl

theorem defAt_comp_sec [IsDomain R] [IsFractionRing R K] {M : Model R A} {N : Model R A'} {P : Model R A''}
    {f : A ⟶ A'} {f' : A' ⟶ A''} {p : 𝟙_ (Over (Sp K)) ⟶ A} {s : 𝟙_ (Over (Sp R)) ⟶ M.Y}
    {t : 𝟙_ (Over (Sp R)) ⟶ N.Y} (hs : Sec M p s) (ht : Sec N (p ≫ f) t) (h : DefAt M N f (sp0 s))
    (h' : DefAt N P f' (sp0 t)) : DefAt M P (f ≫ f') (sp0 s) := by
  obtain ⟨U, g, hy, h⟩ := h
  obtain ⟨t', ht', e⟩ := sec_exists h hs ⟨_, hy⟩ rfl
  rw [sec_unique ht ht', ← e] at h'
  exact defAt_comp h _ h'

theorem exists_section [IsDomain R] (hR : SH R K) (M : Model R A) {C : Set M.Y.left} (hC : IsLocallyClosed C)
    (hne : (C ∩ M.sp).Nonempty) : ∃ s : 𝟙_ (Over (Sp R)) ⟶ M.Y, sp0 s ∈ C := by
  obtain ⟨-, hH, hk, -⟩ := hR
  have := M.smooth
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let i := pullback.fst M.Y.hom r
  let q := pullback.snd M.Y.hom r
  have := LocallyOfFiniteType.jacobsonSpace q
  obtain ⟨y, hy, hy'⟩ := hne
  obtain ⟨w, rfl⟩ : y ∈ Set.range i := by
    rw [range_fst_residue]; exact hy'
  obtain ⟨c, hc, hc'⟩ := nonempty_inter_closedPoints (Z := i ⁻¹' C) ⟨w, hy⟩ (hC.preimage i.continuous)
  obtain ⟨⟨x, hx⟩, hx'⟩ := reducePoint_residue_surjective M.Y.hom R (𝟙 _)
    ⟨pointOfClosedPoint q c hc' ≫ i, by
      rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc, Category.comp_id]⟩
  have e : r ≫ x = pointOfClosedPoint q c hc' ≫ i := congrArg Subtype.val hx'
  refine ⟨Over.homMk x hx, ?_⟩
  have e' := congrArg (fun m => m (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) e
  simp only [Scheme.Hom.comp_apply, pointOfClosedPoint_apply] at e'
  have e2 : r (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) = IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
  rw [e2] at e'
  show x _ ∈ C
  exact e' ▸ hc

omit [IsLocalRing R] in
theorem isPullback_fibre_fst {Y Z : Over (Sp R)} (s : 𝟙_ (Over (Sp R)) ⟶ Y) :
    IsPullback (lift (toUnit Z ≫ s) (𝟙 Z)) (toUnit Z) (fst Y Z) s := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => c.fst ≫ snd Y Z) ?_ ?_ ?_⟩⟩
  · intro c
    ext1
    · have := c.condition
      simp [this, ← Category.assoc, toUnit_unique (_ ≫ toUnit Z) c.snd]
    · simp
  · intro c; exact toUnit_unique _ _
  · intro c m h _
    simp [← h]

omit [IsLocalRing R] in
theorem isPullback_fibre_snd {Y Z : Over (Sp R)} (s : 𝟙_ (Over (Sp R)) ⟶ Y) :
    IsPullback (lift (𝟙 Z) (toUnit Z ≫ s)) (toUnit Z) (snd Z Y) s := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => c.fst ≫ fst Z Y) ?_ ?_ ?_⟩⟩
  · intro c
    ext1
    · simp
    · have := c.condition
      simp [this, ← Category.assoc, toUnit_unique (_ ≫ toUnit Z) c.snd]
  · intro c; exact toUnit_unique _ _
  · intro c m h _
    simp [← h]

theorem exists_fibre {M : Model R A} {W Y : Over (Sp R)} {l : M.Y ⟶ W} {p : W ⟶ Y} {s : 𝟙_ (Over (Sp R)) ⟶ Y}
    (h : IsPullback l (toUnit _) p s) (z : W.left) (hz : p.left z = sp0 s) : ∃ u ∈ M.sp, l.left u = z := by
  obtain ⟨u, h1, h2⟩ := Scheme.exists_preimage_of_isPullback (h.map (Over.forget _)) z (IsLocalRing.closedPoint R) hz
  refine ⟨u, ?_, h1⟩
  have e := Over.w (toUnit M.Y)
  show M.Y.hom u = _
  rw [← e, Scheme.Hom.comp_apply]
  exact h2

theorem exists_section_general [IsDomain R] (hR : SH R K) {M : Model R A} (hi : M.Irr) {f : A ⟶ A}
    (hf : GenIso M M f) {V₁ V₂ : Set M.Y.left} (o₁ : IsOpen V₁) (o₂ : IsOpen V₂) (n₁ : (M.sp ∩ V₁).Nonempty)
    (n₂ : (M.sp ∩ V₂).Nonempty) :
    ∃ (s : 𝟙_ (Over (Sp R)) ⟶ M.Y), sp0 s ∈ V₁ ∧ ∀ p, Sec M p s → ∃ t, Sec M (p ≫ f) t ∧ sp0 t ∈ V₂ := by
  obtain ⟨w, hw, U, g, hwU, hg, ho⟩ := hf
  have key : ∀ u : U.toScheme, g u ∈ M.sp ↔ U.ι u ∈ M.sp := by
    intro u
    show M.Y.hom (g u) = _ ↔ M.Y.hom (U.ι u) = _
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hg.1]
  obtain ⟨_, h1, ⟨u, rfl⟩, h2⟩ := hi.2 (Set.range g) V₂ g.isOpenEmbedding.isOpen_range o₂
    ⟨g ⟨w, hwU⟩, (key _).2 hw, _, rfl⟩ n₂
  have o₃ : IsOpen (U.ι '' (g ⁻¹' V₂)) := U.ι.isOpenEmbedding.isOpenMap _ (o₂.preimage g.continuous)
  obtain ⟨v, h3, h4⟩ := hi.2 V₁ _ o₁ o₃ n₁ ⟨U.ι u, (key _).1 h1, u, h2, rfl⟩
  obtain ⟨s, hs, u', hu', e⟩ := exists_section hR M (o₁.inter o₃).isLocallyClosed ⟨v, h4, h3⟩
  refine ⟨s, hs, fun p hp => ?_⟩
  obtain ⟨t, ht, e'⟩ := sec_exists hg hp u' e
  exact ⟨t, ht, e' ▸ hu'⟩

theorem lawdef_section [IsDomain R] (hR : SH R K) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) (M : Model R A) (hM : Strict M) (X Y : 𝟙_ (Over (Sp R)) ⟶ M.Y) :
    ∃ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom ∧
      DefAt (M.prod M) (M.twist (transl a)) (μ[A]) (sp0 (lift X Y)) := by
  have := hR.2.2.2
  obtain ⟨x, hx, -, -⟩ := GlobalTheory.SS.SectionTranslation.translation_by_section R K hR A hA M hM X
  obtain ⟨y, hy, gy, -⟩ := GlobalTheory.SS.SectionTranslation.translation_by_section R K hR A hA M hM Y
  have gφ := (GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus R K hR).2.1 A A A M M M _ _ hM.1.1 hM.1.2.2 gy
  obtain ⟨z₁, hz₁, i₁⟩ := (hM.2 false _ (modelSectionSpecialPoint_mem_specialFibre M Y)).2
  obtain ⟨z₂, hz₂, i₂⟩ := (hM.2 true _ (modelSectionSpecialPoint_mem_specialFibre M X)).1
  obtain ⟨u₁, m₁, rfl⟩ := exists_fibre (isPullback_fibre_snd (Z := M.Y) Y) z₁ hz₁
  obtain ⟨u₂, m₂, rfl⟩ := exists_fibre (isPullback_fibre_fst (Z := M.Y) X) z₂ hz₂
  obtain ⟨s, hs, hs'⟩ := exists_section_general hR hM.1.1 gφ
    ((isOpen_isoAt (M.prod M) (M.prod M) (shear A false)).preimage (lift (𝟙 M.Y) (toUnit M.Y ≫ Y)).left.continuous)
    ((isOpen_isoAt (M.prod M) (M.prod M) (shear A true)).preimage (lift (toUnit M.Y ≫ X) (𝟙 M.Y)).left.continuous)
    ⟨u₁, m₁, i₁⟩ ⟨u₂, m₂, i₂⟩
  obtain ⟨a, ha, ga, ha'⟩ := GlobalTheory.SS.SectionTranslation.translation_by_section R K hR A hA M hM s
  obtain ⟨t, ht, ht'⟩ := hs' a ha
  have u1 : ∀ (w : 𝟙_ (Over (Sp R)) ⟶ M.Y), w ≫ toUnit M.Y = 𝟙 _ := fun w => toUnit_unique _ _
  have u2 : ∀ (w : 𝟙_ (Over (Sp K)) ⟶ A), w ≫ toUnit A = 𝟙 _ := fun w => toUnit_unique _ _
  have d1 : DefAt M M (transl a).inv (sp0 Y) := by
    refine (ha' (sp0 Y) false ?_).defAt
    have e : s ≫ lift (𝟙 M.Y) (toUnit M.Y ≫ Y) = Y ≫ lift (toUnit M.Y ≫ s) (𝟙 M.Y) := by
      ext1 <;> simp [reassoc_of% u1]
    rw [map_modelSectionSpecialPoint_comp, ← e, ← map_modelSectionSpecialPoint_comp]
    exact hs
  have d2 : DefAt (M.prod M) (M.prod M) (shear A true) (sp0 (lift X t)) := by
    have e : t ≫ lift (toUnit M.Y ≫ X) (𝟙 M.Y) = lift X t := by
      ext1 <;> simp [reassoc_of% u1]
    rw [← e, ← map_modelSectionSpecialPoint_comp]
    exact IsoAt.defAt ht'
  have ef := defAt_global (M.prod M) M _ _ (prod_j_fst M M)
  have es := defAt_global (M.prod M) M _ _ (prod_j_snd M M)
  have d3 : DefAt (M.prod M) M (snd A A ≫ (transl a).inv) (sp0 (lift X Y)) := by
    refine defAt_comp es ⟨sp0 (lift X Y), trivial⟩ ?_
    have : ((⊤ : (M.prod M).Y.left.Opens).ι ≫ (snd M.Y M.Y).left) ⟨sp0 (lift X Y), trivial⟩ = sp0 Y := by
      rw [Scheme.Hom.comp_apply]
      exact (map_modelSectionSpecialPoint_comp (lift X Y) (snd M.Y M.Y)).trans (by rw [lift_snd])
    rw [this]; exact d1
  have d4 := defAt_lift (⟨⊤, _, trivial, ef⟩ : DefAt (M.prod M) M (fst A A) (sp0 (lift X Y))) d3
  have e5 : lift x y ≫ lift (fst A A) (snd A A ≫ (transl a).inv) = lift x (a ≫ ι[A] ≫ (transl y).hom) := by
    ext1
    · simp
    · have : a ≫ ι[A] = a⁻¹ := rfl
      simp only [Category.assoc, lift_snd, lift_snd_assoc, ← Category.assoc a, this]
      simp only [transl, MonObj.comp_mul, GrpObj.comp_inv, reassoc_of% u2, Category.comp_id]
      exact _root_.mul_comm _ _
  have d5 := defAt_comp_sec (sec_lift hx hy) (by rw [e5]; exact sec_lift hx ht) d4 d2
  have d6 := defAt_comp_all d5 (fun w => (⟨⊤, _, trivial, es⟩ : DefAt (M.prod M) M (snd A A) w))
  refine ⟨a, ga, defAt_twist _ ?_⟩
  convert d6 using 1
  have hμ : μ[A] = fst A A * snd A A := by
    rw [Hom.mul_def]; simp
  have u3 : ∀ (w : A ⊗ A ⟶ A), w ≫ toUnit A = toUnit _ := fun w => toUnit_unique _ _
  simp only [shear, transl, Category.assoc, lift_snd, MonObj.comp_mul, GrpObj.comp_inv, lift_fst, reassoc_of% u3,
    Category.comp_id]
  rw [hμ, _root_.mul_left_comm]

end GlobalTheory.SS.LawDef

open GlobalTheory.SS.LawDef in

theorem GlobalTheory.SS.defAt_mul_twist : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∀ z : (M.prod M).Y.left, ∃ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom ∧ DefAt (M.prod M) (M.twist (transl a)) (μ[A]) z := by
  intro R K _ _ _ _ _ hR A _ _ hA M hM z
  by_cases hz : z ∈ (M.prod M).sp
  · obtain ⟨Z, hZ⟩ := exists_section hR (M.prod M) (C := closure {z}) isClosed_closure.isLocallyClosed
      ⟨z, subset_closure rfl, hz⟩
    obtain ⟨a, ga, U, g, hU, h⟩ := lawdef_section hR A hA M hM (Z ≫ fst M.Y M.Y) (Z ≫ snd M.Y M.Y)
    have e : lift (Z ≫ fst M.Y M.Y) (Z ≫ snd M.Y M.Y) = Z := by
      rw [← comp_lift, lift_fst_snd]; exact Category.comp_id _
    rw [e] at hU
    exact ⟨a, ga, U, g, (specializes_iff_mem_closure.2 hZ).mem_open U.isOpen hU, h⟩
  · have := hR.1
    have := hR.2.2.2
    obtain ⟨y, hy⟩ := hM.1.1.nonempty
    have e : (transl (1 : 𝟙_ (Over (Sp K)) ⟶ A)).hom = 𝟙 A := by simp [transl]
    exact ⟨1, ⟨y, hy, e ▸ isoAt_id M y⟩, defAt_generic _ _ _ z hz⟩
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelGroupLaw_definedAt_translate : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∀ z : (M.prod M).Y.left, ∃ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom ∧ DefAt (M.prod M) (M.twist (transl a)) (μ[A]) z := by
  atlas_forward_decl GlobalTheory.SS.defAt_mul_twist
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_model_extension_of_definedAtPoints : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A A' : Over (Sp K)) (M : Model R A) (N : Model R A') (f : A ⟶ A'), (∀ y, DefAt M N f y) → ∃! g : M.Y ⟶ N.Y, M.j ≫ g.left = f.left ≫ N.j := by
  first | exact @GlobalTheory.SS.existsUnique_extension_of_forall_defAt | exact GlobalTheory.SS.existsUnique_extension_of_forall_defAt | (intros; apply GlobalTheory.SS.existsUnique_extension_of_forall_defAt <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.FinUnion
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}

theorem mem_of_closed {S : Scheme.{0}} {W N G U : Over S} (g : W ⟶ N) (h : W ⟶ G) [IsClosedImmersion (lift g h).left]
    (q : U ⟶ N) (φ : U ⟶ G) {T : Scheme.{0}} (t : T ⟶ U.left) (ht : DenseRange t) (r : T ⟶ W.left)
    (h1 : t ≫ q.left = r ≫ g.left) (h2 : t ≫ φ.left = r ≫ h.left) (z : U.left) :
    ∃ w, g.left w = q.left z ∧ h.left w = φ.left z := by
  have e : t ≫ (lift q φ).left = r ≫ (lift g h).left := by
    apply pullback.hom_ext
    · change (t ≫ (lift q φ).left) ≫ (fst N G).left = (r ≫ (lift g h).left) ≫ (fst N G).left
      rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, h1]
    · change (t ≫ (lift q φ).left) ≫ (snd N G).left = (r ≫ (lift g h).left) ≫ (snd N G).left
      rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, h2]
  have hc : IsClosed ((lift q φ).left ⁻¹' Set.range (lift g h).left) :=
    (lift g h).left.isClosedEmbedding.isClosed_range.preimage (lift q φ).left.continuous
  have hs : Set.range t ⊆ (lift q φ).left ⁻¹' Set.range (lift g h).left := by
    rintro _ ⟨x, rfl⟩
    exact ⟨r x, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, e]⟩
  obtain ⟨w, hw⟩ := hc.closure_subset_iff.2 hs (ht z)
  refine ⟨w, ?_, ?_⟩
  · have := congrArg (fst N G).left hw
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst] at this
  · have := congrArg (snd N G).left hw
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd] at this

theorem range_j (M : Model R A) : Set.range M.j = M.Y.hom ⁻¹' Set.range (spMap (algebraMap R K)) := by
  rw [← Scheme.Pullback.range_fst, Model.j, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have : Function.Surjective M.e.inv.left := ((Over.forget _).mapIso M.e).inv.surjective
  rw [this.range_eq, Set.image_univ]

theorem dense_j [IsDomain R] [IsFractionRing R K] (M : Model R A) : DenseRange M.j := by
  have := M.smooth
  have hd : DenseRange (spMap (algebraMap R K)) :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R K)).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)]; exact bot_le)
  unfold DenseRange
  rw [range_j]
  exact hd.preimage M.Y.hom.isOpenMap

theorem dense_res [IsDomain R] [IsFractionRing R K] (M : Model R A) (U : M.Y.left.Opens) : DenseRange (M.j ∣_ U) := by
  have h := (dense_j M).preimage U.ι.isOpenEmbedding.isOpenMap
  refine h.mono ?_
  rintro x ⟨a, ha⟩
  refine ⟨⟨a, show M.j a ∈ U from ha ▸ x.2⟩, Subtype.ext ?_⟩
  exact (morphismRestrict_base_coe M.j U _).trans ha

theorem mem_range_j [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] (M : Model R A) (y : M.Y.left)
    (hy : y ∉ M.sp) : y ∈ Set.range M.j := by
  rw [range_j]
  refine ⟨(⊥ : PrimeSpectrum K), ?_⟩
  have h1 : (M.Y.hom y).asIdeal = ⊥ := by
    by_contra hne
    exact hy (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ((M.Y.hom y).isPrime.isMaximal hne)))
  apply PrimeSpectrum.ext
  rw [h1]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)

theorem ext_apply {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {U : M.Y.left.Opens} {g : U.toScheme ⟶ N.Y.left}
    (h : Extends M N f U g) {T : Scheme.{0}} (t : T ⟶ U.toScheme) (w : T ⟶ A.left) (e : t ≫ U.ι = w ≫ M.j) :
    t ≫ g = w ≫ f.left ≫ N.j := by
  have hp := isPullback_morphismRestrict M.j U
  have a := hp.lift_fst t w e
  have b := hp.lift_snd t w e
  rw [← a, Category.assoc, h.2, ← Category.assoc, b]

theorem prod_j_fst (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (fst M.Y N.Y).left = (fst A A').left ≫ M.j := by
  have h : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (fst M.Y N.Y) = fst A A' ≫ M.e.inv := by
    simp [Model.prod]
  have h2 := congrArg (fun x => x.left ≫ pullback.fst M.Y.hom (spMap (algebraMap R K))) h
  simp only [Over.comp_left, Category.assoc, Over.pullback_map_left] at h2
  erw [pullback.lift_fst] at h2
  exact (Category.assoc _ _ _).trans h2

theorem prod_j_snd (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (snd M.Y N.Y).left = (snd A A').left ≫ N.j := by
  have h : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (snd M.Y N.Y) = snd A A' ≫ N.e.inv := by
    simp [Model.prod]
  have h2 := congrArg (fun x => x.left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))) h
  simp only [Over.comp_left, Category.assoc, Over.pullback_map_left] at h2
  erw [pullback.lift_fst] at h2
  exact (Category.assoc _ _ _).trans h2

theorem twist_j (M : Model R A) (f : A ≅ A') : f.hom.left ≫ (M.twist f).j = M.j := by
  simp only [Model.j, Model.twist, Iso.trans_inv, Over.comp_left, Category.assoc]
  rw [← Category.assoc, ← Over.comp_left, Iso.hom_inv_id]; simp

theorem exists_move {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) (O : (pullback f g).Opens) (z₀ : ↥(pullback f g))
    (h₀ : z₀ ∈ O) (V : X.Opens) (hirr : IsPreirreducible (f ⁻¹' {g (pullback.snd f g z₀)}))
    (x : X) (hx : x ∈ V) (hx' : f x = g (pullback.snd f g z₀)) :
    ∃ z ∈ O, pullback.snd f g z = pullback.snd f g z₀ ∧ pullback.fst f g z ∈ V := by
  set y := pullback.snd f g z₀ with hy
  have H0 : IsPullback ((pullback.snd f g).fiberι y) ((pullback.snd f g).fiberToSpecResidueField y)
      (pullback.snd f g) (Y.fromSpecResidueField y) := IsPullback.of_hasPullback _ _
  have H1 := H0.paste_horiz (IsPullback.of_hasPullback f g)
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] at H1
  have H2 : IsPullback (f.fiberι (g y)) (f.fiberToSpecResidueField (g y)) f (S.fromSpecResidueField (g y)) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨p, hp1, hp2⟩ := H2.exists_lift ((pullback.snd f g).fiberι y ≫ pullback.fst f g)
    ((pullback.snd f g).fiberToSpecResidueField y ≫ Spec.map (g.residueFieldMap y)) (by
      rw [H1.w, Category.assoc])
  rw [← hp1] at H1
  have H3 := H1.of_right hp2 H2
  have ho : UniversallyOpen p := MorphismProperty.of_isPullback H3.flip inferInstance
  have hp : ∀ w, f.fiberι (g y) (p w) = pullback.fst f g ((pullback.snd f g).fiberι y w) := fun w => by
    rw [← Scheme.Hom.comp_apply, hp1, Scheme.Hom.comp_apply]
  obtain ⟨w₀, hw₀⟩ : z₀ ∈ Set.range ((pullback.snd f g).fiberι y) := by
    rw [Scheme.Hom.range_fiberι]; rfl
  obtain ⟨x₀, hx₀⟩ : x ∈ Set.range (f.fiberι (g y)) := by
    rw [Scheme.Hom.range_fiberι]; exact hx'
  have hI : IsPreirreducible (Set.univ : Set (f.fiber (g y))) := by
    have := Subtype.preirreducibleSpace hirr
    have h := (PreirreducibleSpace.isPreirreducible_univ (X := f ⁻¹' {g y})).image _
      (f.fiberHomeo (g y)).symm.continuous.continuousOn
    rwa [Set.image_univ, (f.fiberHomeo (g y)).symm.surjective.range_eq] at h
  obtain ⟨_, -, ⟨w, hw, rfl⟩, hV⟩ := hI _ _
    (p.isOpenMap _ (O.isOpen.preimage ((pullback.snd f g).fiberι y).continuous))
    (V.isOpen.preimage (f.fiberι (g y)).continuous) ⟨p w₀, trivial, w₀, by simpa [hw₀] using h₀, rfl⟩
    ⟨x₀, trivial, by simpa [hx₀] using hx⟩
  refine ⟨_, hw, ((pullback.snd f g).range_fiberι y).le ⟨w, rfl⟩, ?_⟩
  rw [← hp]; exact hV

theorem irr_union {X I : Type} [TopologicalSpace X] (S : Set X) (U : I → Set X) (i₀ : I) (hU : ∀ i, IsOpen (U i))
    (hI : ∀ i, IsPreirreducible (S ∩ U i)) (hc : ∀ x ∈ S, ∃ i, x ∈ U i) (hm : ∀ i, (S ∩ U i ∩ U i₀).Nonempty) :
    IsIrreducible S := by
  refine ⟨(hm i₀).mono fun x hx => hx.1.1, ?_⟩
  have hs : S ⊆ closure (S ∩ U i₀) := fun x hx => by
    obtain ⟨i, hi⟩ := hc x hx
    exact closure_mono (show S ∩ U i ∩ U i₀ ⊆ S ∩ U i₀ from fun y hy => ⟨hy.1.1, hy.2⟩)
      (subset_closure_inter_of_isPreirreducible_of_isOpen (hI i) (hU i₀) (hm i) ⟨hx, hi⟩)
  have e : closure S = closure (S ∩ U i₀) :=
    subset_antisymm (closure_minimal hs isClosed_closure) (closure_mono Set.inter_subset_left)
  rw [← isPreirreducible_iff_closure, e]
  exact (hI i₀).closure

theorem defAt_of_le {P : Model R A'} {N G : Model R A} {f : A' ⟶ A} {z : P.Y.left} (h : DefAt P N f z) (hl : N.Le G) :
    DefAt P G f z := by
  obtain ⟨U, φ, hz, h1, h2⟩ := h
  obtain ⟨g, -, hg⟩ := hl
  refine ⟨U, φ ≫ g.left, hz, ?_, ?_⟩
  · rw [Category.assoc, Over.w g, h1]
  · rw [← Category.assoc, h2, ← hg]; simp only [Category.assoc]

section
variable [GrpObj A] [IsCommMonObj A]

theorem transl_one : (transl (1 : 𝟙_ (Over (Sp K)) ⟶ A)).hom = 𝟙 A := by
  simp [transl]

theorem law_split (a : 𝟙_ (Over (Sp K)) ⟶ A) :
    lift (fst A A ≫ (transl a).hom) (shear A false ≫ snd A A) ≫ μ[A] = snd A A ≫ (transl a).hom := by
  change (fst A A ≫ (transl a).hom) * (shear A false ≫ snd A A) = _
  simp only [transl, shear, lift_snd, MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    toUnit_unique (fst A A ≫ toUnit A) (toUnit _), toUnit_unique (snd A A ≫ toUnit A) (toUnit _)]
  group

set_option backward.isDefEq.respectTransparency false in

theorem le_of_law [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] {M G : Model R A} (hM : Strict M)
    (m : M.Y ⊗ M.Y ⟶ G.Y) (hm : (M.prod M).j ≫ m.left = (μ[A]).left ≫ G.j) (a : 𝟙_ (Over (Sp K)) ⟶ A)
    (ha : GenIso M M (transl a).hom) (hc : Compat (M.twist (transl a)) G) : (M.twist (transl a)).Le G := by
  obtain ⟨W, g, h, hg, hh, eg, eh, hcl⟩ := hc
  have hsurj : Function.Surjective g.left := by
    intro y
    by_cases hy : y ∈ M.sp
    swap
    · obtain ⟨x, rfl⟩ := mem_range_j (M.twist (transl a)) y hy
      exact ⟨W.j x, by rw [← Scheme.Hom.comp_apply, eg]⟩
    obtain ⟨z₀, hz₀, O, σ, hO, hσ, -⟩ := (hM.2 false y hy).2
    obtain ⟨x, hx, V, τ, hV, hτ, -⟩ := ha
    have hy' : M.Y.hom (pullback.snd M.Y.hom M.Y.hom z₀) = IsLocalRing.closedPoint R := by
      have : M.Y.hom ((snd M.Y M.Y).left z₀) = IsLocalRing.closedPoint R := by rw [hz₀]; exact hy
      exact this
    obtain ⟨z, hzO, hz, hzV⟩ := exists_move M.Y.hom M.Y.hom O z₀ hO V
      (by rw [hy']; exact hM.1.1.2) x hV (by rw [hy']; exact hx)
    let Ω : (M.prod M).Y.left.Opens := O ⊓ (fst M.Y M.Y).left ⁻¹ᵁ V
    let U : Over (Sp R) := Over.mk (Ω.ι ≫ (M.Y ⊗ M.Y).hom)
    let i : U ⟶ M.Y ⊗ M.Y := Over.homMk Ω.ι rfl
    let a₁ : Ω.toScheme ⟶ V.toScheme := (fst M.Y M.Y).left.resLE V Ω inf_le_right
    have e₁ : a₁ ≫ V.ι = Ω.ι ≫ (fst M.Y M.Y).left := Scheme.Hom.resLE_comp_ι _ _
    let a₂ : Ω.toScheme ⟶ O.toScheme := Scheme.homOfLE _ inf_le_left
    have e₂ : a₂ ≫ O.ι = Ω.ι := Scheme.homOfLE_ι _ _
    let φ₁ : U ⟶ M.Y := Over.homMk (a₁ ≫ τ) (by
      change (a₁ ≫ τ) ≫ M.Y.hom = Ω.ι ≫ (M.Y ⊗ M.Y).hom
      rw [Category.assoc, hτ.1, ← Category.assoc, e₁, Category.assoc, Over.w])
    let φ₂ : U ⟶ M.Y ⊗ M.Y := Over.homMk (a₂ ≫ σ) (by
      change (a₂ ≫ σ) ≫ (M.prod M).Y.hom = Ω.ι ≫ (M.prod M).Y.hom
      rw [Category.assoc, hσ.1, ← Category.assoc, e₂])
    let t := (M.prod M).j ∣_ Ω
    let w := ((M.prod M).j ⁻¹ᵁ Ω).ι
    have et : t ≫ Ω.ι = w ≫ (M.prod M).j := morphismRestrict_ι _ _
    have c₁ : (t ≫ a₁) ≫ τ = (w ≫ (fst A A).left) ≫ (transl a).hom.left ≫ M.j :=
      ext_apply hτ _ _ (by
        rw [Category.assoc, e₁, ← Category.assoc, et, Category.assoc, Category.assoc]
        exact congrArg (w ≫ ·) (prod_j_fst M M))
    have c₂ : (t ≫ a₂) ≫ σ = w ≫ (shear A false).left ≫ (M.prod M).j :=
      ext_apply hσ _ _ (by rw [Category.assoc, e₂, et])
    have c₃ : t ≫ (lift φ₁ (φ₂ ≫ snd M.Y M.Y)).left =
        w ≫ (lift (fst A A ≫ (transl a).hom) (shear A false ≫ snd A A)).left ≫ (M.prod M).j := by
      apply pullback.hom_ext
      · change (t ≫ _) ≫ (fst M.Y M.Y).left = (w ≫ _) ≫ (fst M.Y M.Y).left
        rw [Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, Category.assoc]
        erw [prod_j_fst M M]
        rw [← Over.comp_left_assoc, lift_fst]
        simp only [Category.assoc, Over.comp_left] at c₁ ⊢
        exact c₁
      · change (t ≫ _) ≫ (snd M.Y M.Y).left = (w ≫ _) ≫ (snd M.Y M.Y).left
        rw [Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, Category.assoc]
        erw [prod_j_snd M M]
        rw [← Over.comp_left_assoc, lift_snd]
        have := congrArg (· ≫ (snd M.Y M.Y).left) c₂
        simp only [Category.assoc] at this
        erw [prod_j_snd M M] at this
        simp only [Category.assoc, Over.comp_left]
        exact this
    obtain ⟨v, hv, -⟩ := mem_of_closed g h (i ≫ snd M.Y M.Y) (lift φ₁ (φ₂ ≫ snd M.Y M.Y) ≫ m) t
      (dense_res (M.prod M) Ω) (w ≫ (snd A A).left ≫ (transl a).hom.left ≫ W.j)
      (by
        simp only [Category.assoc]
        rw [eg, twist_j, ← prod_j_snd M M, ← Category.assoc, ← et, Category.assoc]
        rfl)
      (by
        simp only [Category.assoc]
        rw [eh, Over.comp_left, ← Category.assoc, c₃]
        simp only [Category.assoc]
        erw [hm]
        rw [← Over.comp_left_assoc, law_split, Over.comp_left_assoc])
      ⟨z, hzO, hzV⟩
    exact ⟨v, hv.trans (hz.trans hz₀)⟩
  have : Surjective g.left := ⟨hsurj⟩
  have : IsIso g.left := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨hg, this⟩
  have : IsIso ((Over.forget _).map g) := this
  have : IsIso g := isIso_of_reflects_iso g (Over.forget _)
  have e : g.left ≫ (inv g ≫ h).left = h.left := by rw [← Over.comp_left, IsIso.hom_inv_id_assoc]
  refine ⟨inv g ≫ h, ?_, ?_⟩
  · rw [← IsIso.eq_inv_comp] at e
    rw [e]; infer_instance
  · rw [← eg, Category.assoc, e, eh]
end

theorem sp_inter {M G : Model R A} [IsLocalRing R] (g : M.Y ⟶ G.Y) : G.sp ∩ Set.range g.left = g.left '' M.sp := by
  have e : ∀ x, G.Y.hom (g.left x) = M.Y.hom x := fun x => by rw [← Scheme.Hom.comp_apply, Over.w]
  ext y
  constructor
  · rintro ⟨hy, x, rfl⟩
    exact ⟨x, (e x).symm.trans hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(e x).trans hx, x, rfl⟩

set_option backward.isDefEq.respectTransparency false in

theorem meet [IsDomain R] [IsLocalRing R] [IsFractionRing R K] {M G : Model R A} (f : A ≅ A) (hf : GenIso M M f.hom)
    (g : (M.twist f).Y ⟶ G.Y) (hg : (M.twist f).j ≫ g.left = G.j) (g₀ : M.Y ⟶ G.Y) (hg₀ : M.j ≫ g₀.left = G.j) :
    (G.sp ∩ Set.range g.left ∩ Set.range g₀.left).Nonempty := by
  obtain ⟨x, hx, V, τ, hV, hτ, -⟩ := hf
  have := G.sep
  have : IsClosedImmersion (lift (𝟙 G.Y) (𝟙 G.Y)).left := by
    have : (lift (𝟙 G.Y) (𝟙 G.Y)).left = pullback.diagonal G.Y.hom := by
      apply pullback.hom_ext
      · change (lift (𝟙 G.Y) (𝟙 G.Y) ≫ fst _ _).left = _
        simp
      · change (lift (𝟙 G.Y) (𝟙 G.Y) ≫ snd _ _).left = _
        simp
    rw [this]; infer_instance
  let U : Over (Sp R) := Over.mk (V.ι ≫ M.Y.hom)
  let i : U ⟶ (M.twist f).Y := Over.homMk V.ι rfl
  let φ : U ⟶ M.Y := Over.homMk τ hτ.1
  obtain ⟨v, h1, h2⟩ := mem_of_closed (𝟙 G.Y) (𝟙 G.Y) (i ≫ g) (φ ≫ g₀) (M.j ∣_ V) (dense_res M V)
    ((M.j ⁻¹ᵁ V).ι ≫ f.hom.left ≫ G.j)
    (by
      change M.j ∣_ V ≫ V.ι ≫ g.left = _ ≫ 𝟙 _
      rw [Category.comp_id, ← Category.assoc, morphismRestrict_ι, ← hg, ← Category.assoc f.hom.left, twist_j,
        Category.assoc])
    (by
      change M.j ∣_ V ≫ τ ≫ g₀.left = _ ≫ 𝟙 _
      rw [Category.comp_id, ← Category.assoc, hτ.2, ← hg₀]
      simp only [Category.assoc]) ⟨x, hV⟩
  refine ⟨g.left x, ?_, τ ⟨x, hV⟩, h2.symm.trans h1⟩
  rw [sp_inter]
  exact ⟨x, hx, rfl⟩

end GlobalTheory.SS.FinUnion

namespace GlobalTheory.SS
open FinUnion

theorem exists_union_translates : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∃ G : Model R A, G.Irr ∧ (∀ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom → (M.twist (transl a)).Le G) ∧ (∀ y : G.Y.left, ∃ (a : (𝟙_ (Over (Sp K)) ⟶ A)) (g : M.Y ⟶ G.Y), GenIso M M (transl a).hom ∧ IsOpenImmersion g.left ∧ (M.twist (transl a)).j ≫ g.left = G.j ∧ y ∈ Set.range g.left) ∧ ∀ z, DefAt (M.prod M) G (μ[A]) z := by
  intro R K _ _ _ _ _ hS A _ _ hA M hM
  obtain ⟨_, -, -, _⟩ := id hS
  choose a ha U φ hU hφ using GlobalTheory.T.modelGroupLaw_definedAt_translate R K hS A hA M hM
  have := (M.prod M).qc
  have : CompactSpace (M.prod M).Y.left := QuasiCompact.compactSpace_of_compactSpace (M.prod M).Y.hom
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun z => (U z : Set (M.prod M).Y.left))
    (fun z => (U z).isOpen) (fun z _ => Set.mem_iUnion.2 ⟨z, hU z⟩)
  let b : Fin (T.card + 1) → (𝟙_ (Over (Sp K)) ⟶ A) := Fin.cons 1 fun i => a (T.equivFin.symm i)
  have hb : ∀ i, GenIso M M (transl (b i)).hom := by
    intro i
    refine Fin.cases ?_ (fun i => ha _) i
    change GenIso M M (transl 1).hom
    rw [transl_one]
    obtain ⟨y, hy⟩ := hM.1.1.1
    exact ⟨y, hy, isoAt_id M y⟩
  obtain ⟨G, hle, hcov, hcomp⟩ := GlobalTheory.T.exists_glue_finitely_many_compatible_smoothModels R K A T.card (fun i => M.twist (transl (b i)))
    fun i j => GlobalTheory.T.strictModel_translates_twist_compatible R K hS A hA M hM _ _ (hb i) (hb j)
  have hdef : ∀ z, DefAt (M.prod M) G (μ[A]) z := by
    intro z
    obtain ⟨z', hz', hz⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ z))
    refine defAt_of_le ?_ (hle (T.equivFin ⟨z', hz'⟩).succ)
    have : b (T.equivFin ⟨z', hz'⟩).succ = a z' := by simp [b]
    rw [this]
    exact ⟨U z', φ z', hz, hφ z'⟩
  obtain ⟨m, hm, -⟩ := GlobalTheory.T.existsUnique_model_extension_of_definedAtPoints R K _ _ _ _ _ hdef
  refine ⟨G, ?_, fun c hc => le_of_law hM m hm c hc (hcomp _ fun i => GlobalTheory.T.strictModel_translates_twist_compatible R K hS A hA M hM _ _ hc (hb i)),
    fun y => ?_, hdef⟩
  · obtain ⟨g₀, o₀, e₀⟩ := hle 0
    have e₁ : M.j ≫ g₀.left = G.j := by
      have := twist_j M (transl (1 : 𝟙_ (Over (Sp K)) ⟶ A))
      rw [transl_one, Over.id_left, Category.id_comp] at this
      rw [← this]; exact e₀
    refine irr_union (I := {p : Σ i, ((M.twist (transl (b i))).Y ⟶ G.Y) //
      IsOpenImmersion p.2.left ∧ (M.twist (transl (b p.1))).j ≫ p.2.left = G.j}) G.sp
      (fun p => Set.range p.1.2.left) ⟨⟨0, g₀⟩, o₀, e₀⟩ (fun p => ?_) (fun p => ?_) (fun y _ => ?_)
      (fun p => meet _ (hb p.1.1) p.1.2 p.2.2 g₀ e₁)
    · have := p.2.1
      exact p.1.2.left.isOpenEmbedding.isOpen_range
    · rw [sp_inter]
      exact hM.1.1.2.image _ p.1.2.left.continuous.continuousOn
    · obtain ⟨i, g, h1, h2, h3⟩ := hcov y
      exact ⟨⟨⟨i, g⟩, h1, h2⟩, h3⟩
  · obtain ⟨i, g, h1, h2, h3⟩ := hcov y
    exact ⟨b i, g, hb i, h1, h2, h3⟩

end GlobalTheory.SS
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_union_translates' : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∃ G : Model R A, G.Irr ∧ (∀ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom → (M.twist (transl a)).Le G) ∧ (∀ y : G.Y.left, ∃ (a : (𝟙_ (Over (Sp K)) ⟶ A)) (g : M.Y ⟶ G.Y), GenIso M M (transl a).hom ∧ IsOpenImmersion g.left ∧ (M.twist (transl a)).j ≫ g.left = G.j ∧ y ∈ Set.range g.left) ∧ ∀ z, DefAt (M.prod M) G (μ[A]) z := by
  atlas_forward_decl GlobalTheory.SS.exists_union_translates
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GlobalTheory.SS.StrictGrp

section Basic
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' : Over (Sp K)}

theorem isPullback_j (M : Model R A) : IsPullback M.j A.hom M.Y.hom (spMap (algebraMap R K)) := by
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  have h : IsPullback M.e.inv.left A.hom (pullback.snd M.Y.hom (spMap (algebraMap R K))) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨(Over.w M.e.inv).trans (Category.comp_id _).symm⟩
  simpa [Model.j] using h.paste_horiz (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K)))

theorem j_comm (M : Model R A) (N : Model R A') (f : A ⟶ A') (g : M.Y ⟶ N.Y)
    (h : M.e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map g = f ≫ N.e.inv) : M.j ≫ g.left = f.left ≫ N.j := by
  have h2 := congrArg (fun q => q.left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))) h
  have h4 : ((Over.pullback (spMap (algebraMap R K))).map g).left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))
      = pullback.fst M.Y.hom (spMap (algebraMap R K)) ≫ g.left := pullback.lift_fst _ _ _
  simp only [Over.comp_left, Category.assoc] at h2
  unfold Model.j
  rw [Category.assoc]
  exact (congrArg (fun q => M.e.inv.left ≫ q) h4).symm.trans h2

theorem prod_j_fst (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (fst M.Y N.Y).left = (fst A A').left ≫ M.j :=
  j_comm (M.prod N) M (fst A A') (fst M.Y N.Y) (by simp [Model.prod])

theorem prod_j_snd (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (snd M.Y N.Y).left = (snd A A').left ≫ N.j :=
  j_comm (M.prod N) N (snd A A') (snd M.Y N.Y) (by simp [Model.prod])

theorem twist_j (M : Model R A) (f : A ≅ A') : (M.twist f).j = f.inv.left ≫ M.j := by
  simp [Model.twist, Model.j]

theorem twist_comm {M : Model R A} {N : Model R A'} {f : A ≅ A'} {g : M.Y.left ⟶ N.Y.left}
    (h : (M.twist f).j ≫ g = N.j) : M.j ≫ g = f.hom.left ≫ N.j := by
  rw [← h, twist_j, Category.assoc, ← Category.assoc f.hom.left, ← Over.comp_left, f.hom_inv_id, Over.id_left,
    Category.id_comp]

theorem prod_comm {B B' : Over (Sp K)} {M : Model R A} {N : Model R A'} {P : Model R B} {Q : Model R B'}
    {f : A ⟶ B} {f' : A' ⟶ B'} {g : M.Y ⟶ P.Y} {g' : N.Y ⟶ Q.Y} (h : M.j ≫ g.left = f.left ≫ P.j)
    (h' : N.j ≫ g'.left = f'.left ≫ Q.j) :
    (M.prod N).j ≫ (g ⊗ₘ g').left = (f ⊗ₘ f').left ≫ (P.prod Q).j := by
  apply Over.tensorObj_ext
  · change (_ ≫ _) ≫ (fst P.Y Q.Y).left = (_ ≫ _) ≫ (fst P.Y Q.Y).left
    rw [Category.assoc, Category.assoc, prod_j_fst, ← Over.comp_left, tensorHom_fst, Over.comp_left,
      ← Category.assoc, prod_j_fst, Category.assoc, h, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, tensorHom_fst]
  · change (_ ≫ _) ≫ (snd P.Y Q.Y).left = (_ ≫ _) ≫ (snd P.Y Q.Y).left
    rw [Category.assoc, Category.assoc, prod_j_snd, ← Over.comp_left, tensorHom_snd, Over.comp_left,
      ← Category.assoc, prod_j_snd, Category.assoc, h', ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, tensorHom_snd]

theorem defAt_of_chart {G : Model R A} {N : Model R A'} {φ : A ⟶ A'} {W V : Scheme.{0}} (w : W ⟶ G.Y.left)
    [IsOpenImmersion w] {v : V ⟶ W} {u : V ⟶ A.left} (hp : IsPullback v u w G.j) (h : W ⟶ N.Y.left)
    (h₁ : h ≫ N.Y.hom = w ≫ G.Y.hom) (h₂ : v ≫ h = u ≫ φ.left ≫ N.j) {y : G.Y.left} (hy : y ∈ Set.range w) :
    DefAt G N φ y := by
  refine ⟨w.opensRange, w.isoOpensRange.inv ≫ h, hy, ?_, ?_⟩
  · rw [Category.assoc, h₁, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  · have e : (G.j ∣_ w.opensRange ≫ w.isoOpensRange.inv) ≫ w = (G.j ⁻¹ᵁ w.opensRange).ι ≫ G.j := by
      rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
    rw [← Category.assoc, ← hp.lift_fst _ _ e, Category.assoc, h₂, ← Category.assoc, hp.lift_snd]

theorem isPullback_of_comm {M : Model R A} {G : Model R A'} {f : A ≅ A'} {g : M.Y ⟶ G.Y}
    (h : M.j ≫ g.left = f.hom.left ≫ G.j) : IsPullback M.j f.hom.left g.left G.j := by
  have h₁ := isPullback_j M
  rw [← Over.w f.hom, ← Over.w g] at h₁
  exact IsPullback.of_bot h₁ h (isPullback_j G)

theorem defAt_transport {M : Model R A} {G : Model R A'} {N N' : Model R A''} {f : A ≅ A'} {g : M.Y ⟶ G.Y}
    [IsOpenImmersion g.left] (h : M.j ≫ g.left = f.hom.left ≫ G.j) {ψ : A ⟶ A''} {φ : A' ⟶ A''} {t : A'' ⟶ A''}
    {T : N.Y ⟶ N'.Y} (hT : N.j ≫ T.left = t.left ≫ N'.j) (e : ψ ≫ t = f.hom ≫ φ) {x : M.Y.left}
    (hx : DefAt M N ψ x) : DefAt G N' φ (g.left x) := by
  obtain ⟨U, k, hU, h₁, h₂⟩ := hx
  refine defAt_of_chart (U.ι ≫ g.left) (v := M.j ∣_ U) (u := (M.j ⁻¹ᵁ U).ι ≫ f.hom.left)
    ((isPullback_morphismRestrict M.j U).paste_vert (isPullback_of_comm h)) (k ≫ T.left) ?_ ?_ ⟨⟨x, hU⟩, rfl⟩
  · rw [Category.assoc, Over.w T, h₁, Category.assoc, Over.w g]
  · rw [← Category.assoc, h₂, Category.assoc, Category.assoc, hT, ← Category.assoc ψ.left, ← Over.comp_left, e]
    simp

theorem isOpen_defAt (M : Model R A) (N : Model R A') (f : A ⟶ A') : IsOpen {x | DefAt M N f x} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨U, g, hx, h⟩
  exact ⟨U, fun y hy => ⟨U, g, hy, h⟩, U.isOpen, hx⟩

variable [IsDomain R]

theorem mem_range_generic [IsDiscreteValuationRing R] [IsFractionRing R K] (p : Sp R)
    (hp : p ≠ IsLocalRing.closedPoint R) : p ∈ Set.range (spMap (algebraMap R K)) := by
  refine ⟨(⊥ : PrimeSpectrum K), PrimeSpectrum.ext ?_⟩
  have h : p.asIdeal = ⊥ := by
    by_contra h
    exact hp (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (p.isPrime.isMaximal h)))
  rw [h]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)

theorem defAt_generic [IsDiscreteValuationRing R] [IsFractionRing R K] (M : Model R A) (N : Model R A') (f : A ⟶ A')
    {x : M.Y.left} (hx : x ∉ M.sp) : DefAt M N f x := by
  have := isOpenImmersion_spMap_of_isDiscreteValuationRing R K
  have : IsOpenImmersion M.j := MorphismProperty.of_isPullback (isPullback_j M).flip this
  refine defAt_of_chart M.j (v := 𝟙 _) (u := 𝟙 _) (IsKernelPair.id_of_mono _) (f.left ≫ N.j) ?_ (by simp) ?_
  · rw [Category.assoc, N.j_hom, M.j_hom, ← Category.assoc, Over.w f]
  · obtain ⟨q, hq⟩ := mem_range_generic (K := K) (M.Y.hom x) hx
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (isPullback_j M) x q hq.symm
    exact ⟨z, hz⟩

theorem ext_section [IsFractionRing R K] {Y : Over (Sp R)} [IsSeparated Y.hom] {f g : 𝟙_ (Over (Sp R)) ⟶ Y}
    (h : spMap (algebraMap R K) ≫ f.left = spMap (algebraMap R K) ≫ g.left) : f = g := by
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing R K
  exact Over.OverMorphism.ext (ExtUnique.hom_ext_of_dominant Y.hom (by rw [Over.w, Over.w]) _ h)

end Basic

section Transl
variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A]

theorem comp_transl {T : Over (Sp K)} (x : T ⟶ A) (a : 𝟙_ (Over (Sp K)) ⟶ A) :
    x ≫ (transl a).hom = (toUnit T ≫ a) * x := by
  simp [transl, MonObj.comp_mul, ← Category.assoc, toUnit_unique (x ≫ toUnit A) (toUnit T)]

theorem transl_hom (a : 𝟙_ (Over (Sp K)) ⟶ A) : (transl a).hom = (toUnit A ≫ a) * 𝟙 A := rfl

theorem transl_mul (a b : 𝟙_ (Over (Sp K)) ⟶ A) : (transl a).hom ≫ (transl b).hom = (transl (a * b)).hom := by
  rw [comp_transl, transl_hom, transl_hom, MonObj.comp_mul, ← _root_.mul_assoc, _root_.mul_comm (toUnit A ≫ b)]

theorem transl_one : (transl (1 : 𝟙_ (Over (Sp K)) ⟶ A)).hom = 𝟙 A := by
  rw [transl_hom, MonObj.comp_one, _root_.one_mul]

theorem transl_inv (a : 𝟙_ (Over (Sp K)) ⟶ A) : (transl a).inv = (transl a⁻¹).hom := by
  rw [transl_hom, GrpObj.comp_inv]; rfl

theorem pt_transl (a b : 𝟙_ (Over (Sp K)) ⟶ A) : a ≫ (transl b).hom = b * a := by
  rw [comp_transl, toUnit_unit, Category.id_comp]

theorem mul_transl (a b : 𝟙_ (Over (Sp K)) ⟶ A) :
    μ[A] ≫ (transl (a * b)).hom = (tensorIso (transl a) (transl b)).hom ≫ μ[A] := by
  have h : (tensorIso (transl a) (transl b)).hom = lift (fst A A ≫ (transl a).hom) (snd A A ≫ (transl b).hom) := by
    ext <;> simp
  have h' : μ[A] = fst A A * snd A A := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  rw [h, ← Hom.mul_def, comp_transl, comp_transl, comp_transl, h', MonObj.comp_mul, _root_.mul_mul_mul_comm]

theorem inv_transl (a : 𝟙_ (Over (Sp K)) ⟶ A) : ι[A] ≫ (transl a⁻¹).hom = (transl a).hom ≫ ι[A] := by
  have h' : ι[A] = (𝟙 A)⁻¹ := by rw [Hom.inv_def, Category.id_comp]
  rw [← Hom.inv_def, comp_transl, transl_hom, h', GrpObj.comp_inv, mul_inv]

end Transl

section Special
variable {R K : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K] {A : Over (Sp K)}

theorem exists_section (h : SH R K) (M : Model R A) {S : Set M.Y.left} (hS : IsLocallyClosed S)
    (hne : (S ∩ M.sp).Nonempty) : ∃ s : 𝟙_ (Over (Sp R)) ⟶ M.Y, s.left (IsLocalRing.closedPoint R) ∈ S := by
  obtain ⟨-, hH, hk, -⟩ := h
  have := M.smooth
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  obtain ⟨x, hxS, hx⟩ := hne
  obtain ⟨z, rfl⟩ := (range_fst_residue M.Y.hom).ge hx
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd M.Y.hom r)
  obtain ⟨c, hcS, hc⟩ := nonempty_inter_closedPoints (Z := pullback.fst M.Y.hom r ⁻¹' S) ⟨z, hxS⟩
    (hS.preimage (pullback.fst M.Y.hom r).continuous)
  obtain ⟨⟨s, hs⟩, e⟩ := reducePoint_residue_surjective M.Y.hom R (𝟙 _)
    ⟨pointOfClosedPoint (pullback.snd M.Y.hom r) c hc ≫ pullback.fst M.Y.hom r, by
      rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc, Category.comp_id]⟩
  refine ⟨Over.homMk s hs, ?_⟩
  have e₁ : r ≫ s = pointOfClosedPoint (pullback.snd M.Y.hom r) c hc ≫ pullback.fst M.Y.hom r := congrArg Subtype.val e
  have e₂ : s (r (IsLocalRing.closedPoint _)) = pullback.fst M.Y.hom r c := by
    rw [← Scheme.Hom.comp_apply, e₁, Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
  have e₃ : r (IsLocalRing.closedPoint _) = IsLocalRing.closedPoint R := IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
  rw [e₃] at e₂
  change s _ ∈ S
  rw [e₂]; exact hcS

theorem connectedSpace_of_factor {X S S' P Z : Scheme.{0}} {f : X ⟶ S} {i : S' ⟶ S} {p : P ⟶ X} {q : P ⟶ S'}
    (hP : IsPullback p q f i) [hq : GeometricallyConnected q] {L : Type} [Field L] (y : Sp L ⟶ S') {a : Z ⟶ X}
    {b : Z ⟶ Sp L} (hZ : IsPullback a b f (y ≫ i)) : ConnectedSpace Z :=
  hq.geometrically_connectedSpace y _ _
    (IsPullback.of_right (by rw [hP.lift_fst]; exact hZ) (hP.lift_snd _ _ (by simpa using hZ.w)) hP)

theorem geometricallyConnected (h : SH R K) (M : Model R A) (hM : M.Irr) [GeometricallyConnected A.hom] :
    GeometricallyConnected M.Y.hom := by
  obtain ⟨hD, -, hk, hF⟩ := h
  have := M.smooth
  refine ⟨fun L _ y Z a b hZ => ?_⟩
  by_cases hy : y (IsLocalRing.closedPoint L) = IsLocalRing.closedPoint R
  · let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    have hr : IsClosedImmersion r := .spec_of_surjective _ IsLocalRing.residue_surjective
    have : IrreducibleSpace ↥(pullback M.Y.hom r) := by
      have he := (pullback.fst M.Y.hom r).isClosedEmbedding.isEmbedding
      have h₁ : IsIrreducible (Set.range (pullback.fst M.Y.hom r)) := by
        rw [range_fst_residue]; exact hM
      have := Subtype.irreducibleSpace h₁
      exact he.toHomeomorph.irreducibleSpace_iff.2 this
    have h₂ := geometricallyIrreducible_of_isAlgClosed (pullback.snd M.Y.hom r)
    have : GeometricallyConnected (pullback.snd M.Y.hom r) := ⟨fun L _ y Z a b hZ => by
      have : IrreducibleSpace Z := h₂.geometrically_irreducibleSpace y a b hZ
      infer_instance⟩
    obtain ⟨φ, rfl⟩ := Spec.map_surjective y
    have hl : IsLocalHom φ.hom := (IsLocalRing.isLocalHom_iff_comap_closedPoint _).2 hy
    have e : Spec.map φ = spMap (IsLocalRing.ResidueField.lift φ.hom) ≫ r := by
      rw [← Spec.map_comp]; congr 1
    rw [e] at hZ
    exact connectedSpace_of_factor (IsPullback.of_hasPullback _ _) _ hZ
  · have := isOpenImmersion_spMap_of_isDiscreteValuationRing R K
    have hr : Set.range y ⊆ Set.range (spMap (algebraMap R K)) := by
      rintro _ ⟨q, rfl⟩
      rw [Subsingleton.elim q (IsLocalRing.closedPoint L)]
      exact mem_range_generic _ hy
    rw [← IsOpenImmersion.lift_fac _ _ hr] at hZ
    exact connectedSpace_of_factor (isPullback_j M) _ hZ

end Special

theorem isOpenImmersion_tensor {S : Scheme.{0}} {X Y X' Y' : Over S} (f : X ⟶ X') (g : Y ⟶ Y')
    [IsOpenImmersion f.left] [IsOpenImmersion g.left] : IsOpenImmersion (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]; infer_instance

theorem mem_range_tensor {S : Scheme.{0}} {X Y X' Y' : Over S} (f : X ⟶ X') (g : Y ⟶ Y') (z : (X' ⊗ Y').left)
    (h₁ : (fst X' Y').left z ∈ Set.range f.left) (h₂ : (snd X' Y').left z ∈ Set.range g.left) :
    z ∈ Set.range (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  exact (Scheme.Pullback.range_map _ _ _ _ _ _ _ _ _).ge ⟨h₁, h₂⟩

end GlobalTheory.SS.StrictGrp

open GlobalTheory.SS.StrictGrp in

theorem GlobalTheory.SS.exists_grpObj_of_strict : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∃ (G : Model R A) (_ : GrpObj G.Y), SmConn G.Y ∧ IsMonHom G.e.hom ∧ ∀ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom → ∃ s : 𝟙_ (Over (Sp R)) ⟶ G.Y, spMap (algebraMap R K) ≫ s.left = a.left ≫ G.j := by
  intro R K _ _ _ _ _ hSH A _ _ hA M hM
  obtain ⟨G, hGI, hLe, hcov, hmu⟩ := GlobalTheory.T.exists_union_translates' R K hSH A hA M hM
  have hD := hSH.1
  have hF := hSH.2.2.2
  have hMI : M.Irr := hM.1.1
  have hGs := G.smooth
  have hGp := G.sep
  have hext := GlobalTheory.SS.existsUnique_extension_of_forall_defAt R K
  have hsec := GlobalTheory.SS.SectionTranslation.translation_by_section R K hSH A hA M hM
  obtain ⟨-, hcomp, hinv, -⟩ := GlobalTheory.SS.GI.genIso_calculus R K hSH
  let H : (𝟙_ (Over (Sp K)) ⟶ A) → Prop := fun a => GenIso M M (transl a).hom
  have H1 : H 1 := by
    obtain ⟨y, hy⟩ := hMI.nonempty
    exact ⟨y, hy, transl_one (A := A) ▸ isoAt_id M y⟩
  have Hmul : ∀ a b, H a → H b → H (a * b) := fun a b ha hb => by
    have := hcomp _ _ _ M M M _ _ hMI ha hb
    rwa [transl_mul] at this
  have Hinv : ∀ a, H a → H a⁻¹ := fun a ha => by
    have := (hinv _ _ M M (transl a)).1 ha
    rwa [transl_inv] at this
  have hg : ∀ a, H a → ∃ g : M.Y ⟶ G.Y, IsOpenImmersion g.left ∧ M.j ≫ g.left = (transl a).hom.left ≫ G.j :=
    fun a ha => by
      obtain ⟨g, h₁, h₂⟩ := hLe a ha
      exact ⟨g, h₁, twist_comm h₂⟩
  have hc : ∀ y : G.Y.left, ∃ (a : 𝟙_ (Over (Sp K)) ⟶ A) (g : M.Y ⟶ G.Y) (x : M.Y.left), H a ∧
      IsOpenImmersion g.left ∧ M.j ≫ g.left = (transl a).hom.left ≫ G.j ∧ g.left x = y := fun y => by
    obtain ⟨a, g, ha, h₁, h₂, x, hx⟩ := hcov y
    exact ⟨a, g, x, ha, h₁, twist_comm h₂, hx⟩

  have hT : ∀ c, H c → ∃ T : G.Y ⟶ G.Y, G.j ≫ T.left = (transl c).hom.left ≫ G.j := fun c hc' => by
    refine (hext _ _ G G _ fun y => ?_).exists
    obtain ⟨a, g, x, ha, _, h, rfl⟩ := hc y
    obtain ⟨g', -, h'⟩ := hg _ (Hmul a c ha hc')
    exact defAt_transport h h' (by rw [Category.id_comp, transl_mul]) (isoAt_id M x).defAt

  obtain ⟨m, hm⟩ : ∃ m : (G.prod G).Y ⟶ G.Y, (G.prod G).j ≫ m.left = (μ[A]).left ≫ G.j := by
    refine (hext _ _ (G.prod G) G _ fun z => ?_).exists
    obtain ⟨a, g, x, ha, _, h, hx⟩ := hc ((fst G.Y G.Y).left z)
    obtain ⟨b, g', x', hb, _, h', hx'⟩ := hc ((snd G.Y G.Y).left z)
    obtain ⟨w, rfl⟩ := mem_range_tensor g g' z ⟨x, hx⟩ ⟨x', hx'⟩
    obtain ⟨T, hT⟩ := hT _ (Hmul a b ha hb)
    have := isOpenImmersion_tensor g g'
    exact defAt_transport (M := M.prod M) (G := G.prod G) (f := tensorIso (transl a) (transl b)) (g := g ⊗ₘ g')
      (prod_comm h h') hT (mul_transl a b) (hmu w)

  have hmove : ∀ (s : 𝟙_ (Over (Sp R)) ⟶ M.Y) (c a : 𝟙_ (Over (Sp K)) ⟶ A) (g : M.Y ⟶ G.Y),
      c.left ≫ M.j = spMap (algebraMap R K) ≫ s.left → M.j ≫ g.left = (transl a).hom.left ≫ G.j →
      spMap (algebraMap R K) ≫ (s ≫ g).left = (a * c).left ≫ G.j := fun s c a g h₁ h₂ => by
    rw [Over.comp_left, ← Category.assoc, ← h₁, Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, pt_transl]
  have hsecG : ∀ a, H a → ∃ s : 𝟙_ (Over (Sp R)) ⟶ G.Y, spMap (algebraMap R K) ≫ s.left = a.left ≫ G.j :=
    fun a ha => by
      obtain ⟨s, -⟩ := exists_section hSH M isOpen_univ.isLocallyClosed (by simpa using hMI.nonempty)
      obtain ⟨c, h₁, h₂, -⟩ := hsec s
      obtain ⟨g, -, h₃⟩ := hg _ (Hmul _ _ ha (Hinv _ h₂))
      exact ⟨s ≫ g, by rw [hmove s c _ g h₁ h₃, inv_mul_cancel_right]⟩

  obtain ⟨i, hi⟩ : ∃ i : G.Y ⟶ G.Y, G.j ≫ i.left = (ι[A]).left ≫ G.j := by
    refine (hext _ _ G G _ fun y => ?_).exists
    by_contra hy
    have hys : y ∈ G.sp := by_contra fun h => hy (defAt_generic G G _ h)
    obtain ⟨a, g, x, ha, _, h, rfl⟩ := hc y
    have hxs : x ∈ M.sp := by
      have e : G.Y.hom (g.left x) = M.Y.hom x := by rw [← Scheme.Hom.comp_apply, Over.w g]
      exact e.symm.trans hys
    obtain ⟨s, hs⟩ := exists_section hSH M (S := g.left ⁻¹' {y | DefAt G G (ι[A]) y}ᶜ)
      ((isOpen_defAt G G _).isClosed_compl.preimage g.left.continuous).isLocallyClosed ⟨x, hy, hxs⟩
    obtain ⟨x', hx', hx''⟩ := hM.1.2.2
    obtain ⟨u, hu⟩ := exists_section hSH M (isOpen_defAt M M (ι[A])).isLocallyClosed ⟨x', hx''.defAt, hx'⟩
    obtain ⟨c, hc₁, hc₂, -⟩ := hsec s
    obtain ⟨d, hd₁, hd₂, -⟩ := hsec u
    have He := Hmul _ _ (Hmul _ _ ha hc₂) (Hinv _ hd₂)
    obtain ⟨g₁, _, h₁⟩ := hg _ He
    obtain ⟨g₂, -, h₂⟩ := hg _ (Hinv _ He)
    have e : u ≫ g₁ = s ≫ g := ext_section (K := K) (by
      rw [hmove u d _ g₁ hd₁ h₁, hmove s c _ g hc₁ h, inv_mul_cancel_right])
    have e' : g₁.left (u.left (IsLocalRing.closedPoint R)) = g.left (s.left (IsLocalRing.closedPoint R)) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, e]
    exact hs (e' ▸ defAt_transport h₁ h₂ (inv_transl _) hu)
  obtain ⟨e, he⟩ := hsecG 1 H1
  have := GlobalTheory.isOpenImmersion_spMap_of_isDiscreteValuationRing R K
  obtain ⟨inst, -, -, -, hcomm, hpb⟩ := GlobalTheory.grpObj_of_dense_open (Sp R) (Sp K) (spMap (algebraMap R K)) G.Y A G.j
    (isPullback_j G) m i e (fun φ₂ h => by
      obtain rfl : φ₂ = (G.prod G).j := by
        apply Over.tensorObj_ext
        · exact h.1.trans (prod_j_fst G G).symm
        · exact h.2.trans (prod_j_snd G G).symm
      exact hm) hi (by simpa [Hom.one_def] using he)
  have := hA.geomConnected
  refine ⟨G, inst, ⟨hcomm, hGs, hGp, G.qc, geometricallyConnected hSH G hGI⟩, ?_, hsecG⟩
  obtain ⟨e', h₁, h₂⟩ := grpPullback_iso (isGrpPullback_pullback G.Y (spMap (algebraMap R K))) hpb
  have e₀ : G.e.hom = e'.hom := by
    apply Over.OverMorphism.ext
    apply (isPullback_j G).hom_ext
    · rw [h₂, Model.j, ← Category.assoc, ← Over.comp_left, G.e.hom_inv_id, Over.id_left, Category.id_comp]
    · rw [Over.w, Over.w]
  rw [e₀]
  exact h₁
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_grpObj_of_strictBirationalLaw : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∃ (G : Model R A) (_ : GrpObj G.Y), SmConn G.Y ∧ IsMonHom G.e.hom ∧ ∀ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom → ∃ s : 𝟙_ (Over (Sp R)) ⟶ G.Y, spMap (algebraMap R K) ≫ s.left = a.left ≫ G.j := by
  atlas_forward_decl GlobalTheory.SS.exists_grpObj_of_strict
end
