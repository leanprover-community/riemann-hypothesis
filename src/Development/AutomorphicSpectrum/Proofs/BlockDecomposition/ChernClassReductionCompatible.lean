import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.IsFirstChernClassOfLineBundle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyRestrictionBetweenStableFamilies
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCrystallineLift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineCocycleClosedStatement

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_restriction_between_stable_families : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : Used Q₀)
    (𝒱 : Set X.Opens) (Q' : ObjectProperty (Thick (nlFun γ p X q κ))) (h : St Q₀ 𝒱 ≤ Q') (h' : Q' ≤ St Q₀ {sSup 𝒱})
    (hc : ∀ T T' : Thick (nlFun γ p X q κ), (T ⟶ T') → Q' T → Q₀ T' → Q' T') (j : ℕ),
    (∀ r r' : ℤ, Function.Bijective (((incl h).sq (incl_fil h r) (incl_fil h r')).pull j)) ∧
    (∀ (r r' : Option ℤ) (c c' : R), Function.Bijective (((incl h).sq (incl_std h r c) (incl_std h r' c')).pull j)) ∧
    Function.Bijective ((incl h).o.pull j) := by
  first | exact @GlobalTheory.CompanionTheory.ZarCosieve.main | exact GlobalTheory.CompanionTheory.ZarCosieve.main | (intros; apply GlobalTheory.CompanionTheory.ZarCosieve.main <;> assumption)
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.CrystallineChernClass

theorem mapH_bijective {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {K : Cx.{1} R} {M : Cx.{1} R'}
    (φ : Cx.Hom K M σ) (h : ∀ n, Function.Bijective (φ.f n)) (n : ℕ) : Function.Bijective (φ.mapH n) := by
  refine ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero (φ.mapH n)).2 fun x hx => ?_
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : φ.f n z.1 ∈ M.B n := (Submodule.Quotient.mk_eq_zero ((M.B n).submoduleOf (M.Z n)) (x := φ.mapZ n z)).1 hx
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    change z.1 ∈ K.B n
    cases n with
    | zero =>
      have h2 : φ.f 0 z.1 = 0 := h1
      have h3 : z.1 = 0 := (h 0).1 (h2.trans (map_zero _).symm)
      rw [h3]
      exact Submodule.zero_mem _
    | succ n =>
      obtain ⟨y, hy⟩ := h1
      obtain ⟨y', rfl⟩ := (h n).2 y
      refine ⟨y', (h (n + 1)).1 ?_⟩
      rw [← φ.comm, hy]
  · intro y
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨x, hx⟩ := (h n).2 w.1
    have h0 : K.d n x = 0 := (h (n + 1)).1 (by
      rw [← φ.comm, hx, map_zero]
      exact w.2)
    exact ⟨Submodule.Quotient.mk ⟨x, h0⟩, congrArg _ (Subtype.ext hx)⟩

section Gen

variable {b : Base} {L : b.Fun} {Λ : Type} [CommRing Λ] (c : Λ →+* b.R)

def toO (Q : ObjectProperty (Thick L)) : CH.Mor (Q.ι ⋙ B.OM L c) (CH.modF (sP Q).A) c where
  G := 𝟭 _
  τ T := { toFun := fun x => x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  nat _ _ := rfl

theorem toO_bij (Q : ObjectProperty (Thick L)) (n : ℕ) : Function.Bijective ((toO c Q).pull n) :=
  mapH_bijective _ (fun _ => Function.bijective_id) n

def sub {P Q : ObjectProperty (Thick L)} (h : Q ≤ P) : CH.Mor (P.ι ⋙ B.OM L c) (Q.ι ⋙ B.OM L c) (RingHom.id Λ) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem sub_square {P Q : ObjectProperty (Thick L)} (h : Q ≤ P) (j : ℕ) (x : CH.H (P.ι ⋙ B.OM L c) j) :
    (toO c Q).pull j ((sub c h).pull j x) = (incl h).o.pull j ((toO c P).pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem sub_bij {P Q : ObjectProperty (Thick L)} (h : Q ≤ P) (j : ℕ) (hb : Function.Bijective ((incl h).o.pull j)) :
    Function.Bijective ((sub c h).pull j) := by
  have e : (toO c Q).pull j ∘ (sub c h).pull j = (incl h).o.pull j ∘ (toO c P).pull j :=
    funext (sub_square c h j)
  refine (Function.Bijective.of_comp_iff' (toO_bij c Q j) _).1 ?_
  rw [e]
  exact hb.comp (toO_bij c P j)

theorem sub_sub {P Q S : ObjectProperty (Thick L)} (h : Q ≤ P) (h' : S ≤ Q) (j : ℕ) (x : CH.H (P.ι ⋙ B.OM L c) j) :
    (sub c h').pull j ((sub c h).pull j x) = (sub c (h'.trans h)).pull j x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem res_sub {P Q : ObjectProperty (Thick L)} (h : Q ≤ P) (j : ℕ) (x : CH.H (B.OM L c) j) :
    (sub c h).pull j ((CH.Mor.restrict (B.OM L c) P.ι).pull j x) = (CH.Mor.restrict (B.OM L c) Q.ι).pull j x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem res_all (P : ObjectProperty (Thick L)) (hP : ∀ T, P T) (j : ℕ) :
    Function.Bijective ((CH.Mor.restrict (B.OM L c) P.ι).pull j) := by
  refine mapH_bijective _ (fun n => ⟨fun f g e => ?_, fun g => ?_⟩) j
  · funext t
    exact congrFun e (P.lift t fun i => hP _)
  · exact ⟨fun t => g (P.lift t fun i => hP _), rfl⟩

theorem bij_three {P Q S : ObjectProperty (Thick L)} (h : Q ≤ P) (h1 : S ≤ Q) (h2 : S ≤ P) (j : ℕ)
    (b1 : Function.Bijective ((incl h1).o.pull j)) (b2 : Function.Bijective ((incl h2).o.pull j)) (hP : ∀ T, P T) :
    Function.Bijective ((CH.Mor.restrict (B.OM L c) Q.ι).pull j) := by
  have s1 := sub_bij c h1 j b1
  have s2 := sub_bij c h2 j b2
  have s3 : Function.Bijective ((sub c h).pull j) := by
    have e : (sub c h1).pull j ∘ (sub c h).pull j = (sub c h2).pull j := funext (sub_sub c h h1 j)
    refine (Function.Bijective.of_comp_iff' s1 _).1 ?_
    rw [e]
    exact s2
  have e : (sub c h).pull j ∘ (CH.Mor.restrict (B.OM L c) P.ι).pull j =
      (CH.Mor.restrict (B.OM L c) Q.ι).pull j := funext (res_sub c h j)
  rw [← e]
  exact s3.comp (res_all c _ hP j)

end Gen

end GlobalTheory.CompanionTheory.CrystallineChernClass

namespace GlobalTheory.CompanionTheory.CrystallineChernClass

section Core

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
  {κ : O →+* b.R ⧸ b.I}

def precomp {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {g : C ⥤ Thick ((B.schFn q).cr b ht κ)} {D : E.LineData X}
    (Λ₀ : B.CLift g D) (h : C' ⥤ C) : B.CLift (h ⋙ g) D where
  p c := Λ₀.p (h.obj c)
  hp c := Λ₀.hp (h.obj c)
  w φ := Λ₀.w (h.map φ)
  hw φ hh := Λ₀.hw (h.map φ) hh

theorem exu_core (D : E.LineData X) (Q : ObjectProperty (Thick ((B.schFn q).cr b ht κ)))
    (hQ : ∀ T, Q T ↔ ∃ a : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ D.Y, a ≫ D.f = B.thPt T)
    {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (N : ℕ)
    (hbij : Function.Bijective ((CH.Mor.restrict (B.OM ((B.schFn q).cr b ht κ) c) Q.ι).pull 2))
    (hN : ∀ (T : Thick ((B.schFn q).cr b ht κ)) (k : ℕ), N ≤ k → (k.factorial : T.B) = 0) :
    ∃! x, B.IsFirstChernClassOfLineBundle (q := q) (b := b) (ht := ht) (κ := κ) D c N x := by
  obtain ⟨Λ₀⟩ := GlobalTheory.CompanionTheory.CLiftEx.nonempty_cLift Q.ι D (fun T => (hQ _).1 T.property)
  have hz₀ := (GlobalTheory.T.crystalline_cocycle_closed Q.ι D c N (fun T k hk x _ => by
    change ((k.factorial : ℕ) : (T.obj).B) * _ = 0
    rw [hN _ k hk, zero_mul])).1 Λ₀
  obtain ⟨x, hx⟩ := hbij.2 ((CH.cx _).cls _ hz₀)
  refine ⟨x, ?_, ?_⟩
  · intro C _ G Λ₁
    have hG : ∀ T, Q (G.obj T) := fun T => (hQ _).2 ⟨Λ₁.p T, Λ₁.hp T⟩
    have hcl := GlobalTheory.T.crystalline_cocycle_closed G D c N (fun T k hk x _ => by rw [hN _ k hk, zero_mul])
    let Λ' : B.CLift G D := precomp Λ₀ (Q.lift G hG)
    refine ⟨hcl.1 Λ₁, ?_⟩
    rw [hcl.2 Λ₁ Λ' (hcl.1 Λ₁) (hcl.1 Λ')]
    have e1 : (CH.Mor.restrict (B.OM ((B.schFn q).cr b ht κ) c) G).pull 2 x =
        (CH.Mor.restrict (Q.ι ⋙ B.OM ((B.schFn q).cr b ht κ) c) (Q.lift G hG)).pull 2
          ((CH.Mor.restrict (B.OM ((B.schFn q).cr b ht κ) c) Q.ι).pull 2 x) := by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl
    rw [e1, hx]
    rfl
  · intro y hy
    apply hbij.1
    obtain ⟨h1, h2⟩ := hy _ Q.ι Λ₀
    rw [hx, ← h2]

end Core

section Main

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

def Lifts (D : E.LineData X) : ObjectProperty (Thick (nlFun γ p X q κ)) :=
  fun T => ∃ a : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ D.Y, a ≫ D.f = pt T

theorem st_le_lifts (D : E.LineData X) : St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (𝒱D D) ≤ Lifts D := by
  rintro T ⟨-, V, ⟨σ, hσ⟩, hV⟩
  have hr : Set.range (pt T) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hV (show x ∈ (⊤ : Scheme.Opens _) from trivial)
  refine ⟨IsOpenImmersion.lift V.ι (pt T) hr ≫ σ, ?_⟩
  rw [Category.assoc, hσ, IsOpenImmersion.lift_fac]

theorem inU_top (T : Thick (nlFun γ p X q κ)) : InU ⊤ T := fun _ _ => trivial

theorem lifts_map (D : E.LineData X) {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') (h : Lifts D T) : Lifts D T' := by
  obtain ⟨a, ha⟩ := h
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ a, ?_⟩
  rw [Category.assoc, ha]
  exact congrArg (fun y => y.1.2) φ.pt

theorem res_bij (hp : p ≠ 0) (D : E.LineData X) (hD : sSup (𝒱D D) = ⊤) {Λ : Type} [CommRing Λ] (c : Λ →+* R) (j : ℕ) :
    Function.Bijective ((CH.Mor.restrict (B.OM (nlFun γ p X q κ) c) (Lifts D).ι).pull j) := by
  have hU : Used (⊤ : ObjectProperty (Thick (nlFun γ p X q κ))) := Or.inr ⟨hp, Or.inl rfl⟩
  have h1 : St ⊤ (𝒱D D) ≤ Lifts (γ := γ) (p := p) (q := q) (κ := κ) D := st_le_lifts D
  have h1' : Lifts (γ := γ) (p := p) (q := q) (κ := κ) D ≤ St ⊤ {sSup (𝒱D D)} := fun T _ =>
  ⟨trivial, _, rfl, by rw [hD]; exact inU_top T⟩
  have b1 := (GlobalTheory.T.cohomology_restriction_between_stable_families ⊤ hU (𝒱D D) (Lifts D) h1 h1' (fun T T' φ h _ => lifts_map D φ h) j).2.2
  have h2 : St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (𝒱D D) ≤ St ⊤ {⊤} := fun T _ => ⟨trivial, ⊤, rfl, inU_top T⟩
  have b2 := (GlobalTheory.T.cech_refinement_cohomology_bijective ⊤ hU (𝒱D D) {⊤} h2 (by rintro W rfl; rw [hD]) j).2.2
  have h3 : Lifts (γ := γ) (p := p) (q := q) (κ := κ) D ≤ St ⊤ {⊤} := fun T _ => ⟨trivial, ⊤, rfl, inU_top T⟩
  have hall : ∀ T, St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ {⊤} T := fun T => ⟨trivial, ⊤, rfl, inU_top T⟩
  exact bij_three (b := nlBase R I γ p) (L := nlFun γ p X q κ) c h3 h1 h2 j b1 b2 hall

end Main

theorem existsUnique_crystalline_chern_class : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) (D : E.LineData X) (hD : sSup (𝒱D D) = ⊤) {Λ : Type} [CommRing Λ]
    (c : Λ →+* R) (N : ℕ), (N.factorial : R) = 0 →
    ∃! x, B.IsFirstChernClassOfLineBundle (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) D c N x := by
  intro O R _ _ I γ p hp X q κ D hD Λ _ c N hN
  have hf : ∀ (T : Thick ((B.schFn q).cr (nlBase R I γ p) rfl κ)) (k : ℕ), N ≤ k → (k.factorial : T.B) = 0 := fun T k hk => by
    obtain ⟨m, hm⟩ := Nat.factorial_dvd_factorial hk
    have h0 : (k.factorial : R) = 0 := by rw [hm, Nat.cast_mul, hN, zero_mul]
    have := congrArg T.i h0
    rwa [map_natCast, map_zero] at this
  have hb := res_bij (γ := γ) (q := q) (κ := κ) hp D hD c 2
  let Q : ObjectProperty (Thick ((B.schFn q).cr (nlBase R I γ p) rfl κ)) := Lifts (γ := γ) (p := p) (q := q) (κ := κ) D
  have hQ : ∀ T, Q T ↔ ∃ a : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ D.Y, a ≫ D.f = B.thPt T := fun T => Iff.rfl
  have hb' : Function.Bijective ((CH.Mor.restrict (B.OM ((B.schFn q).cr (nlBase R I γ p) rfl κ) c) Q.ι).pull 2) := hb
  exact exu_core (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) D Q hQ c N hb' hf

end GlobalTheory.CompanionTheory.CrystallineChernClass
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_chern_class_nilpotent_base : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) (D : E.LineData X) (hD : sSup (𝒱D D) = ⊤) {Λ : Type} [CommRing Λ]
    (c : Λ →+* R) (N : ℕ), (N.factorial : R) = 0 →
    ∃! x, B.IsFirstChernClassOfLineBundle (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) D c N x := by
  first | exact @GlobalTheory.CompanionTheory.CrystallineChernClass.existsUnique_crystalline_chern_class | exact GlobalTheory.CompanionTheory.CrystallineChernClass.existsUnique_crystalline_chern_class | (intros; apply GlobalTheory.CompanionTheory.CrystallineChernClass.existsUnique_crystalline_chern_class <;> assumption)
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.FirstChernClassFactorial

theorem pow_dvd_factorial_mul (l : ℕ) (hl : 0 < l) (n : ℕ) : l ^ n ∣ (l * n).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (l * n).factorial * l.factorial ∣ (l * n + l).factorial :=
      Nat.factorial_mul_factorial_dvd_factorial_add _ _
    have h2 : l ∣ l.factorial := Nat.dvd_factorial hl le_rfl
    rw [pow_succ, Nat.mul_succ]
    exact (mul_dvd_mul ih h2).trans h1

theorem factorial_acr {l : ℕ} [Fact l.Prime] (n k : ℕ) (hk : l * n ≤ k) : (k.factorial : (PAlg.base l).Acr n) = 0 := by
  obtain ⟨a, ha⟩ := (pow_dvd_factorial_mul l (Fact.out : l.Prime).pos n).trans (Nat.factorial_dvd_factorial hk)
  rw [ha, Nat.cast_mul, Nat.cast_pow, (PAlg.base l).pow_l_acr n, zero_mul]

theorem dlog_eq_of_factorial {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J) {N N' : ℕ} (h : N ≤ N')
    (hf : ∀ k, N ≤ k → (k.factorial : A) = 0) (v : A) : B.dlog δ N' v = B.dlog δ N v := by
  unfold B.dlog
  refine (Finset.sum_subset (Finset.range_mono h) fun k _ hk => ?_).symm
  rw [hf k (by simpa using hk)]
  simp

open B in

theorem isFirstChern_base_change {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b b' : Base}
    {ht : b.t = 1} {ht' : b'.t = 1} {κ : O →+* b.R ⧸ b.I} {κ' : O →+* b'.R ⧸ b'.I}
    (σ : b.R →+* b'.R) (hp : b.p = b'.p) (hI : IsDPMorphism b.γ b'.γ σ) (τ : b.R ⧸ b.I →+* b'.R ⧸ b'.I)
    (hτ : τ.comp κ = κ') (hτσ : ∀ r, τ (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (σ r))
    {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (c' : Λ →+* b'.R) (hc : ∀ a, σ (c a) = c' (RingHom.id Λ a))
    (D : E.LineData X) {N N' : ℕ} (hN : N ≤ N') (hf : ∀ k, N ≤ k → (k.factorial : b'.R) = 0)
    (y : CH.H (OM ((schFn q).cr b ht κ) c) 2)
    (hy : IsFirstChernClassOfLineBundle (q := q) (b := b) (ht := ht) (κ := κ) D c N' y) :
    IsFirstChernClassOfLineBundle (q := q) (b := b') (ht := ht') (κ := κ') D c' N
      ((omMor (crMor (F := schFn q) (F' := schFn q) (b := b) (b' := b') (ht := ht) (ht' := ht') σ hp hI
        (basePt (schFn q) τ hτ) fun _ y r => congrArg y.1.1 (hτσ r)) (RingHom.id Λ) hc).pull 2 y) := by
  intro C _ G Lf
  let mm := omMor (c := c) (c' := c') (crMor (F := schFn q) (F' := schFn q) (b := b) (b' := b') (ht := ht) (ht' := ht') σ hp hI
        (basePt (schFn q) τ hτ) fun _ y r => congrArg y.1.1 (hτσ r)) (RingHom.id Λ) hc
  let G' : C ⥤ Thick ((schFn q).cr b ht κ) := G ⋙ mm.G
  let Lf' : CLift G' D := { p := Lf.p, hp := Lf.hp, w := Lf.w, hw := Lf.hw }
  obtain ⟨hz', hcl⟩ := hy C G' Lf'
  let m4 : CH.Mor (G' ⋙ OM _ c) (G ⋙ OM _ c') (RingHom.id _) :=
    { G := 𝟭 C, τ := fun T => mm.τ (G.obj T), nat := fun φ x => mm.nat (G.map φ) x }
  have hE : m4.pullC 2 (Lf'.coc c N') = Lf.coc c' N := by
    funext s
    refine dlog_eq_of_factorial (G.obj (s.obj (Fin.last 2))).δ hN (fun j hj => ?_) _
    have := congrArg (G.obj (s.obj (Fin.last 2))).i (hf j hj)
    rw [map_natCast, map_zero] at this
    exact this
  have hz : CH.d _ 2 (Lf.coc c' N) = 0 := by
    rw [← hE, m4.d_pullC, hz', map_zero]
  refine ⟨hz, ?_⟩
  have h1 : (CH.Mor.restrict (OM _ c') G).pull 2 (mm.pull 2 y) =
      m4.pull 2 ((CH.Mor.restrict (OM _ c) G').pull 2 y) := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rfl
  refine Eq.trans ?_ h1.symm
  rw [← hcl]
  have key : ∀ (z : CH.Cn (G ⋙ OM _ c') 2) (h : CH.d _ 2 z = 0), z = Lf.coc c' N →
      (CH.cx _).cls z h = (CH.cx _).cls (Lf.coc c' N) hz := by
    rintro _ _ rfl
    rfl
  exact (key (m4.pullC 2 (Lf'.coc c N')) (by rw [m4.d_pullC, hz', map_zero]) hE).symm

open B in

theorem chern_class_reduction_compatible {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* OC l) (k : Bool)
    (D : E.LineData X) (n : ℕ) (y : B.Hc (schFn q) κ k (n + 1) 2)
    (hy : IsFirstChernClassOfLineBundle (q := q) (b := bs l k (n + 1)) (ht := rfl) (κ := κb κ k (n + 1)) D ((PAlg.base l).cris (n + 1)) (l * (n + 1)) y) :
    IsFirstChernClassOfLineBundle (q := q) (b := bs l k n) (ht := rfl) (κ := κb κ k n) D ((PAlg.base l).cris n) (l * n)
      (redHc (schFn q) κ k n.le_succ 2 y) :=
  isFirstChern_base_change (b := bs l k (n + 1)) (b' := bs l k n) ((PAlg.base l).red n.le_succ) rfl (dd_red k _ n.le_succ)
    (Ideal.quotientMap _ _ (red_le k n.le_succ)) (red_κb κ k n.le_succ) (fun _ => rfl) _ _ (red_cris _ n.le_succ) D
    (Nat.mul_le_mul_left l n.le_succ) (fun j hj => factorial_acr n j hj) y hy

theorem exists_C1H {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (D : E.LineData M.X)
    (hD : sSup (𝒱D D) = ⊤) : ∃ x : (M.HS false 2).lim, B.IsFirstChernFamily M.p D (okToOC l K) false x.1 := by
  have ex : ∀ n, ∃! x, B.IsFirstChernClassOfLineBundle (q := M.p) (b := B.bs l false n) (ht := rfl) (κ := B.κb (okToOC l K) false n) D
      ((PAlg.base l).cris n) (l * n) x := fun n =>
    GlobalTheory.T.existsUnique_chern_class_nilpotent_base (B.DD false (PAlg.base l) n) l (Fact.out : l.Prime).ne_zero M.p (B.κb (okToOC l K) false n) D hD
      ((PAlg.base l).cris n) (l * n) (factorial_acr n _ le_rfl)
  choose x hx hu using ex
  refine ⟨⟨x, fun n => ?_⟩, hx⟩
  exact hu n _ (chern_class_reduction_compatible M.p (okToOC l K) false D n (x (n + 1)) (hx (n + 1)))

end GlobalTheory.CompanionTheory.FirstChernClassFactorial
end
