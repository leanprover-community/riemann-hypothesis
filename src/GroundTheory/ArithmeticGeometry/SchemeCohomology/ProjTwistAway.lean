import Mathlib

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite

universe u

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

namespace ProjTwist

abbrev Loc (x : ProjectiveSpectrum 𝒜) : Type u :=
  Localization x.asHomogeneousIdeal.toIdeal.primeCompl

variable {𝒜}

def IsFraction (k : ℤ) {U : Opens (ProjectiveSpectrum.top 𝒜)} (f : ∀ x : U, Loc 𝒜 x.1) : Prop :=
  ∃ (i j : ℕ) (_ : (j : ℤ) = i + k) (r s : A) (_ : r ∈ 𝒜 j) (_ : s ∈ 𝒜 i)
    (s_nin : ∀ x : U, s ∉ x.1.asHomogeneousIdeal), ∀ x : U, f x = Localization.mk r ⟨s, s_nin x⟩

variable (𝒜) in

def isFractionPrelocal (k : ℤ) :
    PrelocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => Loc 𝒜 x where
  pred f := IsFraction k f
  res := by
    rintro V U i f ⟨a, b, hab, r, s, hr, hs, h, w⟩
    exact ⟨a, b, hab, r, s, hr, hs, (h <| i ·), (w <| i ·)⟩

variable (𝒜) in

def isLocallyFraction (k : ℤ) : LocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => Loc 𝒜 x :=
  (isFractionPrelocal 𝒜 k).sheafify

theorem exists_pos_deg_nmem (x : ProjectiveSpectrum 𝒜) :
    ∃ (f : A) (m : ℕ), f ∈ 𝒜 m ∧ 0 < m ∧ f ∉ x.asHomogeneousIdeal := by
  classical
  by_contra! h
  refine x.not_irrelevant_le fun z hz => ?_
  rw [← DirectSum.sum_support_decompose 𝒜 z]
  refine x.1.toIdeal.sum_mem fun n hn => ?_
  by_cases hn0 : n = 0
  · subst hn0
    have : (DirectSum.decompose 𝒜 z 0 : A) = 0 := by
      rw [← GradedRing.proj_apply]
      exact (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hz
    rw [this]
    exact zero_mem _
  · exact h _ n (SetLike.coe_mem _) (Nat.pos_of_ne_zero hn0)

theorem exists_den (k : ℤ) (x : ProjectiveSpectrum 𝒜) :
    ∃ (i j : ℕ) (s : A), (j : ℤ) = i + k ∧ s ∈ 𝒜 i ∧ s ∉ x.asHomogeneousIdeal := by
  obtain ⟨f, m, hf, hm, hfx⟩ := exists_pos_deg_nmem x
  refine ⟨m * (-k).toNat, m * (-k).toNat + k.toNat - (-k).toNat + 0, f ^ (-k).toNat, ?_,
    ?_, fun h => hfx (x.isPrime.mem_of_pow_mem _ h)⟩
  · have : ((-k).toNat : ℤ) ≤ m * (-k).toNat := by
      exact_mod_cast Nat.le_mul_of_pos_left _ hm
    push_cast
    omega
  · simpa [mul_comm] using SetLike.pow_mem_graded (-k).toNat hf

theorem nmem_mul {x : ProjectiveSpectrum 𝒜} {s s' : A} (h : s ∉ x.asHomogeneousIdeal)
    (h' : s' ∉ x.asHomogeneousIdeal) : s * s' ∉ x.asHomogeneousIdeal := fun hh =>
  (x.isPrime.mem_or_mem hh).elim h h'

theorem zero_mem' (k : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    (isLocallyFraction 𝒜 k).pred (0 : ∀ x : U, Loc 𝒜 x.1) := fun x => by
  obtain ⟨i, j, s, hij, hs, hsx⟩ := exists_den k x.1
  refine ⟨U ⊓ ProjectiveSpectrum.basicOpen 𝒜 s, ⟨x.2, hsx⟩, Opens.infLELeft _ _, i, j, hij, 0, s,
    zero_mem _, hs, fun y => y.2.2, fun y => ?_⟩
  simp [Localization.mk_zero]

theorem add_mem' (k : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) (a b : ∀ x : U, Loc 𝒜 x.1)
    (ha : (isLocallyFraction 𝒜 k).pred a) (hb : (isLocallyFraction 𝒜 k).pred b) :
    (isLocallyFraction 𝒜 k).pred (a + b) := fun x => by
  obtain ⟨Va, ma, ia, i, j, hij, r, s, hr, hs, hsn, wa⟩ := ha x
  obtain ⟨Vb, mb, ib, i', j', hij', r', s', hr', hs', hsn', wb⟩ := hb x
  have hdeg : j' + i = j + i' := by omega
  refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, i + i', j + i', by push_cast; omega,
    r * s' + s * r', s * s', add_mem (SetLike.mul_mem_graded hr hs') ?_,
    SetLike.mul_mem_graded hs hs', fun ⟨y, hya, hyb⟩ => ?_, fun ⟨y, hya, hyb⟩ => ?_⟩
  · have := SetLike.mul_mem_graded hs hr'
    rwa [add_comm i j', hdeg] at this
  · exact nmem_mul (hsn ⟨y, hya⟩) (hsn' ⟨y, hyb⟩)
  · have e1 : a (ia ⟨y, hya⟩) = _ := wa ⟨y, hya⟩
    have e2 : b (ib ⟨y, hyb⟩) = _ := wb ⟨y, hyb⟩
    change a (ia ⟨y, hya⟩) + b (ib ⟨y, hyb⟩) = _
    rw [e1, e2, Localization.add_mk]
    congr 1
    ring

theorem neg_mem' (k : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) (a : ∀ x : U, Loc 𝒜 x.1)
    (ha : (isLocallyFraction 𝒜 k).pred a) : (isLocallyFraction 𝒜 k).pred (-a) := fun x => by
  obtain ⟨V, m, iV, i, j, hij, r, s, hr, hs, hsn, w⟩ := ha x
  refine ⟨V, m, iV, i, j, hij, -r, s, neg_mem hr, hs, hsn, fun y => ?_⟩
  simp only [Pi.neg_apply, w y, Localization.neg_mk]

variable (𝒜) in

def twistSheafInType (k : ℤ) : Sheaf (Type u) (ProjectiveSpectrum.top 𝒜) :=
  subsheafToTypes (isLocallyFraction 𝒜 k)

def sectionsSubgroup (k : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    AddSubgroup (∀ x : U, Loc 𝒜 x.1) where
  carrier := {f | (isLocallyFraction 𝒜 k).pred f}
  zero_mem' := zero_mem' k U
  add_mem' := add_mem' k U _ _
  neg_mem' := neg_mem' k U _

instance (k : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    AddCommGroup ((twistSheafInType 𝒜 k).obj.obj U) :=
  (sectionsSubgroup k U.unop).toAddCommGroup

open ProjectiveSpectrum in

def toLocFun (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    (Proj.structureSheaf 𝒜).obj.obj (op U) →+* (∀ x : U, Loc 𝒜 x.1) where
  toFun t x := (t.1 x).val
  map_one' := by funext x; exact HomogeneousLocalization.val_one
  map_mul' a b := by funext x; exact HomogeneousLocalization.val_mul _ _
  map_zero' := by funext x; exact HomogeneousLocalization.val_zero
  map_add' a b := by funext x; exact HomogeneousLocalization.val_add _ _

open ProjectiveSpectrum in
instance (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    Module ((Proj.structureSheaf 𝒜).obj.obj (op U)) (∀ x : U, Loc 𝒜 x.1) :=
  Module.compHom _ (toLocFun U)

open ProjectiveSpectrum in
lemma smul_apply' {U : Opens (ProjectiveSpectrum.top 𝒜)} (t : (Proj.structureSheaf 𝒜).obj.obj (op U))
    (f : ∀ x : U, Loc 𝒜 x.1) (x : U) : (t • f) x = (t.1 x).val * f x := rfl

open ProjectiveSpectrum in

def sectionsSubmodule (k : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    Submodule ((Proj.structureSheaf 𝒜).obj.obj (op U)) (∀ x : U, Loc 𝒜 x.1) where
  __ := sectionsSubgroup k U
  smul_mem' t f hf x := by
    obtain ⟨V, hxV, iV, l, ⟨a, ha⟩, ⟨b, hb⟩, hbn, wt⟩ := t.2 x
    obtain ⟨W, hxW, iW, i, j, hij, r, s, hr, hs, hsn, wf⟩ := hf x
    refine ⟨V ⊓ W, ⟨hxV, hxW⟩, Opens.infLELeft _ _ ≫ iV, l + i, l + j, by push_cast; omega,
      a * r, b * s, SetLike.mul_mem_graded ha hr, SetLike.mul_mem_graded hb hs,
      fun ⟨y, hyV, hyW⟩ => nmem_mul (hbn ⟨y, hyV⟩) (hsn ⟨y, hyW⟩), fun ⟨y, hyV, hyW⟩ => ?_⟩
    have e1 : t.1 (iV ⟨y, hyV⟩) = _ := wt ⟨y, hyV⟩
    have e2 : f (iW ⟨y, hyW⟩) = _ := wf ⟨y, hyW⟩
    change (t.1 (iV ⟨y, hyV⟩)).val * f (iW ⟨y, hyW⟩) = _
    rw [e1, e2, HomogeneousLocalization.val_mk, Localization.mk_mul]
    rfl

open ProjectiveSpectrum in
instance (k : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Module ((Proj.structureSheaf 𝒜).obj.obj U) ((twistSheafInType 𝒜 k).obj.obj U) :=
  (sectionsSubmodule k U.unop).module

variable (𝒜) in

def twistPresheafAb (k : ℤ) : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of ((twistSheafInType 𝒜 k).obj.obj U)
  map i := AddCommGrpCat.ofHom
    { toFun := (twistSheafInType 𝒜 k).obj.map i
      map_zero' := rfl
      map_add' _ _ := rfl }

end ProjTwist

open ProjTwist in

noncomputable def twistingSheaf (k : ℤ) : (Proj 𝒜).Modules where
  val :=
    letI (U : (Opens (Proj 𝒜))ᵒᵖ) :
        Module ((Proj 𝒜).ringCatSheaf.obj.obj U) ((twistPresheafAb 𝒜 k).obj U) :=
      let U' : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ := U
      inferInstanceAs (Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj U')
        ((twistSheafInType 𝒜 k).obj.obj U'))
    PresheafOfModules.ofPresheaf (R := (Proj 𝒜).ringCatSheaf.obj) (twistPresheafAb 𝒜 k)
      fun _ _ _ _ _ => rfl
  isSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2
    (twistSheafInType 𝒜 k).2

namespace ProjTwist

variable {𝒜} {k : ℤ} {U V : (Proj 𝒜).Opens}

def val (s : Γ(twistingSheaf 𝒜 k, U)) : ∀ x : U, Loc 𝒜 x.1 := s.1

lemma isLocallyFraction_val (s : Γ(twistingSheaf 𝒜 k, U)) :
    (isLocallyFraction 𝒜 k).pred (val s) := s.2

def mkSection (f : ∀ x : U, Loc 𝒜 x.1) (hf : (isLocallyFraction 𝒜 k).pred f) :
    Γ(twistingSheaf 𝒜 k, U) := ⟨f, hf⟩

@[simp] lemma val_mkSection (f : ∀ x : U, Loc 𝒜 x.1) (hf : (isLocallyFraction 𝒜 k).pred f) :
    val (mkSection f hf) = f := rfl

@[ext] lemma ext {s t : Γ(twistingSheaf 𝒜 k, U)} (h : val s = val t) : s = t := Subtype.ext h

@[simp] lemma val_add (s t : Γ(twistingSheaf 𝒜 k, U)) : val (s + t) = val s + val t := rfl

@[simp] lemma val_zero : val (0 : Γ(twistingSheaf 𝒜 k, U)) = 0 := rfl

@[simp] lemma val_neg (s : Γ(twistingSheaf 𝒜 k, U)) : val (-s) = -val s := rfl

@[simp] lemma val_sub (s t : Γ(twistingSheaf 𝒜 k, U)) : val (s - t) = val s - val t := rfl

lemma val_smul (t : Γ(Proj 𝒜, U)) (s : Γ(twistingSheaf 𝒜 k, U)) (x : U) :
    val (t • s) x = (t.1 x).val * val s x := rfl

lemma val_res (h : V ≤ U) (s : Γ(twistingSheaf 𝒜 k, U)) (x : V) :
    val ((twistingSheaf 𝒜 k).presheaf.map (homOfLE h).op s) x = val s ⟨x.1, h x.2⟩ := rfl

end ProjTwist

end GroundTheory.Arith.SchemeCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite

universe u

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

noncomputable section

namespace ProjTwist

def fpow (f : A) (n : ℕ) : Submonoid.powers f := ⟨f ^ n, (Submonoid.mem_powers_iff _ _).2 ⟨n, rfl⟩⟩

@[simp] lemma coe_fpow (f : A) (n : ℕ) : (fpow f n : A) = f ^ n := rfl

lemma fpow_add (f : A) (n m : ℕ) : fpow f (n + m) = fpow f n * fpow f m :=
  Subtype.ext (pow_add f n m)

def locMap {f : A} (x : ProjectiveSpectrum 𝒜) (hx : f ∉ x.asHomogeneousIdeal) :
    Localization.Away f →+* Loc 𝒜 x :=
  IsLocalization.map (M := Submonoid.powers f) (T := x.asHomogeneousIdeal.toIdeal.primeCompl) _
    (RingHom.id _) (Submonoid.powers_le.mpr hx)

lemma locMap_mk {f : A} (x : ProjectiveSpectrum 𝒜) (hx : f ∉ x.asHomogeneousIdeal) (a : A)
    (n : ℕ) :
    locMap x hx (Localization.mk a (fpow f n)) =
      Localization.mk a ⟨f ^ n, (Submonoid.powers_le.mpr hx) ⟨n, rfl⟩⟩ := by
  rw [locMap, Localization.mk_eq_mk', IsLocalization.map_mk', Localization.mk_eq_mk']
  rfl

lemma locMap_algebraMap {f : A} (x : ProjectiveSpectrum 𝒜) (hx : f ∉ x.asHomogeneousIdeal)
    (a : A) : locMap x hx (algebraMap A _ a) = algebraMap A _ a := by
  rw [locMap, IsLocalization.map_eq]
  rfl

lemma locMap_comp {f f' : A} (φ : Localization.Away f →+* Localization.Away f')
    (hφ : φ.comp (algebraMap A _) = algebraMap A _) (x : ProjectiveSpectrum 𝒜)
    (hx : f' ∉ x.asHomogeneousIdeal) (hx' : f ∉ x.asHomogeneousIdeal) (z : Localization.Away f) :
    locMap x hx (φ z) = locMap x hx' z := by
  have : (locMap x hx).comp φ = locMap x hx' := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext a
    simp only [RingHom.comp_apply]
    rw [← RingHom.comp_apply φ, hφ, locMap_algebraMap, locMap_algebraMap]
  exact congrArg (fun F => F z) this

variable (𝒜) in

def awayDeg {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) (k : ℤ) :
    AddSubgroup (Localization.Away f) where
  carrier := {z | ∃ (n j : ℕ) (a : A), a ∈ 𝒜 j ∧ (j : ℤ) = n * d + k ∧
    z = Localization.mk a (fpow f n)}
  zero_mem' := ⟨(-k).toNat, (-k).toNat * d + k.toNat - (-k).toNat, 0, zero_mem _, by
    have : (-k).toNat ≤ (-k).toNat * d := Nat.le_mul_of_pos_right _ hd
    omega, by rw [Localization.mk_zero]⟩
  add_mem' := by
    rintro _ _ ⟨n, j, a, ha, hj, rfl⟩ ⟨m, j', b, hb, hj', rfl⟩
    refine ⟨n + m, j + m * d, f ^ n * b + f ^ m * a, add_mem ?_ ?_, ?_, ?_⟩
    · have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded n hf) hb
      have e : n • d + j' = j + m * d := by
        have : ((n • d + j' : ℕ) : ℤ) = ((j + m * d : ℕ) : ℤ) := by
          push_cast [smul_eq_mul]; linarith
        exact_mod_cast this
      rwa [e] at h
    · have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded m hf) ha
      rwa [smul_eq_mul, add_comm] at h
    · push_cast; linarith
    · rw [Localization.add_mk, fpow_add]
      rfl
  neg_mem' := by
    rintro _ ⟨n, j, a, ha, hj, rfl⟩
    exact ⟨n, j, -a, neg_mem ha, hj, by rw [Localization.neg_mk]⟩

lemma mul_mem_awayDeg {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) {k₁ k₂ : ℤ}
    {z w : Localization.Away f} (hz : z ∈ awayDeg 𝒜 hf hd k₁) (hw : w ∈ awayDeg 𝒜 hf hd k₂) :
    z * w ∈ awayDeg 𝒜 hf hd (k₁ + k₂) := by
  obtain ⟨n, j, a, ha, hj, rfl⟩ := hz
  obtain ⟨m, j', b, hb, hj', rfl⟩ := hw
  refine ⟨n + m, j + j', a * b, SetLike.mul_mem_graded ha hb, by push_cast; linarith, ?_⟩
  rw [Localization.mk_mul, fpow_add]

lemma mk_mem_awayDeg {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) {k : ℤ} {n j : ℕ} {a : A}
    (ha : a ∈ 𝒜 j) (hj : (j : ℤ) = n * d + k) :
    Localization.mk a (fpow f n) ∈ awayDeg 𝒜 hf hd k :=
  ⟨n, j, a, ha, hj, rfl⟩

lemma exists_val_eq_of_mem_awayDeg_zero {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    {z : Localization.Away f} (hz : z ∈ awayDeg 𝒜 hf hd 0) :
    ∃ z₀ : HomogeneousLocalization.Away 𝒜 f, z₀.val = z := by
  obtain ⟨n, j, a, ha, hj, rfl⟩ := hz
  have e : n • d = j := by
    have : ((n • d : ℕ) : ℤ) = j := by push_cast [smul_eq_mul]; linarith
    exact_mod_cast this
  refine ⟨HomogeneousLocalization.mk ⟨j, ⟨a, ha⟩, ⟨f ^ n, e ▸ SetLike.pow_mem_graded n hf⟩,
    (fpow f n).2⟩, ?_⟩
  rw [HomogeneousLocalization.val_mk]
  rfl

lemma nmem_of_mem {f : A} (x : Proj.basicOpen 𝒜 f) : f ∉ x.1.asHomogeneousIdeal := x.2

def toSection {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) (k : ℤ) :
    awayDeg 𝒜 hf hd k →+ Γ(twistingSheaf 𝒜 k, Proj.basicOpen 𝒜 f) where
  toFun z := mkSection (fun x => locMap x.1 (nmem_of_mem x) z.1) (fun x => by
    obtain ⟨n, j, a, ha, hj, hz⟩ := z.2
    refine ⟨Proj.basicOpen 𝒜 f, x.2, 𝟙 _, n * d, j, by push_cast; linarith, a, f ^ n, ha,
      ?_, fun y h => nmem_of_mem y (y.1.isPrime.mem_of_pow_mem n h), fun y => ?_⟩
    · have := SetLike.pow_mem_graded n hf
      rwa [smul_eq_mul] at this
    · change locMap y.1 (nmem_of_mem y) z.1 = _
      rw [hz]
      exact locMap_mk y.1 (nmem_of_mem y) a n)
  map_zero' := by
    ext x
    exact map_zero _
  map_add' z w := by
    ext x
    exact map_add _ _ _

lemma val_mem_awayDeg_zero {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (z₀ : HomogeneousLocalization.Away 𝒜 f) : z₀.val ∈ awayDeg 𝒜 hf hd 0 := by
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf z₀
  rw [HomogeneousLocalization.Away.val_mk]
  exact mk_mem_awayDeg hf hd ha (by push_cast [smul_eq_mul]; ring)

lemma isLocallyFraction_mul {U : Opens (ProjectiveSpectrum.top 𝒜)} {k₁ k₂ k₃ : ℤ}
    (hk : k₁ + k₂ = k₃) {a b : ∀ x : U, Loc 𝒜 x.1} (ha : (isLocallyFraction 𝒜 k₁).pred a)
    (hb : (isLocallyFraction 𝒜 k₂).pred b) : (isLocallyFraction 𝒜 k₃).pred (a * b) := fun x => by
  obtain ⟨Va, ma, ia, i, j, hij, r, s, hr, hs, hsn, wa⟩ := ha x
  obtain ⟨Vb, mb, ib, i', j', hij', r', s', hr', hs', hsn', wb⟩ := hb x
  refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, i + i', j + j', by push_cast; omega,
    r * r', s * s', SetLike.mul_mem_graded hr hr', SetLike.mul_mem_graded hs hs',
    fun ⟨y, hya, hyb⟩ => nmem_mul (hsn ⟨y, hya⟩) (hsn' ⟨y, hyb⟩), fun ⟨y, hya, hyb⟩ => ?_⟩
  have e1 : a (ia ⟨y, hya⟩) = _ := wa ⟨y, hya⟩
  have e2 : b (ib ⟨y, hyb⟩) = _ := wb ⟨y, hyb⟩
  change a (ia ⟨y, hya⟩) * b (ib ⟨y, hyb⟩) = _
  rw [e1, e2, Localization.mk_mul]
  rfl

lemma isLocallyFraction_locMap {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) {k : ℤ}
    {z : Localization.Away f} (hz : z ∈ awayDeg 𝒜 hf hd k) :
    (isLocallyFraction 𝒜 k).pred
      (fun x : (Proj.basicOpen 𝒜 f : Opens (ProjectiveSpectrum.top 𝒜)) =>
        locMap x.1 (nmem_of_mem x) z) :=
  (toSection hf hd k ⟨z, hz⟩).2

set_option backward.isDefEq.respectTransparency.types false in
open ProjectiveSpectrum in

lemma exists_section_of_isLocallyFraction_zero {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (t : ∀ x : U, Loc 𝒜 x.1) (ht : (isLocallyFraction 𝒜 0).pred t) :
    ∃ t' : (Proj.structureSheaf 𝒜).obj.obj (op U), ∀ x, (t'.1 x).val = t x := by
  have key : ∀ x : U, ∃ (V : Opens (ProjectiveSpectrum.top 𝒜)) (_ : x.1 ∈ V) (iV : V ⟶ U)
      (j : ℕ) (r s : 𝒜 j) (s_nin : ∀ y : V, s.1 ∉ y.1.asHomogeneousIdeal),
      ∀ y : V, t (iV y : U) = Localization.mk r.1 ⟨s.1, s_nin y⟩ := by
    intro x
    obtain ⟨V, hxV, iV, i, j, hij, r, s, hr, hs, hsn, w⟩ := ht x
    have e : i = j := by omega
    subst e
    exact ⟨V, hxV, iV, i, ⟨r, hr⟩, ⟨s, hs⟩, hsn, w⟩
  have pt : ∀ x : U, ∃ y : HomogeneousLocalization.AtPrime 𝒜
      x.1.asHomogeneousIdeal.toIdeal, y.val = t x := by
    intro x
    obtain ⟨V, hxV, iV, j, r, s, hsn, w⟩ := key x
    exact ⟨HomogeneousLocalization.mk ⟨j, r, s,
      (show s.1 ∈ x.1.asHomogeneousIdeal.toIdeal.primeCompl from hsn ⟨x.1, hxV⟩)⟩,
      by rw [HomogeneousLocalization.val_mk]; exact (w ⟨x.1, hxV⟩).symm⟩
  choose g hg using pt
  refine ⟨(⟨g, fun x => ?_⟩ : (StructureSheaf.structureSheafInType 𝒜).obj.obj (op U)), hg⟩
  obtain ⟨V, hxV, iV, j, r, s, hsn, w⟩ := key x
  refine ⟨V, hxV, iV, j, r, s, hsn, fun y => HomogeneousLocalization.val_injective _ ?_⟩
  rw [HomogeneousLocalization.val_mk]
  exact (hg _).trans (w y)

theorem toSection_bijective {f u g : A} {e : ℕ} (hu : u ∈ 𝒜 1) (hg : g ∈ 𝒜 e)
    (hfug : f = u * g) (hf : f ∈ 𝒜 (e + 1)) (k : ℤ) :
    Function.Bijective (toSection hf (Nat.succ_pos e) k) := by
  set hd := Nat.succ_pos e
  have hk : (k.toNat : ℤ) - ((-k).toNat : ℤ) = k := by omega

  set c : Localization.Away f := Localization.mk (u ^ (-k).toNat * g ^ k.toNat) (fpow f k.toNat)
  set c' : Localization.Away f := Localization.mk (u ^ k.toNat * g ^ (-k).toNat) (fpow f (-k).toNat)
  have hc : c ∈ awayDeg 𝒜 hf hd (-k) := by
    refine mk_mem_awayDeg hf hd (j := (-k).toNat + k.toNat * e) ?_ ?_
    · have h1 := SetLike.pow_mem_graded (-k).toNat hu
      have h2 := SetLike.pow_mem_graded k.toNat hg
      have := SetLike.mul_mem_graded h1 h2
      simpa [smul_eq_mul, mul_comm] using this
    · push_cast; linarith
  have hc' : c' ∈ awayDeg 𝒜 hf hd k := by
    refine mk_mem_awayDeg hf hd (j := k.toNat + (-k).toNat * e) ?_ ?_
    · have h1 := SetLike.pow_mem_graded k.toNat hu
      have h2 := SetLike.pow_mem_graded (-k).toNat hg
      have := SetLike.mul_mem_graded h1 h2
      simpa [smul_eq_mul, mul_comm] using this
    · push_cast; linarith
  have hcc' : c * c' = 1 := by
    rw [Localization.mk_mul, ← fpow_add, ← Localization.mk_self (fpow f (k.toNat + (-k).toNat))]
    congr 1
    rw [coe_fpow, hfug]
    ring
  have hloc : ∀ x : Proj.basicOpen 𝒜 f,
      locMap x.1 (nmem_of_mem x) c * locMap x.1 (nmem_of_mem x) c' = 1 := fun x => by
    rw [← map_mul, hcc', map_one]
  have hiso := (Proj.basicOpenIsoAway 𝒜 f hf hd).commRingCatIsoToRingEquiv.bijective
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    have hz' : ∀ x : Proj.basicOpen 𝒜 f, locMap x.1 (nmem_of_mem x) z.1 = 0 := fun x =>
      congrFun (congrArg val hz) x
    have hw : c * z.1 ∈ awayDeg 𝒜 hf hd 0 := by
      have := mul_mem_awayDeg hf hd hc z.2
      rwa [neg_add_cancel] at this
    obtain ⟨z₀, hz₀⟩ := exists_val_eq_of_mem_awayDeg_zero hf hd hw
    have h0 : (Proj.awayToSection 𝒜 f).hom z₀ = 0 := by
      apply Subtype.ext
      funext x
      apply HomogeneousLocalization.val_injective
      have h := ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 f z₀ x
      have h' : locMap x.1 (nmem_of_mem x) z₀.val = 0 := by
        rw [hz₀, map_mul, hz' x, mul_zero]
      exact h.trans (h'.trans HomogeneousLocalization.val_zero.symm)
    have hz0 : z₀ = 0 := by
      apply hiso.1
      exact h0.trans (map_zero _).symm
    have hcz : c * z.1 = 0 := by rw [← hz₀, hz0, HomogeneousLocalization.val_zero]
    apply Subtype.ext
    change z.1 = 0
    calc z.1 = c' * (c * z.1) := by rw [← mul_assoc, mul_comm c', hcc', one_mul]
      _ = 0 := by rw [hcz, mul_zero]
  · intro s
    have ht := isLocallyFraction_mul (neg_add_cancel k) (isLocallyFraction_locMap hf hd hc)
      (isLocallyFraction_val s)
    obtain ⟨t', ht'⟩ := exists_section_of_isLocallyFraction_zero _ ht
    obtain ⟨z₀, hz₀⟩ := hiso.2 t'
    have hz₀' : (Proj.awayToSection 𝒜 f).hom z₀ = t' := hz₀
    have hmem : c' * z₀.val ∈ awayDeg 𝒜 hf hd k := by
      have := mul_mem_awayDeg hf hd hc' (val_mem_awayDeg_zero hf hd z₀)
      rwa [add_zero] at this
    refine ⟨⟨c' * z₀.val, hmem⟩, ?_⟩
    subst hz₀'
    ext x
    have e1 : locMap x.1 (nmem_of_mem x) z₀.val =
        (((Proj.awayToSection 𝒜 f).hom z₀).1 x).val :=
      (ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 f z₀ x).symm
    have e2 : (((Proj.awayToSection 𝒜 f).hom z₀).1 x).val =
        locMap x.1 (nmem_of_mem x) c * val s x := ht' x
    show locMap x.1 (nmem_of_mem x) (c' * z₀.val) = val s x
    rw [map_mul, e1, e2]
    linear_combination (val s x) * hloc x

end ProjTwist

end

end GroundTheory.Arith.SchemeCoh
end
