import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlmostFiniteModuleBoundedTorsion
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LimLift

open CrystallineSemistableComparison.CechClassBoundaries

variable {R : Type} [CommRing R]

theorem cls_congr {K : Cx.{1} R} {j : ℕ} {a b : K.X j} (h : a = b) (ha : K.d j a = 0) (hb : K.d j b = 0) :
    K.cls a ha = K.cls b hb := by
  subst h
  rfl

theorem pow_tf {K : Cx.{1} R} {c : R} (ht : ∀ j (x : K.X j), c • x = 0 → x = 0) (n j : ℕ) (x : K.X j)
    (h : c ^ n • x = 0) : x = 0 := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ', mul_smul] at h
    exact ih (ht _ _ h)

theorem ker_red {K L : Cx.{1} R} (c : R) (n : ℕ) (r : Cx.Hom K L (RingHom.id R))
    (hs : ∀ j, Function.Surjective (r.f j)) (hk : ∀ j x, r.f j x = 0 ↔ ∃ y, x = c ^ n • y)
    (ht : ∀ j (x : K.X j), c • x = 0 → x = 0) (j : ℕ) (z : K.H j) (hz : r.mapH j z = 0) :
    ∃ y, z = c ^ n • y := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K j).1 z
  rw [mapH_cls' r a ha (cyc r a ha), (CrystallineSemistableComparison.P.cls_surj L j).2.1] at hz
  have hv : ∃ v : K.X j, v ∈ K.B j ∧ K.d j v = 0 ∧ r.f j (a - v) = 0 := by
    cases j with
    | zero =>
      refine ⟨0, (mem_boundaries_zero_iff _).2 rfl, map_zero _, ?_⟩
      rw [sub_zero]
      exact (mem_boundaries_zero_iff _).1 hz
    | succ j =>
      obtain ⟨b, hb⟩ := (mem_Bs _).1 hz
      obtain ⟨v, rfl⟩ := hs j b
      refine ⟨K.d j v, (mem_Bs _).2 ⟨v, rfl⟩, K.dd j v, ?_⟩
      rw [map_sub, ← r.comm, hb, sub_self]
  obtain ⟨v, hvB, hvd, h0⟩ := hv
  obtain ⟨y, hy⟩ := (hk j _).1 h0
  have hdy : K.d j y = 0 := by
    refine pow_tf ht n _ _ ?_
    rw [← map_smul, ← hy, map_sub, ha, hvd, sub_zero]
  refine ⟨K.cls y hdy, ?_⟩
  have hcy : K.d j (c ^ n • y) = 0 := by rw [map_smul, hdy, smul_zero]
  rw [← cls_smul _ _ hdy hcy, (CrystallineSemistableComparison.P.cls_surj K j).2.2.1 _ _ ha hcy, ← hy]
  simpa using hvB

theorem kill_H {K L : Cx.{1} R} (c : R) (n : ℕ) (r : Cx.Hom K L (RingHom.id R))
    (hs : ∀ j, Function.Surjective (r.f j)) (hk : ∀ j x, r.f j x = 0 ↔ ∃ y, x = c ^ n • y)
    (j : ℕ) (h : L.H j) : c ^ n • h = 0 := by
  obtain ⟨w, hw, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L j).1 h
  obtain ⟨a, rfl⟩ := hs j w
  have h0 : c ^ n • r.f j a = 0 := by
    rw [← map_smul]
    exact (hk j _).2 ⟨a, rfl⟩
  have hd : L.d j (c ^ n • r.f j a) = 0 := by rw [h0, map_zero]
  rw [← cls_smul _ _ hw hd, (CrystallineSemistableComparison.P.cls_surj L j).2.1, h0]
  exact zero_mem _

theorem lift_level {K L : Cx.{1} R} (c : R) (n k j : ℕ) (r : Cx.Hom K L (RingHom.id R))
    (hs : ∀ j, Function.Surjective (r.f j)) (hk : ∀ j x, r.f j x = 0 ↔ ∃ y, x = c ^ n • y)
    (ht : ∀ j (x : K.X j), c • x = 0 → x = 0)
    (hA : ∀ (x : K.H (j + 1)) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0) (x : L.H j) :
    ∃ y : K.H j, r.mapH j y = c ^ k • x := by
  obtain ⟨w, hw, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L j).1 x
  obtain ⟨a, rfl⟩ := hs j w
  have h1 : r.f (j + 1) (K.d j a) = 0 := by rw [← r.comm]; exact hw
  obtain ⟨b, hb⟩ := (hk (j + 1) _).1 h1
  have hdb : K.d (j + 1) b = 0 := by
    refine pow_tf ht n _ _ ?_
    rw [← map_smul, ← hb, K.dd]
  have hcb : K.d (j + 1) (c ^ n • b) = 0 := by rw [map_smul, hdb, smul_zero]
  have h2 : c ^ n • K.cls b hdb = 0 := by
    rw [← cls_smul _ _ hdb hcb, (CrystallineSemistableComparison.P.cls_surj K (j + 1)).2.1]
    exact (mem_Bs _).2 ⟨a, hb⟩
  have h3 := hA _ n h2
  have hkb : K.d (j + 1) (c ^ k • b) = 0 := by rw [map_smul, hdb, smul_zero]
  rw [← cls_smul _ _ hdb hkb, (CrystallineSemistableComparison.P.cls_surj K (j + 1)).2.1] at h3
  obtain ⟨e, he⟩ := (mem_Bs _).1 h3
  have hy : K.d j (c ^ k • a - c ^ n • e) = 0 := by
    rw [map_sub, map_smul, map_smul, he, hb, smul_smul, smul_smul, mul_comm, sub_self]
  have hr : r.f j (c ^ k • a - c ^ n • e) = c ^ k • r.f j a := by
    rw [map_sub, (hk j _).2 ⟨e, rfl⟩, sub_zero, map_smul]
  have hd : L.d j (c ^ k • r.f j a) = 0 := by rw [map_smul, hw, smul_zero]
  refine ⟨K.cls _ hy, ?_⟩
  rw [mapH_cls' r _ hy (cyc r _ hy), ← cls_smul _ _ hw hd]
  exact cls_congr hr _ _

theorem mapH_tr {K L M : Cx.{1} R} (r : Cx.Hom K L (RingHom.id R)) (r' : Cx.Hom K M (RingHom.id R))
    (t : Cx.Hom L M (RingHom.id R)) (j : ℕ) (h : ∀ x, t.f j (r.f j x) = r'.f j x) (z : K.H j) :
    t.mapH j (r.mapH j z) = r'.mapH j z := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K j).1 z
  rw [mapH_cls' r a ha (cyc r a ha), mapH_cls' t _ _ (cyc t _ (cyc r a ha)), mapH_cls' r' a ha (cyc r' a ha)]
  exact cls_congr (h a) _ _

theorem lim_lift : ∀ {R : Type} [CommRing R] {K : Cx.{1} R} (Kn : ℕ → Cx.{1} R) (c : R) (red : ∀ n, Cx.Hom K (Kn n) (RingHom.id R))
    (tr : ∀ n, Cx.Hom (Kn (n + 1)) (Kn n) (RingHom.id R)), (∀ n j x, (tr n).f j ((red (n + 1)).f j x) = (red n).f j x) →
    (∀ n j, Function.Surjective ((red n).f j)) → (∀ n j x, (red n).f j x = 0 ↔ ∃ y, x = c ^ n • y) → (∀ j (x : K.X j), c • x = 0 → x = 0) →
    ∀ j k : ℕ, (∀ (x : K.H (j + 1)) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0) → (∀ x : K.H j, (∀ n : ℕ, ∃ y, x = c ^ n • y) → c ^ k • x = 0) →
    (∀ x : ℕ → K.H j, (∀ n, ∃ y, x (n + 1) - x n = c ^ n • y) → ∃ z : K.H j, ∀ n, ∃ y, z - c ^ k • x n = c ^ n • y) →
    (∀ x : ∀ n, (Kn n).H j, (∀ n, (tr n).mapH j (x (n + 1)) = x n) → ∃ z : K.H j, ∀ n, (red n).mapH j z = c ^ (2 * k) • x n) ∧
    ∀ z : K.H j, (∀ n, (red n).mapH j z = 0) → c ^ k • z = 0 := by
  intro R _ K Kn c red tr hc hs hk ht j k hA hB hC
  refine ⟨fun x hx => ?_, fun z hz => hB z fun n => ker_red c n (red n) (hs n) (hk n) ht j z (hz n)⟩
  choose y hy using fun n => lift_level c n k j (red n) (hs n) (hk n) ht hA (x n)
  have hdiff : ∀ n, ∃ u, y (n + 1) - y n = c ^ n • u := by
    intro n
    refine ker_red c n (red n) (hs n) (hk n) ht j _ ?_
    rw [map_sub, ← mapH_tr (red (n + 1)) (red n) (tr n) j (hc n j), hy, hy, map_smul, hx, sub_self]
  obtain ⟨z, hz⟩ := hC y hdiff
  refine ⟨z, fun n => ?_⟩
  obtain ⟨u, hu⟩ := hz n
  have e : z = c ^ k • y n + c ^ n • u := by rw [← hu]; abel
  rw [e, map_add, map_smul, map_smul, hy, kill_H c n (red n) (hs n) (hk n), add_zero, smul_smul, ← pow_add, two_mul]

end GlobalTheory.CompanionTheory.LimLift
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverse_limit_cohomology_comparison : ∀ {R : Type} [CommRing R] {K : Cx.{1} R} (Kn : ℕ → Cx.{1} R) (c : R) (red : ∀ n, Cx.Hom K (Kn n) (RingHom.id R))
    (tr : ∀ n, Cx.Hom (Kn (n + 1)) (Kn n) (RingHom.id R)), (∀ n j x, (tr n).f j ((red (n + 1)).f j x) = (red n).f j x) →
    (∀ n j, Function.Surjective ((red n).f j)) → (∀ n j x, (red n).f j x = 0 ↔ ∃ y, x = c ^ n • y) → (∀ j (x : K.X j), c • x = 0 → x = 0) →
    ∀ j k : ℕ, (∀ (x : K.H (j + 1)) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0) → (∀ x : K.H j, (∀ n : ℕ, ∃ y, x = c ^ n • y) → c ^ k • x = 0) →
    (∀ x : ℕ → K.H j, (∀ n, ∃ y, x (n + 1) - x n = c ^ n • y) → ∃ z : K.H j, ∀ n, ∃ y, z - c ^ k • x n = c ^ n • y) →
    (∀ x : ∀ n, (Kn n).H j, (∀ n, (tr n).mapH j (x (n + 1)) = x n) → ∃ z : K.H j, ∀ n, (red n).mapH j z = c ^ (2 * k) • x n) ∧
    ∀ z : K.H j, (∀ n, (red n).mapH j z = 0) → c ^ k • z = 0 := by
  first | exact @GlobalTheory.CompanionTheory.LimLift.lim_lift | exact GlobalTheory.CompanionTheory.LimLift.lim_lift | (intros; apply GlobalTheory.CompanionTheory.LimLift.lim_lift <;> assumption)
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LiftLat

section Coch
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F : C ⥤ ModuleCat.{0} R} {G : ℕ → C ⥤ ModuleCat.{0} R}

theorem gen (c : R) (red : ∀ n, CH.Mor F (G n) (RingHom.id R)) (tr : ∀ n, CH.Mor (G (n + 1)) (G n) (RingHom.id R))
    (τ : ∀ n T, F.obj T →ₗ[R] (G n).obj T) (ρ : ∀ n T, (G (n + 1)).obj T →ₗ[R] (G n).obj T)
    (hred : ∀ n j (x : CH.Cn F j) s, (red n).hom.f j x s = τ n _ (x s))
    (htr : ∀ n j (x : CH.Cn (G (n + 1)) j) s, (tr n).hom.f j x s = ρ n _ (x s))
    (hcomp : ∀ n T x, ρ n T (τ (n + 1) T x) = τ n T x)
    (hsurj : ∀ n T, Function.Surjective (τ n T))
    (hker : ∀ n T x, τ n T x = 0 ↔ ∃ y, x = c ^ n • y)
    (htors : ∀ T (x : F.obj T), c • x = 0 → x = 0) (j k : ℕ)
    (h1 : ∀ (x : CH.H F (j + 1)) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0)
    (h2 : ∀ x : CH.H F j, (∀ n : ℕ, ∃ y, x = c ^ n • y) → c ^ k • x = 0)
    (h3 : ∀ x : ℕ → CH.H F j, (∀ n, ∃ y, x (n + 1) - x n = c ^ n • y) → ∃ z : CH.H F j, ∀ n, ∃ y, z - c ^ k • x n = c ^ n • y) :
    (∀ x : ∀ n, CH.H (G n) j, (∀ n, (tr n).pull j (x (n + 1)) = x n) →
      ∃ z : CH.H F j, ∀ n, (red n).pull j z = c ^ (2 * k) • x n) ∧
    ∀ z : CH.H F j, (∀ n, (red n).pull j z = 0) → c ^ k • z = 0 := by
  refine GlobalTheory.T.inverse_limit_cohomology_comparison (K := CH.cx F) (fun n => CH.cx (G n)) c (fun n => (red n).hom) (fun n => (tr n).hom)
    ?_ ?_ ?_ ?_ j k h1 h2 h3
  · intro n j x
    funext s
    rw [htr, hred, hred, hcomp]
  · intro n j y
    choose g hg using fun T => hsurj n T
    exact ⟨fun s => g _ (y s), funext fun s => (hred n j _ s).trans (hg _ _)⟩
  · intro n j x
    constructor
    · intro hx
      have : ∀ s, ∃ y, x s = c ^ n • y := fun s => (hker n _ _).1 ((hred n j x s).symm.trans (congrFun hx s))
      choose y hy using this
      exact ⟨y, funext hy⟩
    · rintro ⟨y, rfl⟩
      funext s
      exact (hred n j _ s).trans ((hker n _ _).2 ⟨_, rfl⟩)
  · intro j x hx
    exact funext fun s => htors _ _ (congrFun hx s)

end Coch

section Sq
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem sqMk_eq_zero (a b : IdF A) {T : C} (x : A.obj T) (hx : x ∈ a.S T) : sqMk a b x hx = 0 ↔ x ∈ b.S T := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact Subtype.ext_iff

theorem pull_sqLe_toSq {a b a' b' : IdF A} (ha : ∀ T, a.S T = ⊤) (ha' : ∀ T, a'.S T = ⊤) (hle : ∀ T, a.S T ≤ a'.S T)
    (hb : ∀ T, b.S T ≤ b'.S T) (j : ℕ) (z : CH.H (CH.modF A) j) :
    (sqLe hle hb).pull j ((toSq a b ha).pull j z) = (toSq a' b' ha').pull j z := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rfl

theorem gen_top (c : R) (b : ℕ → IdF A) (hb : ∀ n T, (b (n + 1)).S T ≤ (b n).S T)
    (hmem : ∀ n T (x : A.obj T), x ∈ (b n).S T ↔ ∃ y : A.obj T, x = c ^ n • y)
    (htors : ∀ T (x : A.obj T), c • x = 0 → x = 0) (j k : ℕ)
    (h1 : ∀ (x : CH.H (CH.modF A) (j + 1)) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0)
    (h2 : ∀ x : CH.H (CH.modF A) j, (∀ n : ℕ, ∃ y, x = c ^ n • y) → c ^ k • x = 0)
    (h3 : ∀ x : ℕ → CH.H (CH.modF A) j, (∀ n, ∃ y, x (n + 1) - x n = c ^ n • y) →
      ∃ z : CH.H (CH.modF A) j, ∀ n, ∃ y, z - c ^ k • x n = c ^ n • y) :
    (∀ x : ∀ n, CH.H (sq (IdF.top A) (b n)) j,
      (∀ n, (sqLe (fun _ => le_rfl) (hb n)).pull j (x (n + 1)) = x n) →
      ∃ z : CH.H (CH.modF A) j, ∀ n, (toSq (IdF.top A) (b n) fun _ => rfl).pull j z = c ^ (2 * k) • x n) ∧
    ∀ z : CH.H (CH.modF A) j, (∀ n, (toSq (IdF.top A) (b n) fun _ => rfl).pull j z = 0) → c ^ k • z = 0 := by
  refine gen (G := fun n => sq (IdF.top A) (b n)) c (fun n => toSq (IdF.top A) (b n) fun _ => rfl)
    (fun n => sqLe (fun _ => le_rfl) (hb n)) (fun n T => (toSq (IdF.top A) (b n) fun _ => rfl).τ T)
    (fun n T => (sqLe (fun _ => le_rfl) (hb n)).τ T) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) ?_ ?_ ?_ htors j k h1 h2 h3
  · intro n T x
    rfl
  · intro n T y
    obtain ⟨y, hy⟩ := y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨x, rfl⟩
  · intro n T x
    exact (sqMk_eq_zero (IdF.top A) (b n) (show A.obj T from x) trivial).trans (hmem n T x)

theorem gen_quo (c : R) (a₀ br : IdF A) (ha₀ : ∀ T, a₀.S T = ⊤) (b : ℕ → IdF A) (hle : ∀ n T, br.S T ≤ (b n).S T)
    (hb : ∀ n T, (b (n + 1)).S T ≤ (b n).S T)
    (hmem : ∀ n T (x : A.obj T), x ∈ (b n).S T ↔ ∃ y : A.obj T, x - c ^ n • y ∈ br.S T)
    (htors : ∀ T (x : A.obj T), c • x ∈ br.S T → x ∈ br.S T) (j k : ℕ)
    (h1 : ∀ (x : CH.H (sq a₀ br) (j + 1)) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0)
    (h2 : ∀ x : CH.H (sq a₀ br) j, (∀ n : ℕ, ∃ y, x = c ^ n • y) → c ^ k • x = 0)
    (h3 : ∀ x : ℕ → CH.H (sq a₀ br) j, (∀ n, ∃ y, x (n + 1) - x n = c ^ n • y) →
      ∃ z : CH.H (sq a₀ br) j, ∀ n, ∃ y, z - c ^ k • x n = c ^ n • y)
    (z : CH.H (sq a₀ br) j)
    (hz : ∀ n, (sqLe (a' := IdF.top A) (fun T => le_top) (hle n)).pull j z = 0) : c ^ k • z = 0 := by
  refine (gen (G := fun n => sq (IdF.top A) (b n)) c (fun n => sqLe (a' := IdF.top A) (fun T => le_top) (hle n))
    (fun n => sqLe (fun _ => le_rfl) (hb n)) (fun n T => (sqLe (a' := IdF.top A) (fun T => le_top) (hle n)).τ T)
    (fun n T => (sqLe (fun _ => le_rfl) (hb n)).τ T) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) ?_ ?_ ?_ ?_ j k h1 h2 h3).2 z hz
  · intro n T x
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  · intro n T y
    obtain ⟨y, hy⟩ := y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨sqMk a₀ br x (by rw [ha₀]; trivial), rfl⟩
  · intro n T x
    obtain ⟨x, hx⟩ := x
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    have e1 : (sqLe (a' := IdF.top A) (fun T => le_top) (hle n)).τ T ⟨Ideal.Quotient.mk _ w, hx⟩ = 0 ↔ w ∈ (b n).S T :=
      sqMk_eq_zero (IdF.top A) (b n) w trivial
    refine e1.trans ((hmem n T w).trans ⟨?_, ?_⟩)
    · rintro ⟨y, hy⟩
      refine ⟨sqMk a₀ br y (by rw [ha₀]; trivial), Subtype.ext ?_⟩
      exact Ideal.Quotient.eq.2 hy
    · rintro ⟨⟨y, hy⟩, h⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨y, Ideal.Quotient.eq.1 (congrArg Subtype.val h)⟩
  · intro T x hx
    obtain ⟨x, hx'⟩ := x
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    have e2 : (Ideal.Quotient.mk (br.S T) (c • w)) = 0 := congrArg Subtype.val hx
    have e3 := htors T w (Ideal.Quotient.eq_zero_iff_mem.1 e2)
    exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 e3)

theorem bij_toSq (a b : IdF A) (ha : ∀ T, a.S T = ⊤) (hb : ∀ T, b.S T = ⊥) (n : ℕ) :
    Function.Bijective ((toSq a b ha).hom.f n) := by
  constructor
  · intro f g hfg
    funext s
    have e : Ideal.Quotient.mk (b.S _) (show A.obj _ from f s) = Ideal.Quotient.mk (b.S _) (show A.obj _ from g s) :=
      congrArg Subtype.val (congrFun hfg s)
    have e' := Ideal.Quotient.eq.1 e
    rw [hb, Ideal.mem_bot] at e'
    exact sub_eq_zero.1 e'
  · intro g
    have : ∀ s : ComposableArrows C n, ∃ x : A.obj (s.obj (Fin.last n)), (toSq a b ha).τ _ x = g s := by
      intro s
      obtain ⟨y, hy⟩ := g s
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨x, rfl⟩
    choose f hf using this
    exact ⟨f, funext hf⟩
end Sq

section Fin
variable {R : Type} [CommRing R]

theorem afg_of_bij {M N : Type 1} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (c : R) (f : M →ₗ[R] N)
    (hf : Function.Bijective f) (h : AFG c N) : AFG c M := by
  obtain ⟨n, N₀, hN, hx⟩ := h
  let e := LinearEquiv.ofBijective f hf
  refine ⟨n, N₀.map e.symm.toLinearMap, hN.map _, fun x => ⟨c ^ n • e x, hx (e x), ?_⟩⟩
  simp

theorem dividedPowerFiltration_one_eq {J : Ideal R} (δ : DividedPowers J) : pdP δ 1 = J := by
  refine le_antisymm (DPFil.dividedPowerFiltration_one_le δ) fun x hx => ?_
  have h := DPFil.dpow_mem_pdP δ 1 hx
  rwa [δ.dpow_one hx] at h

theorem pow_le_pdP' {J : Ideal R} (δ : DividedPowers J) (r : ℕ) : J ^ r ≤ pdP δ r := by
  induction r with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, top_le_iff]
    exact (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨[], by simp, by simp, by simp⟩)
  | succ r ih =>
    rw [pow_succ]
    refine (Ideal.mul_mono ih ?_).trans (DPFil.dividedPowerFiltration_mul_le δ r 1)
    exact (dividedPowerFiltration_one_eq δ).ge

theorem bounds {I : Ideal R} {γ : DividedPowers I} {l m : ℕ} (h : LatBase γ l m) {M M' : Type 1} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (hM : AFG (l : R) M) (hM' : AFG (l : R) M') :
    ∃ k : ℕ, (∀ (x : M') (n : ℕ), (l : R) ^ n • x = 0 → (l : R) ^ k • x = 0) ∧
      (∀ x : M, (∀ n : ℕ, ∃ y, x = (l : R) ^ n • y) → (l : R) ^ k • x = 0) ∧
      ∀ x : ℕ → M, (∀ n, ∃ y, x (n + 1) - x n = (l : R) ^ n • y) → ∃ z : M, ∀ n, ∃ y, z - (l : R) ^ k • x n = (l : R) ^ n • y := by
  have hfg : I.FG := by
    have := h.fg 1
    rwa [dividedPowerFiltration_one_eq] at this
  have hnil : IsNilpotent I := ⟨m, by
    have := pow_le_pdP' γ m
    rw [h.tf.nil] at this
    exact le_bot_iff.1 this⟩
  have hcl : ∀ x : R, (∀ n : ℕ, x ∈ Ideal.span {(l : R) ^ n} ⊔ I) → x ∈ I := by
    have := h.closed 1
    rwa [dividedPowerFiltration_one_eq] at this
  have key := fun (N : Type 1) [AddCommGroup N] [Module R N] => GlobalTheory.T.almost_finite_module_bounded_torsion R I (l : R) hfg hnil h.prime h.val h.dv
    h.cpl.toIsPrecomplete hcl N
  obtain ⟨k₁, a₁, -, -⟩ := key M' hM'
  obtain ⟨k₂, -, b₂, c₂⟩ := key M hM
  refine ⟨k₁ + k₂, fun x n hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [pow_add, mul_comm, mul_smul, a₁ x n hx, smul_zero]
  · rw [pow_add, mul_smul, b₂ x hx, smul_zero]
  · obtain ⟨z, hz⟩ := c₂ x hx
    refine ⟨(l : R) ^ k₁ • z, fun n => ?_⟩
    obtain ⟨y, hy⟩ := hz n
    refine ⟨(l : R) ^ k₁ • y, ?_⟩
    rw [pow_add, mul_smul, ← smul_sub, hy, smul_comm]

end Fin

section Main
variable {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L))

theorem mem_none (c : b.R) (T : Q.FullSubcategory) (x : (sP Q).A.obj T) :
    x ∈ (stdI Q none c).S T ↔ ∃ y : (sP Q).A.obj T, x = c • y := by
  change x ∈ (⊥ : Ideal _) ⊔ Ideal.span {algebraMap b.R ((sP Q).A.obj T) c} ↔ _
  rw [bot_sup_eq, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [Algebra.smul_def, mul_comm]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [Algebra.smul_def, mul_comm]⟩

theorem top_part (c : b.R) (hT : ∀ (T : Q.FullSubcategory) (x : (sP Q).A.obj T), c • x = 0 → x = 0) (j k : ℕ)
    (h1 : ∀ (x : HO Q (j + 1)) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0)
    (h2 : ∀ x : HO Q j, (∀ n : ℕ, ∃ y, x = c ^ n • y) → c ^ k • x = 0)
    (h3 : ∀ x : ℕ → HO Q j, (∀ n, ∃ y, x (n + 1) - x n = c ^ n • y) → ∃ z : HO Q j, ∀ n, ∃ y, z - c ^ k • x n = c ^ n • y) :
    (∀ x : ∀ n, HM Q none (c ^ n) j, (∀ n, trM Q none c n j (x (n + 1)) = x n) →
      ∃ z : HO Q j, ∀ n, redM Q none (c ^ n) j z = c ^ (2 * k) • x n) ∧
    ∀ z : HO Q j, (∀ n, redM Q none (c ^ n) j z = 0) → c ^ k • z = 0 :=
  gen_top c (fun n => stdI Q none (c ^ n)) (stdI_le Q none c) (fun n T x => mem_none Q _ T x) hT j k h1 h2 h3

theorem mem_some (r : ℤ) (c : b.R) (T : Q.FullSubcategory) (x : (sP Q).A.obj T) :
    x ∈ (stdI Q (some r) c).S T ↔ ∃ y : (sP Q).A.obj T, x - c • y ∈ (sFil Q r).S T := by
  change x ∈ (sFil Q r).S T ⊔ Ideal.span {algebraMap b.R ((sP Q).A.obj T) c} ↔ _
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hv
    refine ⟨y, ?_⟩
    rw [Algebra.smul_def, mul_comm, add_sub_cancel_right]
    exact hu
  · rintro ⟨y, hy⟩
    refine ⟨_, hy, c • y, ?_, sub_add_cancel _ _⟩
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem quo_part (c : b.R) (r : ℤ)
    (hT : ∀ (T : Q.FullSubcategory) (x : (sP Q).A.obj T), c • x ∈ (sFil Q r).S T → x ∈ (sFil Q r).S T) (j k : ℕ)
    (h1 : ∀ (x : HQ Q 0 r (j + 1)) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0)
    (h2 : ∀ x : HQ Q 0 r j, (∀ n : ℕ, ∃ y, x = c ^ n • y) → c ^ k • x = 0)
    (h3 : ∀ x : ℕ → HQ Q 0 r j, (∀ n, ∃ y, x (n + 1) - x n = c ^ n • y) →
      ∃ z : HQ Q 0 r j, ∀ n, ∃ y, z - c ^ k • x n = c ^ n • y)
    (z : HO Q j) (hz : ∀ n, redM Q (some r) (c ^ n) j z = 0) : c ^ k • quoM Q r j z = 0 := by
  have hle : ∀ (n : ℕ) T, (sFil Q r).S T ≤ (stdI Q (some r) (c ^ n)).S T := fun n T => le_sup_left
  refine gen_quo c (sFil Q 0) (sFil Q r) (fun T => T.obj.pdPow_zero) (fun n => stdI Q (some r) (c ^ n)) hle
    (stdI_le Q (some r) c) (fun n T x => mem_some Q r _ T x) hT j k h1 h2 h3 _ fun n => ?_
  exact (pull_sqLe_toSq (fun T => T.obj.pdPow_zero) (fun _ => rfl) (fun T => le_top) (hle n) j z).trans (hz n)

theorem bij_quoM (s : ℤ) (h : ∀ T : Q.FullSubcategory, (sFil Q s).S T = ⊥) (j : ℕ) : Function.Bijective (quoM Q s j) :=
  P.mapH_bij _ (bij_toSq (sFil Q 0) (sFil Q s) (fun T => T.obj.pdPow_zero) h) j

theorem sub_HQ (r : ℤ) (h0 : r ≤ 0) (j : ℕ) : Subsingleton (HQ Q 0 r j) := by
  have h : ∀ T : Q.FullSubcategory, Subsingleton ((sq (sFil Q 0) (sFil Q r)).obj T) := fun T => by
    have e : (sFil Q r).S T = ⊤ := (GlobalTheory.CompanionTheory.DPFil.isFil_sFil Q).top r h0 T
    have : Subsingleton ((sP Q).A.obj T ⧸ (sFil Q r).S T) := Ideal.Quotient.subsingleton_iff.2 e
    exact ⟨fun x y => Subtype.ext (Subsingleton.elim (α := (sP Q).A.obj T ⧸ (sFil Q r).S T) _ _)⟩
  have h2 : Subsingleton (CH.Cn (sq (sFil Q 0) (sFil Q r)) j) := ⟨fun f g => funext fun s => (h _).elim _ _⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact congrArg _ (Subtype.ext (h2.elim _ _))

theorem liftingProperty_of_bounds (c : b.R) (s : ℕ) (hzero : ∀ T : Q.FullSubcategory, (sFil Q (s : ℤ)).S T = ⊥)
    (htf : ∀ (r : ℤ) (T : Q.FullSubcategory) (x : (sP Q).A.obj T), c • x ∈ (sFil Q r).S T → x ∈ (sFil Q r).S T)
    (hQ : ∀ t : ℕ, t ≤ s → ∀ j, AFG c (HQ Q 0 t j))
    (hb : ∀ (M M' : Type 1) [AddCommGroup M] [Module b.R M] [AddCommGroup M'] [Module b.R M'], AFG c M → AFG c M' →
      ∃ k : ℕ, (∀ (x : M') (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0) ∧
      (∀ x : M, (∀ n : ℕ, ∃ y, x = c ^ n • y) → c ^ k • x = 0) ∧
      ∀ x : ℕ → M, (∀ n, ∃ y, x (n + 1) - x n = c ^ n • y) → ∃ z : M, ∀ n, ∃ y, z - c ^ k • x n = c ^ n • y) (j : ℕ) :
    ∃ e : ℕ, LiftP Q c s j e := by
  have htop : ∀ (T : Q.FullSubcategory) (x : (sP Q).A.obj T), c • x = 0 → x = 0 := fun T x h => by
    have h' : x ∈ (sFil Q (s : ℤ)).S T := htf _ T x (by rw [h]; exact Ideal.zero_mem _)
    rw [hzero] at h'
    exact h'
  have hHO : ∀ j, AFG c (HO Q j) := fun j =>
    afg_of_bij _ (quoM Q s j) (bij_quoM Q _ hzero j) (hQ s le_rfl j)
  obtain ⟨k, a, b, d⟩ := hb _ _ (hHO j) (hHO (j + 1))
  obtain ⟨p1, p2⟩ := top_part Q c htop j k a b d
  have hr : ∀ t : ℕ, ∃ e : ℕ, t ≤ s → ∀ z : HO Q j,
      (∀ n, redM Q (some (t : ℤ)) (c ^ n) j z = 0) → c ^ e • quoM Q t j z = 0 := by
    intro t
    by_cases ht : t ≤ s
    · obtain ⟨e, a, b, d⟩ := hb _ _ (hQ t ht j) (hQ t ht (j + 1))
      exact ⟨e, fun _ z hz => quo_part Q c t (htf t) j e a b d z hz⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose f hf using hr
  refine ⟨2 * k + (Finset.range (s + 1)).sup f, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, hz⟩ := p1 x hx
    refine ⟨c ^ (Finset.range (s + 1)).sup f • z, fun n => ?_⟩
    rw [map_smul, hz, smul_smul, ← pow_add, Nat.add_comm ((Finset.range (s + 1)).sup f)]
  · intro z hz
    rw [show 2 * k + (Finset.range (s + 1)).sup f = (k + (Finset.range (s + 1)).sup f) + k by omega, pow_add, mul_smul,
      p2 z hz, smul_zero]
  · intro r hrs z hz
    by_cases h0 : r ≤ 0
    · have : Subsingleton (HQ Q 0 r j) := sub_HQ Q r h0 j
      exact Subsingleton.elim _ _
    · obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ r)
      have ht : t ≤ s := by omega
      have hle : f t ≤ (Finset.range (s + 1)).sup f := Finset.le_sup (Finset.mem_range.2 (by omega))
      obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hle
      rw [hu, show 2 * k + (f t + u) = (2 * k + u) + f t by omega, pow_add, mul_smul, hf t ht z hz, smul_zero]

end Main

theorem liftA_of_afgA : AfgA → LiftA := by
  intro hA O A _ _ _ _ _ I γ l s m hdv hO hL hms X q _ U 𝒱 h𝒱 j
  refine liftingProperty_of_bounds (TS γ q l s 𝒱) (l : A) s ?_ ?_ ?_ ?_ j
  · intro T
    change T.obj.pdPow (s : ℤ).toNat = ⊥
    rw [Int.toNat_natCast]
    exact T.property.1.1
  · intro r T x h
    have e : (l : A) • x = (l : T.obj.B) * (show T.obj.B from x) := by
      rw [Algebra.smul_def, map_natCast]
    rw [e] at h
    exact T.property.1.2 _ _ h
  · intro t ht j
    exact hA γ l s m hdv hO hL hms q U 𝒱 h𝒱 0 t (by omega) (by omega) j
  · intro M M' _ _ _ _ h h'
    exact bounds hL h h'

end GlobalTheory.CompanionTheory.LiftLat
end
