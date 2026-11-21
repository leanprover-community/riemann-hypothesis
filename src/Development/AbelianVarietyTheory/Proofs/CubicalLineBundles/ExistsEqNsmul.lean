import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUnitOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import BuildAid.ForwardExisting

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_torsion_fieldExt : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (k k' : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field k'] [IsAlgClosed k'] (j : k →+* k') (t : Sp k ⟶ S), ∃ r : (Over.mk t ⟶ P.A) →* (Over.mk (spMap j ≫ t) ⟶ P.A), (∀ x, (r x).left = spMap j ≫ x.left) ∧ Function.Injective r ∧ (∀ (n : ℕ) y, 0 < n → y ^ n = 1 → ∃ x, r x = y) ∧ ∀ (n : ℕ) x y (c : kˣ), 0 < n → x ^ n = 1 → y ^ n = 1 → (Out.WeilIs P.A P.L n x y (unitOn c) ↔ Out.WeilIs P.A P.L n (r x) (r y) (unitOn (Units.map j.toMonoidHom c))) := by
  intro hL S _ P k k' _ _ _ _ _ j t
  let h : Over.mk (spMap j ≫ t) ⟶ Over.mk t := Over.homMk (spMap j) rfl
  let r : (Over.mk t ⟶ P.A) →* (Over.mk (spMap j ≫ t) ⟶ P.A) :=
    { toFun := fun x => h ≫ x, map_one' := comp_one _, map_mul' := fun x y => comp_mul _ _ _ }
  have hr : Function.Injective r := by
    letI := j.toAlgebra
    haveI : Flat (spMap j) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact (inferInstance : Module.Flat k k')
    haveI : Surjective (spMap j) := ⟨fun p => ⟨(⊥ : PrimeSpectrum k'), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
    haveI : Epi h.left := Flat.epi_of_flat_of_surjective (spMap j)
    haveI : Epi h := Over.epi_of_epi_left _
    exact fun x y e => (cancel_epi h).1 e
  have hu : ∀ c : kˣ, Units.map h.left.appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map j.toMonoidHom c) :=
    fun c => Units.ext (congrArg (fun q => q.hom (c : k))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))).symm
  have up : ∀ (n : ℕ) x y (c : kˣ), Out.WeilIs P.A P.L n x y (unitOn c) →
      Out.WeilIs P.A P.L n (r x) (r y) (unitOn (Units.map j.toMonoidHom c)) := fun n x y c H =>
    hu c ▸ CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB h H
  refine ⟨r, fun _ => rfl, hr, fun n y hn hy => ?_, fun n x y c _ hx hy => ⟨up n x y c, fun H => ?_⟩⟩
  · have hk : (n : k) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hk' : (n : k') ≠ 0 := by rw [← map_natCast j]; exact (map_ne_zero j).2 hk
    have c₁ := (hL.mulN S P n hn).2.2.2.2 k t hk
    have c₂ := (hL.mulN S P n hn).2.2.2.2 k' (spMap j ≫ t) hk'
    let f : {x : Over.mk t ⟶ P.A // x ^ n = 1} → {x : Over.mk (spMap j ≫ t) ⟶ P.A // x ^ n = 1} :=
      fun x => ⟨r x.1, by rw [← map_pow, x.2, map_one]⟩
    have hf : Function.Injective f := fun a b e => Subtype.ext (hr (congrArg Subtype.val e))
    haveI : Finite {x : Over.mk (spMap j ≫ t) ⟶ P.A // x ^ n = 1} :=
      Nat.finite_of_card_ne_zero (by rw [c₂]; positivity)
    obtain ⟨x, hx⟩ := (hf.bijective_of_nat_card_le (by rw [c₁, c₂])).2 ⟨y, hy⟩
    exact ⟨x.1, congrArg Subtype.val hx⟩
  · obtain ⟨d, hd, -⟩ := (hL.weil S P n (Over.mk t)).1 x y hx hy
    let u : kˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom d
    have e : unitOn u = d := Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of k)) d.val)
    rw [← e] at hd
    have e₁ := ((hL.weil S P n (Over.mk (spMap j ≫ t))).1 (r x) (r y) (by rw [← map_pow, hx, map_one])
      (by rw [← map_pow, hy, map_one])).unique (up n x y u hd) H
    have e₂ : u = c := Units.ext (j.injective
      ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k')).inv).1 (congrArg Units.val e₁)))
    exact e₂ ▸ hd

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.exists_torsion_injective_weil_compatible : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (k k' : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field k'] [IsAlgClosed k'] (j : k →+* k') (t : Sp k ⟶ S), ∃ r : (Over.mk t ⟶ P.A) →* (Over.mk (spMap j ≫ t) ⟶ P.A), (∀ x, (r x).left = spMap j ≫ x.left) ∧ Function.Injective r ∧ (∀ (n : ℕ) y, 0 < n → y ^ n = 1 → ∃ x, r x = y) ∧ ∀ (n : ℕ) x y (c : kˣ), 0 < n → x ^ n = 1 → y ^ n = 1 → (Out.WeilIs P.A P.L n x y (unitOn c) ↔ Out.WeilIs P.A P.L n (r x) (r y) (unitOn (Units.map j.toMonoidHom c))) := by
  atlas_forward_decl GlobalTheory.exists_torsion_fieldExt
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem exists_algClosure_lift {K k : Type} [Field K] [Field k] [IsAlgClosed k] (β : K →+* k) :
    ∃ j : AlgebraicClosure K →+* k, j.comp (algebraMap K (AlgebraicClosure K)) = β := by
  letI : Algebra K k := β.toAlgebra
  let f : AlgebraicClosure K →ₐ[K] k := IsAlgClosed.lift
  exact ⟨f.toRingHom, RingHom.ext fun z => f.commutes z⟩

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

section Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}

def OnTors (e : ℕ → Q → Q → kˣ → Prop) (n : ℕ) (x y : Q) (c : kˣ) : Prop :=
  0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c

def tateIsoCongr {e e' : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e)
    (h : ∀ n x y c, 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e' n x y c) : TateIso D k Q act e' :=
  { I with
    isom := fun n hn a b =>
      h n _ _ _ hn ((I.onto n hn _).2 ⟨a, rfl⟩) ((I.onto n hn _).2 ⟨b, rfl⟩) (I.isom n hn a b) }

theorem onTors_iff {Ω Q' : Type} [Field Ω] [Group Q'] (i : k →+* Ω) (r : Q →* Q') (hr : Function.Injective r)
    {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → Ωˣ → Prop}
    (h : ∀ (n : ℕ) x y (c : kˣ), 0 < n → x ^ n = 1 → y ^ n = 1 →
      (e n x y c ↔ e' n (r x) (r y) (Units.map i.toMonoidHom c))) (n : ℕ) (x y : Q) (c : kˣ) :
    OnTors e' n (r x) (r y) (Units.map i.toMonoidHom c) ↔ OnTors e n x y c := by
  unfold OnTors
  rw [← map_pow, ← map_pow, map_eq_one_iff r hr, map_eq_one_iff r hr]
  exact forall₃_congr fun hn hx hy => (h n x y c hn hx hy).symm

theorem onto_tors {Q' : Type} [Group Q'] (r : Q →* Q') (hr : Function.Injective r)
    (h : ∀ (n : ℕ) y, 0 < n → y ^ n = 1 → ∃ x, r x = y) (n : ℕ) (hn : 0 < n) (z : Q') (hz : z ^ n = 1) :
    ∃ y : Q, y ^ n = 1 ∧ r y = z := by
  obtain ⟨x, rfl⟩ := h n z hn hz
  exact ⟨x, by rwa [← map_pow, map_eq_one_iff r hr] at hz, rfl⟩

end Abstract

theorem cmTorsionIsometry_transport_geometricPoint (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (D : Datum H) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) (act : 𝓞 E → (P.A ⟶ P.A))
    (hm : ∀ c, IsMonHom (act c))
    {F Ω k : Type} [Field F] [Field Ω] [Field k] [IsAlgClosed F] [IsAlgClosed Ω] [IsAlgClosed k] [CharZero F]
    (i : F →+* Ω) (j : F →+* k) (x : Sp F ⟶ S) (y : Sp Ω ⟶ S) (z : Sp k ⟶ S)
    (hy : spMap i ≫ x = y) (hz : spMap j ≫ x = z)
    (I : TateIso D Ω (Over.mk y ⟶ P.A) (fun c y => y ≫ act c)
      (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c))) :
    ∃ I' : TateIso D k (Over.mk z ⟶ P.A) (fun c y => y ≫ act c)
      (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)),
      (∀ (n : ℕ) (u : F), 0 < n → (I.ζ n : Ω) = i u → (I'.ζ n : k) = j u) ∧
      ∀ (n : ℕ) a (s : 𝟙_ (Over S) ⟶ P.A), 0 < n → toUnit _ ≫ s = I.ev n a → toUnit _ ≫ s = I'.ev n a := by
  subst hy hz
  have key : ∀ (k' : Type) [Field k'] (l : F →+* k') (r : (Over.mk x ⟶ P.A) →* (Over.mk (spMap l ≫ x) ⟶ P.A)),
      (∀ y, (r y).left = spMap l ≫ y.left) →
      (∀ c y, r (y ≫ act c) = r y ≫ act c) ∧ ∀ s : 𝟙_ (Over S) ⟶ P.A, r (toUnit _ ≫ s) = toUnit _ ≫ s := by
    intro k' _ l r hr
    have h : ∀ y, r y = (Over.homMk (spMap l) rfl : Over.mk (spMap l ≫ x) ⟶ Over.mk x) ≫ y :=
      fun y => Over.OverMorphism.ext (hr y)
    exact ⟨fun c y => by rw [h, h, Category.assoc], fun s => by rw [h, ← Category.assoc, comp_toUnit]⟩
  obtain ⟨r, hr, rinj, ronto, rw'⟩ := GlobalTheory.T.exists_torsion_injective_weil_compatible hL S P F Ω i x
  obtain ⟨q, hq, qinj, qonto, qw⟩ := GlobalTheory.T.exists_torsion_injective_weil_compatible hL S P F k j x
  obtain ⟨I₀, h₀⟩ := TateIsoFieldExt.down D i r (act := fun c y => y ≫ act c)
    (e := OnTors fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)) rinj (onto_tors r rinj ronto)
    (key Ω i r hr).1 (fun c => by haveI := hm c; exact MonObj.one_comp (act c))
    (onTors_iff i r rinj rw') (tateIsoCongr I fun _ _ _ _ _ _ _ h _ _ _ => h)
  obtain ⟨I', h'⟩ := TateIsoFieldExt.up D j q (act' := fun c y => y ≫ act c)
    (e' := OnTors fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)) qinj (onto_tors q qinj qonto)
    (key k j q hq).1 (onTors_iff j q qinj qw) I₀
  refine ⟨tateIsoCongr I' fun _ _ _ _ hn hx hy h => h hn hx hy, fun n u hn hu => ?_, fun n a s hn hs => ?_⟩
  · have h1 : i (I₀.ζ n) = i u := (h₀ n hn).1.symm.trans hu
    exact (h' n hn).1.trans (congrArg j (i.injective h1))
  · have h1 : toUnit _ ≫ s = I₀.ev n a :=
      rinj (((key Ω i r hr).2 s).trans (hs.trans ((h₀ n hn).2 a)))
    exact ((key k j q hq).2 s).symm.trans ((congrArg q h1).trans ((h' n hn).2 a).symm)

theorem tateIso_move : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T : PAT H (Sp K)) (I : TateIso D ℂ (Over.mk (spMap σ) ⟶ T.t.G) (fun a x => x ≫ T.t.act.act a) (fun n x x' c => Out.WeilIs T.t.G T.t.PP.L n x x' (unitOn c))) (k : Type) [Field k] [IsAlgClosed k] (β : K →+* k), ∃ I' : TateIso D k (Over.mk (spMap β) ⟶ T.t.G) (fun a x => x ≫ T.t.act.act a) (fun n x x' c => Out.WeilIs T.t.G T.t.PP.L n x x' (unitOn c)), (∀ (n : ℕ) (z : K), 0 < n → (I.ζ n : ℂ) = σ z → (I'.ζ n : k) = β z) ∧ ∀ (n : ℕ) a (s : 𝟙_ (Over (Sp K)) ⟶ T.t.G), 0 < n → toUnit _ ≫ s = I.ev n a → toUnit _ ≫ s = I'.ev n a := by
  intro hL E _ _ _ H D K _ _ σ T I k _ _ β
  obtain ⟨i, hi⟩ := exists_algClosure_lift σ
  obtain ⟨j, hj⟩ := exists_algClosure_lift β
  obtain ⟨I', h1, h2⟩ := cmTorsionIsometry_transport_geometricPoint hL D T.pol (fun a => T.t.act.act a) T.t.act.hom i j
    (spMap (algebraMap K (AlgebraicClosure K))) (spMap σ) (spMap β)
    (by rw [← spMap_comp_eq, hi]) (by rw [← spMap_comp_eq, hj]) I
  refine ⟨I', fun n z hn hz => ?_, h2⟩
  rw [h1 n (algebraMap K _ z) hn (by rw [hz, ← hi]; rfl), ← hj]; rfl

end GlobalTheory.CM
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_iso_exists_alg_closed : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T : PAT H (Sp K)) (I : TateIso D ℂ (Over.mk (spMap σ) ⟶ T.t.G) (fun a x => x ≫ T.t.act.act a) (fun n x x' c => Out.WeilIs T.t.G T.t.PP.L n x x' (unitOn c))) (k : Type) [Field k] [IsAlgClosed k] (β : K →+* k), ∃ I' : TateIso D k (Over.mk (spMap β) ⟶ T.t.G) (fun a x => x ≫ T.t.act.act a) (fun n x x' c => Out.WeilIs T.t.G T.t.PP.L n x x' (unitOn c)), (∀ (n : ℕ) (z : K), 0 < n → (I.ζ n : ℂ) = σ z → (I'.ζ n : k) = β z) ∧ ∀ (n : ℕ) a (s : 𝟙_ (Over (Sp K)) ⟶ T.t.G), 0 < n → toUnit _ ≫ s = I.ev n a → toUnit _ ≫ s = I'.ev n a := by
  first | exact @GlobalTheory.CM.tateIso_move | exact GlobalTheory.CM.tateIso_move | (intros; apply GlobalTheory.CM.tateIso_move <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.RationalTorsion

theorem section_ext {K k : Type} [Field K] [Field k] (t : Sp k ⟶ Sp K) {G : Over (Sp K)}
    {s s' : 𝟙_ (Over (Sp K)) ⟶ G} (h : toUnit (Over.mk t) ≫ s = toUnit (Over.mk t) ≫ s') : s = s' := by
  have h1 : Surjective t := ⟨fun x => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩
  have h2 : Flat t := inferInstance
  have h3 : Epi t := Flat.epi_of_flat_of_surjective t
  have h4 : (toUnit (Over.mk t)).left = t := by simp
  have h5 : Epi (toUnit (Over.mk t)).left := by rw [h4]; exact h3
  have h6 : Epi (toUnit (Over.mk t)) := Over.epi_of_epi_left _
  exact (cancel_epi _).1 h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem ev_add_smul {D : Datum H} {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a c : D.La) :
    I.ev n (a + n • c) = I.ev n a := by
  rw [I.add, (I.ker n hn _).2 ⟨c, rfl⟩, _root_.mul_one]

theorem exists_eq_nsmul (D : Datum H) (l : Level H) {J J' : Ideal (𝓞 E)}
    (hJ : J * J' = Ideal.span {(l.M : 𝓞 E)}) {e : 𝓞 E} (he : e ∈ J) {a : D.La}
    (ha : a ∈ J' • (⊤ : Submodule (𝓞 E) D.La)) : ∃ c, e • a = l.M • c := by
  have h1 : e • a ∈ (J * J') • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul he ha
  rw [hJ, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨c, -, hc⟩ := h1
  exact ⟨c, by rw [← hc, Nat.cast_smul_eq_nsmul]⟩

theorem exists_obj : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (K : Type) [Field K] [NumberField K] (j : B →+* K) (σ : K →+* ℂ) (T : PAT H (Sp K)) (I : TateIso D ℂ (Over.mk (spMap σ) ⟶ T.t.G) (fun a x => x ≫ T.t.act.act a) (fun n x x' c => Out.WeilIs T.t.G T.t.PP.L n x x' (unitOn c))), HasType H T.t.act (j b.ρ) D.p D.q → (I.ζ l.A : ℂ) = σ (j b.ζ) → (∀ x : Over.mk (spMap σ) ⟶ T.t.G, x ^ l.M' = 1 → ∃ s : 𝟙_ (Over (Sp K)) ⟶ T.t.G, toUnit _ ≫ s = x) → ∃ o : Obj D l b (spMap j), o.t = T.t := by
  intro laws E _ _ _ H D l B _ b K _ _ j σ T I hty hζ hrat
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hA : 0 < l.A := l.A_pos
  have hsec : ∀ n : ℕ, 0 < n → n ∣ l.M' → ∀ a, ∃ s : 𝟙_ (Over (Sp K)) ⟶ T.t.G, toUnit _ ≫ s = I.ev n a := by
    rintro n hn ⟨m, hm⟩ a
    apply hrat
    rw [hm, pow_mul, (I.onto n hn _).2 ⟨a, rfl⟩, one_pow]
  choose sA hsA using hsec l.A hA (Nat.dvd_lcm_right _ _)
  choose sM hsM using hsec l.M hM (Nat.dvd_lcm_left _ _)
  obtain ⟨f, hf, e, he, hfe⟩ : ∃ f ∈ l.Mb, ∃ e ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), f + e = 1 :=
    Submodule.mem_sup.1 (by rw [l.coprime]; trivial)
  refine ⟨{
    t := T.t
    proper := T.ab.proper
    ample := T.ample
    ktriv := T.ktriv
    eta := fun a => sM (e • a)
    eta_add := fun a c => section_ext (spMap σ) (by
      rw [MonObj.comp_mul, hsM, hsM, hsM, smul_add, I.add])
    eta_ker := fun a ha => section_ext (spMap σ) (by
      obtain ⟨c, hc⟩ := exists_eq_nsmul D l (by rw [mul_comm]; exact l.prod) he ha
      rw [MonObj.comp_one, hsM]
      exact (I.ker _ hM _).2 ⟨c, hc⟩)
    etaA := sA
    etaA_add := fun a c => section_ext (spMap σ) (by
      rw [MonObj.comp_mul, hsA, hsA, hsA, I.add])
    etaA_ker := fun a => section_ext (spMap σ) (by
      rw [MonObj.comp_one, hsA]
      exact (I.ker _ hA _).2 ⟨a, rfl⟩)
    geom := ?_ }, rfl⟩
  intro k _ _ x β hx
  obtain ⟨ν, rfl⟩ : ∃ ν : K →+* k, x = spMap ν := ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩
  have hβ : β = ν.comp j := by
    have h1 : spMap (ν.comp j) = spMap β := by
      rw [← hx, ← Spec.map_comp]; rfl
    have h2 := Spec.map_injective h1
    exact (congrArg CommRingCat.Hom.hom h2).symm
  subst hβ
  refine ⟨hty k ν ν.injective, ?_⟩
  obtain ⟨I', hζ', hev⟩ := GlobalTheory.T.tate_iso_exists_alg_closed laws E H D K σ T I k ν
  refine ⟨I', hζ' _ _ hA hζ, fun a => hev _ a _ hA (hsA a), fun a ha => ?_⟩
  obtain ⟨c, hc⟩ := exists_eq_nsmul D l l.prod hf ha
  have h1 : a = e • a + l.M • c := by rw [← hc, ← add_smul, add_comm, hfe, one_smul]
  rw [hev _ (e • a) _ hM (hsM _)]
  conv_rhs => rw [h1]
  exact (ev_add_smul I' hM _ _).symm

end GlobalTheory.CM.RationalTorsion
end
end
