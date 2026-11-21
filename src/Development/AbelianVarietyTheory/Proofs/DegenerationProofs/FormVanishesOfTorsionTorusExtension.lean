import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CoeffSymmSum
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPartPartSec
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisUniqueMinAndSumsSeparated
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPointTranslatePure
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FinsuppEqZeroOfSumTorsionCharactersEqZero
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PureWeightSectionToTwistedPolarisationPower
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowEqTorus
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionZerosTwistLe
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.FormSec
open scoped Pointwise

theorem map_form {B B' J : Type} [CommRing B] [CommRing B'] (ψ : B →+* B') (T : Finset (J →₀ ℕ))
    (c : (J →₀ ℕ) → B) (s : J → B) :
    ψ (∑ m ∈ T, c m * m.prod (fun i n => s i ^ n)) =
      ∑ m ∈ T, ψ (c m) * m.prod (fun i n => ψ (s i) ^ n) := by
  simp only [map_sum, map_mul, Finsupp.prod, map_prod, map_pow]

theorem form_scale {B J : Type} [CommRing B] (T : Finset (J →₀ ℕ)) (d : ℕ)
    (hT : ∀ m ∈ T, ∑ i ∈ m.support, m i = d) (c : (J →₀ ℕ) → B) (u : B) (s : J → B) :
    ∑ m ∈ T, c m * m.prod (fun i n => (u * s i) ^ n) =
      u ^ d * ∑ m ∈ T, c m * m.prod (fun i n => s i ^ n) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hT m hm]
  ring

section Supp
variable {A X : Type} [CommRing A] [AddCommGroup X]

theorem supp_mul {x y : AddMonoidAlgebra A X} {S S' : Set X} (hx : (x.coeff.support : Set X) ⊆ S)
    (hy : (y.coeff.support : Set X) ⊆ S') : ((x * y).coeff.support : Set X) ⊆ S + S' := by
  classical
  intro a ha
  obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset x y ha)
  exact Set.add_mem_add (hx hb) (hy hc)

theorem supp_one : ((1 : AddMonoidAlgebra A X).coeff.support : Set X) ⊆ 0 := by
  intro a ha
  have := AddMonoidAlgebra.support_coeff_one_subset (k := A) (G := X) ha
  simpa using this

theorem supp_pow {x : AddMonoidAlgebra A X} {S : Set X} (hx : (x.coeff.support : Set X) ⊆ S) (n : ℕ) :
    ((x ^ n).coeff.support : Set X) ⊆ n • S := by
  induction n with
  | zero => rw [pow_zero, zero_nsmul]; exact supp_one
  | succ n ih => rw [pow_succ, succ_nsmul]; exact supp_mul ih hx

theorem supp_prod {J : Type} {x : J → AddMonoidAlgebra A X} {S : Set X}
    (hx : ∀ i, ((x i).coeff.support : Set X) ⊆ S) (n : J → ℕ) (t : Finset J) :
    ((∏ i ∈ t, x i ^ n i).coeff.support : Set X) ⊆ (∑ i ∈ t, n i) • S := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, zero_nsmul]; exact supp_one
  | insert j t hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, add_nsmul]
    exact supp_mul (supp_pow (hx j) _) ih

theorem supp_form {B J : Type} [CommRing B] (f : A →+* B)
    (g : Multiplicative X →* B) (hc : ∀ x y, Commute (f x) (g y))
    (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f g hc)) (T : Finset (J →₀ ℕ)) (d : ℕ)
    (hT : ∀ m ∈ T, ∑ i ∈ m.support, m i = d) (c : (J →₀ ℕ) → A) (s : J → B) (S : Set X)
    (hs : ∀ i α, ((Equiv.ofBijective _ hb).symm (s i)).coeff α ≠ 0 → α ∈ S) (α : X)
    (hα : ((Equiv.ofBijective _ hb).symm (∑ m ∈ T, f (c m) * m.prod (fun i n => s i ^ n))).coeff α ≠ 0) :
    ∃ β : Fin d → X, (∀ n, β n ∈ S) ∧ α = ∑ n, β n := by
  let e := RingEquiv.ofBijective _ hb
  have h1 : ∀ x, e.symm (f x) = AddMonoidAlgebra.single 0 x := fun x => by
    rw [RingEquiv.symm_apply_eq]
    change _ = AddMonoidAlgebra.liftNCRingHom f g hc _
    simp [AddMonoidAlgebra.liftNCRingHom]
  change (e.symm.toRingHom _).coeff α ≠ 0 at hα
  rw [map_form, AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply] at hα
  obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hα
  have h2 : ((e.symm.toRingHom (f (c m))).coeff.support : Set X) ⊆ 0 := by
    change ((e.symm (f (c m))).coeff.support : Set X) ⊆ 0
    rw [h1, AddMonoidAlgebra.coeff_single]
    intro a ha
    simpa using Finsupp.support_single_subset ha
  have h3 := supp_mul h2 (supp_prod (x := fun i => e.symm.toRingHom (s i)) (S := S)
    (fun i a ha => hs i a (Finsupp.mem_support_iff.1 ha)) m m.support) (Finsupp.mem_support_iff.2 hne)
  rw [zero_add, hT m hm, Set.mem_nsmul] at h3
  obtain ⟨β, hβ⟩ := h3
  exact ⟨fun n => β n, fun n => (β n).2, by rw [← hβ, List.sum_ofFn]⟩

end Supp

theorem res_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U)
    (a : R) : resG X h (constFn q U a) = constFn q V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map q (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem valHom_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (x : Sp R ⟶ X)
    (hx : x ≫ p = 𝟙 _) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : R) :
    CrdCalc.valHom x U h (constFn p U a) = a := by
  have e : p.appLE ⊤ U (fun _ _ => trivial) ≫ x.appLE U ⊤ h = 𝟙 _ := by
    refine (Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ (fun _ _ => trivial) h).trans ?_
    generalize_proofs h₁
    revert h₁
    rw [hx]
    intro h₁
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
    exact (Category.id_comp _).trans ((Sp R).presheaf.map_id _)
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (p.appLE ⊤ U (fun _ _ => trivial) ≫ x.appLE U ⊤ h) ≫
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom a = a
  rw [e, Category.id_comp, Iso.inv_hom_id]
  rfl

theorem deg_of_mem {k J : Type} [Field k] {d : ℕ} {Pf : MvPolynomial J k} (h : Pf.IsHomogeneous d) :
    ∀ m ∈ Pf.support, ∑ i ∈ m.support, m i = d := fun m hm => by
  have := h (MvPolynomial.mem_support_iff.1 hm)
  simpa [Finsupp.weight_apply, Finsupp.sum] using this

def formSec {k : Type} [Field k] (Φ : FibPre k) {J : Type} (F : J → (Φ.H 1).Sec) {d : ℕ}
    (Pf : MvPolynomial J k) (h : Pf.IsHomogeneous d) : (Φ.H d).Sec where
  f l := ∑ m ∈ Pf.support, constFn Φ.G.hom ((Φ.H d).U l) (Pf.coeff m) *
    m.prod (fun i n => (show Γ(Φ.G.left, (Φ.H d).U l) from (F i).f l) ^ n)
  compat l l' := by
    let V : Φ.G.left.Opens := (Φ.H d).U l ⊓ (Φ.H d).U l'
    let r : Γ(Φ.G.left, (Φ.H d).U l) →+* Γ(Φ.G.left, V) := resG _ inf_le_left
    let r' : Γ(Φ.G.left, (Φ.H d).U l') →+* Γ(Φ.G.left, V) := resG _ inf_le_right
    let u : Γ(Φ.G.left, V)ˣ := pullU Φ.D.q.left (Φ.N₀.U l ⊓ Φ.N₀.U l') (Φ.N₀.g l l')
    have hF : ∀ i, r ((F i).f l) = (u : Γ(Φ.G.left, V)) * r' ((F i).f l') := fun i => by
      have := (F i).compat l l'
      change r ((F i).f l) = ((u ^ 1 : Γ(Φ.G.left, V)ˣ) : Γ(Φ.G.left, V)) * r' ((F i).f l') at this
      exact this.trans (congrArg (fun w : Γ(Φ.G.left, V)ˣ => (w : Γ(Φ.G.left, V)) * r' ((F i).f l')) (pow_one u))
    change r _ = ((u ^ d : Γ(Φ.G.left, V)ˣ) : Γ(Φ.G.left, V)) * r' _
    rw [map_form, map_form, Units.val_pow_eq_pow_val, ← form_scale _ d (deg_of_mem h)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [res_constFn, res_constFn]
    congr 2
    funext i n
    exact congrArg (· ^ n) (hF i)

theorem exists_formSec : (∀ (k : Type) [Field k] (Φ : FibPre k) (J : Type) (F : J → (Φ.H 1).Sec) (d : ℕ) (Pf : MvPolynomial J k), Pf.IsHomogeneous d → ∃ φ : (Φ.H d).Sec, (∀ l, φ.f l = ∑ m ∈ Pf.support, constFn Φ.G.hom ((Φ.H d).U l) (Pf.coeff m) * m.prod (fun i n => (show Γ(Φ.G.left, (Φ.H d).U l) from (F i).f l) ^ n)) ∧ (∀ α ∈ Φ.supp φ, ∃ β : Fin d → Φ.E.X, (∀ n, ∃ i, β n ∈ Φ.supp (F i)) ∧ α = ∑ n, β n) ∧ ∀ (x : Φ.Pt) (v : J → k), Crd (Φ.H 1) F x.left v → (MvPolynomial.eval v Pf = 0 ↔ ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ)) := by
  intro k _ Φ J F d Pf h
  refine ⟨formSec Φ F Pf h, fun _ => rfl, ?_, ?_⟩
  · rintro α ⟨l, hl⟩
    refine supp_form _ _ _ (Φ.D.coord (Φ.ch l) _ (Φ.aff l) (Φ.le l)) Pf.support d (deg_of_mem h)
      (fun m => constFn Φ.E.B.hom _ (Pf.coeff m)) (fun i => (F i).f l) {β | ∃ i, β ∈ Φ.supp (F i)}
      (fun i β hβ => ⟨i, l, hβ⟩) α ?_
    simp only [WtLin.app_constFn _ _ _ (Over.w Φ.D.q)]
    exact hl
  · rintro x v ⟨l, c, hl, hv⟩
    have hl' : ⊤ ≤ x.left ⁻¹ᵁ (Φ.H d).U l := hl
    have hc : Crd (Φ.H d) (fun _ : Unit => formSec Φ F Pf h) x.left (fun _ => MvPolynomial.eval v Pf) := by
      refine ⟨l, c ^ d, hl', fun _ => ?_⟩
      rw [CrdCalc.valR_eq _ _ hl']
      change _ = _ * CrdCalc.valHom x.left _ hl' (∑ m ∈ Pf.support, _)
      rw [map_form, Units.val_pow_eq_pow_val, ← form_scale _ d (deg_of_mem h), MvPolynomial.eval_eq]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [valHom_constFn _ _ (Over.w x)]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hv i, CrdCalc.valR_eq _ _ hl]
      rfl
    rw [← CrdCalc.crd_isUnit_iff () hc, isUnit_iff_ne_zero, not_not]

end GlobalTheory.ZH.FormSec
end
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.TorsionFourier

section Val
variable {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X} {U : X.Opens}

theorem valF_sum (h : ⊤ ≤ x ⁻¹ᵁ U) {J : Type} (A : Finset J) (a : J → Γ(X, U)) :
    valF x U (∑ j ∈ A, a j) = ∑ j ∈ A, valF x U (a j) := by
  simp only [valF, dif_pos h, map_sum]

theorem valF_ne_zero_iff_le (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) :
    valF x U a ≠ 0 ↔ ⊤ ≤ x ⁻¹ᵁ X.basicOpen a := by
  have e1 := Scheme.basicOpen_appLE x ⊤ U h a
  rw [top_inf_eq] at e1
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a) = (x.appLE U ⊤ h).hom a := by
    rw [valF, dif_pos h]
    exact (Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply _
  have e3 : x ⁻¹ᵁ X.basicOpen a =
      (Sp F).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a)) := by
    rw [e2]; exact e1.symm
  rw [e3]
  constructor
  · intro hne
    exact (Scheme.basicOpen_of_isUnit _ ((Ne.isUnit hne).map _)).ge
  · intro hle h0
    rw [h0, map_zero, Scheme.basicOpen_zero] at hle
    exact hle (show (IsLocalRing.closedPoint F : Sp F) ∈ (⊤ : (Sp F).Opens) from trivial)

theorem le_nonzeroLocus_iff {H : LB X} (s : H.Sec) (x : Sp F ⟶ X) :
    ⊤ ≤ x ⁻¹ᵁ Out.nonzeroLocus s ↔ ∃ l, ⊤ ≤ x ⁻¹ᵁ H.U l ∧ valF x (H.U l) (s.f l) ≠ 0 := by
  constructor
  · intro h
    have hp : x (IsLocalRing.closedPoint F) ∈ Out.nonzeroLocus s :=
      h (show (IsLocalRing.closedPoint F : Sp F) ∈ (⊤ : (Sp F).Opens) from trivial)
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
    have h1 : ⊤ ≤ x ⁻¹ᵁ X.basicOpen (s.f l) := by
      intro y _
      have : y = IsLocalRing.closedPoint F := Subsingleton.elim (α := PrimeSpectrum F) _ _
      subst this
      exact hl
    have h2 : ⊤ ≤ x ⁻¹ᵁ H.U l := h1.trans (Scheme.Hom.preimage_mono x (X.basicOpen_le _))
    exact ⟨l, h2, (valF_ne_zero_iff_le h2 _).2 h1⟩
  · rintro ⟨l, h2, hne⟩
    exact ((valF_ne_zero_iff_le h2 _).1 hne).trans
      (Scheme.Hom.preimage_mono x (le_iSup (fun k => X.basicOpen (s.f k)) l))

end Val

theorem part_vanishes_on_torsion : (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (d n : ℕ), (n : k) ≠ 0 → ∀ φ : (Φ.H d).Sec, (∀ α ∈ Φ.supp φ, ∀ β ∈ Φ.supp φ, (∃ w, α = β + n • w) → α = β) → (∀ x : Φ.Pt, x ^ n = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ) → ∀ α ψ, Φ.IsPart α φ ψ → ∀ x : Φ.Pt, x ^ n = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus ψ) := by
  intro k _ _ Φ d n hn φ hinc hφ α ψ hψ x hx hle
  classical
  obtain ⟨hex, hfin, hext, hsum⟩ := GlobalTheory.ZH.WtPart.weight_parts k Φ d
  obtain ⟨l, hl, hne⟩ := (le_nonzeroLocus_iff (F := k) ψ x.left).1 hle
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn Nat.cast_zero
  have : NeZero (n : k) := ⟨hn⟩
  have : NeZero n := ⟨hn0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k n

  have hα : α ∈ Φ.supp φ := by
    by_contra hα
    apply hne
    have h0 : ψ.f l = ∑ β ∈ (∅ : Finset Φ.E.X), ((fun _ => ψ) β).f l := by
      refine hsum ψ ∅ (fun _ => ψ) ?_ (fun β hβ => absurd hβ (Finset.notMem_empty β)) l
      rintro β ⟨l', hl'⟩
      have e : β = α := hψ.1 ⟨l', hl'⟩
      subst e
      exact absurd ⟨l', by rwa [← hψ.2 l']⟩ hα
    refine (congrArg (valF (F := k) x.left _) h0).trans ((valF_sum (F := k) hl _ _).trans ?_)
    exact Finset.sum_empty
  choose p hp using hex φ
  let p' : Φ.E.X → (Φ.H d).Sec := fun β => if β = α then ψ else p β
  have hp' : ∀ β, Φ.IsPart β φ (p' β) := fun β => by
    by_cases h : β = α
    · subst h
      simpa only [p', if_pos rfl] using hψ
    · simpa only [p', if_neg h] using hp β
  let A : Finset Φ.E.X := (hfin φ).toFinset
  have hA : ∀ β, β ∈ A ↔ β ∈ Φ.supp φ := fun β => (hfin φ).mem_toFinset
  let v : Φ.E.X → k := fun β => valF (F := k) x.left ((Φ.H d).U l) ((p' β).f l)
  let c : Φ.E.X →₀ k := Finsupp.indicator A fun β _ => v β
  have hcs : c.support ⊆ A := Finsupp.support_indicator_subset _ _
  have hc : c = 0 := by
    refine GlobalTheory.finsupp_eq_zero_of_sum_torsion_characters_eq_zero k Φ.E.X n ζ (Nat.pos_of_ne_zero hn0) hζ k c
      (fun a ha b hb => hinc a ((hA a).1 (hcs ha)) b ((hA b).1 (hcs hb))) fun t ht => ?_
    obtain ⟨a, -, ha, hat⟩ := GlobalTheory.TorusTranslate.exists_point_translate_pure k Φ t
    have hax : (a * x) ^ n = 1 := by
      rw [mul_pow, ha n ht, hx, _root_.one_mul]
    have hl' := (hat d α ψ hψ.1 x l hl).1
    have h0 : valF (F := k) (a * x).left ((Φ.H d).U l) (φ.f l) = 0 := by
      by_contra h
      exact hφ _ hax ((le_nonzeroLocus_iff (F := k) φ (a * x).left).2 ⟨l, hl', h⟩)
    rw [Finsupp.sum_of_support_subset c hcs _ (fun _ _ => smul_zero _), ← h0]
    have h1 := hsum φ A p' (fun β hβ => (hA β).2 hβ) (fun β _ => hp' β) l
    refine Eq.trans ?_ ((congrArg (valF (F := k) (a * x).left _) h1).trans (valF_sum (F := k) hl' _ _)).symm
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [Finsupp.indicator_of_mem hβ]
    exact (hat d β (p' β) (hp' β).1 x l hl).2.symm
  have h2 : c α = v α := Finsupp.indicator_of_mem ((hA α).2 hα) _
  apply hne
  have h3 : v α = 0 := by rw [← h2, hc]; rfl
  have h4 : p' α = ψ := if_pos rfl
  rw [← h4]
  exact h3

end GlobalTheory.TorsionFourier
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
theorem _root_.GlobalTheory.T.part_vanishes_on_torus_torsion_fourier : (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (d n : ℕ), (n : k) ≠ 0 → ∀ φ : (Φ.H d).Sec, (∀ α ∈ Φ.supp φ, ∀ β ∈ Φ.supp φ, (∃ w, α = β + n • w) → α = β) → (∀ x : Φ.Pt, x ^ n = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ) → ∀ α ψ, Φ.IsPart α φ ψ → ∀ x : Φ.Pt, x ^ n = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus ψ) := by
  atlas_forward_decl GlobalTheory.TorsionFourier.part_vanishes_on_torsion
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.PureZero

theorem lt_of_big {g N N' : ℕ} (h : Big g N N') (hg : 1 ≤ g) : N ^ g * g.factorial < N' := by
  have hs := h.sep
  have h4 : (4 : ℝ) ≤ N := by exact_mod_cast h.four
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have h1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ g := one_le_pow₀ (by norm_num)
  have h2 : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ ((g : ℝ) / 2 - 1) := by
    have : (2 : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ ((g : ℝ) / 2 - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_neg_one] at this
    linarith
  have h3 : (1 / 2 : ℝ) ≤ (g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1) := by
    have : (1 : ℝ) ≤ (g : ℝ) * (3 / 2 : ℝ) ^ g := one_le_mul_of_one_le_of_one_le hg' h1
    nlinarith
  set C := (g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)
  have hM : (0 : ℝ) ≤ ((N ^ g * g.factorial : ℕ) : ℝ) := Nat.cast_nonneg _
  have h5 : (1 : ℝ) ≤ 2 * C * N := by nlinarith
  have : ((N ^ g * g.factorial : ℕ) : ℝ) < N' := by nlinarith
  exact_mod_cast this

theorem sec_eq_zero_of_dim_zero {K : Type} [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (hg : P.g = 0)
    {M : LB (Out.baseOver (Sp K) ⊗ P.A).left} (s : M.Sec)
    (hs : ¬ ⊤ ≤ (Out.ptSecT P.A (1 : Out.baseOver (Sp K) ⟶ P.A)).left ⁻¹ᵁ Out.nonzeroLocus s) (j : M.ι) :
    s.f j = 0 := by
  have := polAV_isIntegral_of_isAlgClosed K P
  have : Etale P.A.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 (hg ▸ P.smoothDim)
  let e : Sp K ⟶ P.A.left := (1 : Out.baseOver (Sp K) ⟶ P.A).left
  have := isOpenImmersion_of_section_of_etale P.A.hom e (Over.w _)
  have : IsDominant e := ⟨e.isOpenEmbedding.isOpen_range.dense ⟨_, (default : PrimeSpectrum K), rfl⟩⟩
  have : IsIso (snd (Out.baseOver (Sp K)) P.A).left :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 (Sp K)) P.A.hom))
  let z : Sp K ⟶ (Out.baseOver (Sp K) ⊗ P.A).left := (Out.ptSecT P.A (1 : Out.baseOver (Sp K) ⟶ P.A)).left
  have hz : z = e ≫ inv (snd (Out.baseOver (Sp K)) P.A).left := by
    rw [IsIso.eq_comp_inv]
    exact congrArg (·.left) (lift_snd (𝟙 _) (1 : Out.baseOver (Sp K) ⟶ P.A))
  have hd : IsDominant z := by rw [hz]; infer_instance
  have : IsReduced (Out.baseOver (Sp K) ⊗ P.A).left :=
    isReduced_of_isOpenImmersion (snd (Out.baseOver (Sp K)) P.A).left
  by_contra hne
  have hb : ((Out.baseOver (Sp K) ⊗ P.A).left.basicOpen (s.f j) : Set (Out.baseOver (Sp K) ⊗ P.A).left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun h => hne ((basicOpen_eq_bot_iff _).1 (TopologicalSpace.Opens.ext h))
  obtain ⟨y, hy⟩ := hd.denseRange.exists_mem_open (TopologicalSpace.Opens.isOpen _) hb
  refine hs fun y' _ => ?_
  have : y' = y := Subsingleton.elim (α := PrimeSpectrum K) _ _
  subst this
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hy⟩

theorem twist_eq_zero (h : Out.Laws) (h₂ : Out.Laws2) {K : Type} [Field K] [IsAlgClosed K]
    (P : Out.PolAV (Sp K)) {g N N' d : ℕ} (hB : Big g N N') (hN' : (N' : K) ≠ 0) (hg : P.g ≤ g) (hd : 1 ≤ d)
    (hd' : d ≤ N ^ g * g.factorial) (c : Out.baseOver (Sp K) ⟶ P.A)
    (s : LB.Sec (Out.twistLB P.A P.L (N * d) c))
    (hs : ∀ x : Out.baseOver (Sp K) ⟶ P.A, x ^ N' = 1 → ¬ ⊤ ≤ (Out.ptSecT P.A x).left ⁻¹ᵁ Out.nonzeroLocus s) :
    ∀ j, s.f j = 0 := by
  rcases Nat.eq_zero_or_pos P.g with h0 | h0
  · exact sec_eq_zero_of_dim_zero P h0 s (hs 1 (one_pow _))
  by_contra hne
  push Not at hne
  have hM1 : 1 ≤ N' := Nat.pos_of_ne_zero fun e => hN' (by rw [e, Nat.cast_zero])
  have hcard := (h.mulN (Sp K) P N' hM1).2.2.2.2 K (𝟙 _) hN'
  have h₄ := card_torsion_zeros_twist_le h h₂ K P N d N' c h0 hB.four hd hN' s hne
  have e : N' ^ (2 * P.g) = N' ^ 2 * N' ^ (2 * P.g - 2) := by rw [← pow_add]; congr 1; omega
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => and_iff_left_of_imp (hs x)), hcard, e] at h₄
  have h₅ := Nat.le_of_mul_le_mul_right h₄ (pow_pos hM1 _)
  have h₆ := lt_of_big hB (h0.trans_le hg)
  have h₇ : N ^ P.g * P.g.factorial ≤ N ^ g * g.factorial :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by have := hB.four; omega) hg) (Nat.factorial_le hg)
  have h₈ := Nat.mul_le_mul h₇ hd'
  nlinarith

theorem pure_eq_zero_of_vanishing_on_torsion :
    Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' d : ℕ) (π : Φ.Pol N), Big g N N' → (N' : k) ≠ 0 → π.PB.g ≤ g → 1 ≤ d → d ≤ N ^ g * g.factorial → ∀ (α : Φ.E.X) (φ : (Φ.H d).Sec), Φ.Pure α φ → (∀ x : Φ.Pt, x ^ N' = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ) → ∀ l, φ.f l = 0) := by
  intro h h₂ k _ _ Φ g N N' d π hB hN' hg hd hd' α φ hφ hx
  have hM1 : 1 ≤ N' := Nat.pos_of_ne_zero fun e => hN' (by rw [e, Nat.cast_zero])
  obtain ⟨s, hs0, hs⟩ := (GlobalTheory.T.pureWeightSection_to_twistedPolarisationPower k Φ N d π α (by have := hB.four; omega) hd).1 φ hφ
  refine hs0 (twist_eq_zero h h₂ π.PB hB hN' hg hd hd' _ s fun b hb => ?_)
  have := π.hom
  have hb' : (b ≫ π.β.inv) ^ N' = 1 := by
    rw [← cancel_mono π.β.hom, MonObj.pow_comp, MonObj.one_comp, Category.assoc, π.β.inv_hom_id,
      Category.comp_id, hb]
  obtain ⟨x, hx1, hxq⟩ := (TorsLift.points_lift k Φ.E Φ.G Φ.D N' hM1).2.1 _ hb'
  have e : x ≫ Φ.D.q ≫ π.β.hom = b := by
    rw [← Category.assoc, hxq, Category.assoc, π.β.inv_hom_id, Category.comp_id]
  rw [← e]
  exact fun hh => hx x hx1 ((hs x).2 hh)

end GlobalTheory.PureZero
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.TorsionVanish

theorem form_vanishes_of_torsion : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (π : Φ.Pol N), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → (N' : k) ≠ 0 → ∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → (∀ x : Φ.Pt, x ^ N' = 1 → ∃ v, Crd (Φ.H 1) F x.left v ∧ MvPolynomial.eval v Pf = 0) → ∀ v ∈ cone Φ.G.hom (Φ.H 1) F, MvPolynomial.eval v Pf = 0) := by
  intro L1 L2 k _ _ Φ g N N' q J _ cls F π hBig hGood hg hN' d Pf hd hPf hx v hv
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hd1
  · obtain ⟨v0, -, hv0⟩ := hx 1 (one_pow _)
    have hC : Pf = MvPolynomial.C (Pf.coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hPf.totalDegree_le)
    rw [hC] at hv0 ⊢
    simpa using hv0
  obtain ⟨φ, -, hsupp, hval⟩ := GlobalTheory.ZH.FormSec.exists_formSec k Φ J F d Pf hPf
  obtain ⟨hpart, hfin, -, hsum⟩ := GlobalTheory.ZH.WtPart.weight_parts k Φ d
  obtain ⟨-, -, hsep⟩ := GlobalTheory.exists_basis_unique_min_and_sums_separated Φ.E.X q hGood.pos _ g N N'
    (N ^ g * g.factorial) rfl (by omega) hBig.lll hBig.sep
  have hdist : ∀ α ∈ Φ.supp φ, ∀ β ∈ Φ.supp φ, (∃ w, α = β + N' • w) → α = β := by
    rintro α hα β hβ ⟨w, hw⟩
    obtain ⟨a, ha, rfl⟩ := hsupp α hα
    obtain ⟨b, hb, rfl⟩ := hsupp β hβ
    have h0 : w = 0 := hsep d a b hd
      (fun j => by obtain ⟨i, hi⟩ := ha j; exact (hGood.supp i _ hi).1)
      (fun j => by obtain ⟨i, hi⟩ := hb j; exact (hGood.supp i _ hi).1) w hw
    rw [hw, h0, smul_zero, add_zero]
  have htor : ∀ x : Φ.Pt, x ^ N' = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ := fun x hx1 => by
    obtain ⟨v0, hc, h0⟩ := hx x hx1
    exact (hval x v0 hc).1 h0
  choose ψ hψ using hpart φ
  have hψ0 : ∀ α l, (ψ α).f l = 0 := fun α =>
    GlobalTheory.PureZero.pure_eq_zero_of_vanishing_on_torsion L1 L2 k Φ g N N' d π hBig hN' (by omega) hd1 hd α (ψ α) (hψ α).1
      (GlobalTheory.T.part_vanishes_on_torus_torsion_fourier k Φ d N' hN' φ hdist htor α (ψ α) (hψ α))
  have hφ0 : ∀ l, φ.f l = 0 := fun l => by
    rw [hsum φ (hfin φ).toFinset ψ (by simp) (fun α _ => hψ α) l]
    exact Finset.sum_eq_zero fun α _ => hψ0 α l
  obtain ⟨x, hxp, hc⟩ := hv
  refine (hval (Over.homMk x hxp) v hc).2 fun h => ?_
  have hb : Out.nonzeroLocus φ = ⊥ := by
    simp [Out.nonzeroLocus, hφ0]
  rw [hb] at h
  obtain ⟨p⟩ : Nonempty (Sp k) := (inferInstance : Nonempty (PrimeSpectrum k))
  exact h (Set.mem_univ p)

end GlobalTheory.ZH.TorsionVanish
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.form_vanishes_of_torsion_torusExtension : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (π : Φ.Pol N), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → (N' : k) ≠ 0 → ∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → (∀ x : Φ.Pt, x ^ N' = 1 → ∃ v, Crd (Φ.H 1) F x.left v ∧ MvPolynomial.eval v Pf = 0) → ∀ v ∈ cone Φ.G.hom (Φ.H 1) F, MvPolynomial.eval v Pf = 0) := by
  atlas_forward_decl GlobalTheory.ZH.TorsionVanish.form_vanishes_of_torsion
end
