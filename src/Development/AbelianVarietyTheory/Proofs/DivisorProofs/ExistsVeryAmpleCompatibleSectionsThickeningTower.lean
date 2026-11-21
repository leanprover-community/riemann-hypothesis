import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsAffineOpenPreimageEqOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerCechH1Uniform
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLbOfGeneratedSystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerSquares
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecOnPullSurjectiveOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftedRatiosProjectiveRelations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftedRatiosGenerateSurjective
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg.ChartsEx

section Level0

variable {X : Scheme.{0}} {H : LB X}

theorem exists_chart_of_mem_nonzeroLocus (s : LB.Sec H) {x : X} (hx : x ∈ nonzeroLocus s) :
    ∃ k, x ∈ H.U k := by
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact ⟨l, X.basicOpen_le _ hl⟩

theorem mem_nonzeroLocus_iff_basicOpen (s : LB.Sec H) (k : H.ι) {x : X} (hk : x ∈ H.U k) :
    x ∈ nonzeroLocus s ↔ x ∈ X.basicOpen (s.f k) := by
  refine ⟨fun hx => ?_, fun hx => TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx⟩⟩
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have e := congrArg X.basicOpen (s.compat k l)
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (H.g k l).isUnit] at e
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e
  have hx' : x ∈ H.U k ⊓ H.U l := ⟨hk, X.basicOpen_le _ hl⟩
  exact (e.ge ⟨hx', hx', hl⟩).2

theorem isUnit_rs (s : LB.Sec H) (k : H.ι) {O : X.Opens} (hk : O ≤ H.U k)
    (h : O ≤ nonzeroLocus s) : IsUnit (rs X hk (s.f k)) := by
  have hb : O ≤ X.basicOpen (s.f k) := fun x hx => (mem_nonzeroLocus_iff_basicOpen s k (hk hx)).1 (h hx)
  have hu : IsUnit (rs X (X.basicOpen_le (s.f k)) (s.f k)) :=
    X.toRingedSpace.isUnit_res_basicOpen (s.f k)
  simpa only [rs_rs] using hu.map (rs X hb)

theorem ratio_self (s : LB.Sec H) {V : X.Opens} (h : V ≤ nonzeroLocus s) (r : Γ(X, V))
    (hr : ∀ k, rs X (inf_le_right : V ⊓ H.U k ≤ H.U k) (s.f k) =
      rs X (inf_le_left : V ⊓ H.U k ≤ V) r * rs X (inf_le_right : V ⊓ H.U k ≤ H.U k) (s.f k)) :
    r = 1 := by
  refine X.sheaf.eq_of_locally_eq' (fun k : H.ι => V ⊓ H.U k) V (fun k => homOfLE inf_le_left)
    (fun x hx => ?_) _ _ fun k => ?_
  · obtain ⟨l, hl⟩ := exists_chart_of_mem_nonzeroLocus s (h hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, hx, hl⟩
  · change rs X inf_le_left r = rs X inf_le_left 1
    rw [map_one]
    exact (isUnit_rs s k inf_le_right (inf_le_left.trans h)).mul_right_cancel
      ((hr k).symm.trans (_root_.one_mul _).symm)

variable {n : ℕ} (s : Fin (n + 1) → LB.Sec H) (r : ∀ i, Fin (n + 1) → Γ(X, nonzeroLocus (s i)))
  (hr : ∀ i j k, rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) =
    rs X (inf_le_left : nonzeroLocus (s i) ⊓ H.U k ≤ nonzeroLocus (s i)) (r i j) *
      rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s i).f k))

include hr in

theorem basicOpen_ratio (i j : Fin (n + 1)) :
    X.basicOpen (r i j) = nonzeroLocus (s i) ⊓ nonzeroLocus (s j) := by
  have key : ∀ k, (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen ((s j).f k) =
      (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen (r i j) := by
    intro k
    have e := congrArg X.basicOpen (hr i j k)
    rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (isUnit_rs (s i) k inf_le_right inf_le_left)] at e
    erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e
    rw [e, inf_assoc, inf_comm (X.basicOpen (r i j)), ← inf_assoc, inf_idem]
  ext x
  constructor
  · intro hx
    have hxi : x ∈ nonzeroLocus (s i) := X.basicOpen_le _ hx
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus (s i) hxi
    have hm : x ∈ (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen (r i j) := ⟨⟨hxi, hk⟩, hx⟩
    rw [← key k] at hm
    exact ⟨hxi, TopologicalSpace.Opens.mem_iSup.2 ⟨k, hm.2⟩⟩
  · rintro ⟨hxi, hxj⟩
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus (s i) hxi
    have hm : x ∈ (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen ((s j).f k) :=
      ⟨⟨hxi, hk⟩, (mem_nonzeroLocus_iff_basicOpen (s j) k hk).1 hxj⟩
    rw [key k] at hm
    exact hm.2

include hr in

theorem ratio_cocycle (i j l : Fin (n + 1)) :
    rs X (inf_le_left : nonzeroLocus (s i) ⊓ nonzeroLocus (s j) ≤ nonzeroLocus (s i)) (r i l) =
      rs X (inf_le_left : nonzeroLocus (s i) ⊓ nonzeroLocus (s j) ≤ nonzeroLocus (s i)) (r i j) *
        rs X (inf_le_right : nonzeroLocus (s i) ⊓ nonzeroLocus (s j) ≤ nonzeroLocus (s j)) (r j l) := by
  refine X.sheaf.eq_of_locally_eq' (fun k : H.ι => (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k)
    (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) (fun k => homOfLE inf_le_left) (fun x hx => ?_) _ _
    fun k => ?_
  · obtain ⟨l', hl⟩ := exists_chart_of_mem_nonzeroLocus (s i) hx.1
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨l', hx, hl⟩
  · change rs X inf_le_left _ = rs X inf_le_left _
    have hi : (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k ≤ nonzeroLocus (s i) ⊓ H.U k :=
      inf_le_inf_right _ inf_le_left
    have hj : (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k ≤ nonzeroLocus (s j) ⊓ H.U k :=
      inf_le_inf_right _ inf_le_right
    have e1 := congrArg (rs X hi) (hr i l k)
    have e2 := congrArg (rs X hi) (hr i j k)
    have e3 := congrArg (rs X hj) (hr j l k)
    simp only [map_mul, rs_rs] at e1 e2 e3 ⊢
    have hu := isUnit_rs (s i) k (inf_le_right : (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k ≤ H.U k)
      (inf_le_left.trans inf_le_left)
    refine hu.mul_right_cancel ?_
    rw [← e1, e3, e2]
    ring

end Level0

end GlobalTheory.FormalAlg.ChartsEx

namespace GlobalTheory.FormalAlg.ChartsEx

section Tower

variable {R : Type} [CommRing R] {I : Ideal R}

theorem surjective_thickTrans (e : ℕ) : Surjective (thickTrans R I e) := by
  refine ⟨fun x => ?_⟩
  have h : I ^ (e + 1 + 1) ≤ I ^ (e + 1) := Ideal.pow_le_pow_right (by omega)
  have hx : (x : PrimeSpectrum (R ⧸ I ^ (e + 1 + 1))) ∈
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.factor h)) := by
    rw [_root_.range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective h)]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have ha' : a ∈ I ^ (e + 1) := by
      simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using ha
    refine x.2.mem_of_pow_mem 2 ?_
    have : Ideal.Quotient.mk (I ^ (e + 1 + 1)) a ^ 2 = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      refine Ideal.pow_le_pow_right (show e + 1 + 1 ≤ (e + 1) * 2 by omega) ?_
      rw [pow_mul]
      exact Ideal.pow_mem_pow ha' 2
    rw [this]
    exact Ideal.zero_mem _
  exact hx

theorem isNilpotent_ker_factor (e : ℕ) (h : I ^ (e + 1 + 1) ≤ I ^ (e + 1)) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor h)) := by
  refine ⟨2, le_bot_iff.1 ?_⟩
  rw [pow_two, Ideal.mul_le]
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have ha : a ∈ I ^ (e + 1) := by simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hx
  have hb : b ∈ I ^ (e + 1) := by simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hy
  rw [← map_mul, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.pow_le_pow_right (show e + 1 + 1 ≤ (e + 1) + (e + 1) by omega) ?_
  rw [pow_add]
  exact Ideal.mul_mem_mul ha hb

variable {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
  {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {n : ℕ}

variable (Y n) in

abbrev Lvl (e : ℕ) : Type :=
  {p : (Σ D : Fin (n + 1) → (Y e).left.Opens, ∀ i, Fin (n + 1) → Γ((Y e).left, D i)) //
    ∀ i, IsAffineOpen (p.1 i)}

variable (β) in

def Lifts (e : ℕ) (q : Lvl Y n e) (q' : Lvl Y n (e + 1)) : Prop :=
  ∃ h : ∀ i, β e ⁻¹ᵁ q'.1.1 i = q.1.1 i,
    ∀ i j, ((β e).appLE (q'.1.1 i) (q.1.1 i) (h i).ge).hom (q'.1.2 i j) = q.1.2 i j

theorem exists_lifts {e : ℕ} (hsq : IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (q : Lvl Y n e) : ∃ q' : Lvl Y n (e + 1), Lifts β e q q' := by
  have hle : I ^ (e + 1 + 1) ≤ I ^ (e + 1) := Ideal.pow_le_pow_right (by omega)
  have hsurj : Function.Surjective (Ideal.Quotient.factor hle) := Ideal.Quotient.factor_surjective hle
  have hD := fun i => GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent _ _
    (Ideal.Quotient.factor hle) hsurj (isNilpotent_ker_factor e hle) _ _ (Y (e + 1)).hom (Y e).hom
    (β e) hsq (q.1.1 i) (q.2 i)
  choose D' hD' hpre using hD
  haveI : IsClosedImmersion (β e) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip
      (IsClosedImmersion.spec_of_surjective _ hsurj)
  have hs : ∀ i, Function.Surjective ((β e).appLE (D' i) (q.1.1 i) (hpre i).ge).hom := by
    intro i y
    obtain ⟨x, hx⟩ := (β e).app_surjective (D' i) (hD' i) (rs _ (hpre i).le y)
    refine ⟨x, ?_⟩
    change rs _ (hpre i).ge (((β e).app (D' i)).hom x) = y
    rw [hx, rs_rs, rs_self]
  choose ρ' hρ' using fun i j => hs i (q.1.2 i j)
  exact ⟨⟨⟨D', ρ'⟩, hD'⟩, hpre, hρ'⟩

variable (β) in

def seq (hsq : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (q₀ : Lvl Y n 0) (e : ℕ) : Lvl Y n e :=
  Nat.rec (motive := Lvl Y n) q₀ (fun e q => Classical.choose (exists_lifts (hsq e) q)) e

theorem seq_lifts (hsq : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (q₀ : Lvl Y n 0) (e : ℕ) : Lifts β e (seq β hsq q₀ e) (seq β hsq q₀ (e + 1)) :=
  Classical.choose_spec (exists_lifts (hsq e) (seq β hsq q₀ e))

end Tower

end GlobalTheory.FormalAlg.ChartsEx

open GlobalTheory.FormalAlg.ChartsEx in

theorem GlobalTheory.FormalAlg.exists_charts_of_veryAmpleBy : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H₀ : LB (Y 0).left) (n : ℕ) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → VeryAmpleBy (Y 0).hom H₀ s₀ → ∃ C : Charts I Y β n, (∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m) := by
  intro R _ I Y β hsq H₀ n s₀ _ hva
  obtain ⟨hcov, hloc⟩ := hva
  choose haff r hrel hsurj using hloc
  let q₀ : Lvl Y n 0 := ⟨⟨fun i => nonzeroLocus (s₀ i), r⟩, haff⟩
  have hsurjβ : ∀ e, Surjective (β e) := fun e =>
    MorphismProperty.of_isPullback (P := @Surjective) (hsq e).flip (surjective_thickTrans e)
  have hcover : ∀ e, ⨆ i, (seq β hsq q₀ e).1.1 i = ⊤ := by
    intro e
    induction e with
    | zero => exact hcov
    | succ e ih =>
      obtain ⟨hpre, -⟩ := seq_lifts hsq q₀ e
      refine top_unique fun y _ => ?_
      obtain ⟨x, rfl⟩ := (hsurjβ e).surj y
      have hx : x ∈ β e ⁻¹ᵁ (⨆ i, (seq β hsq q₀ (e + 1)).1.1 i) := by
        rw [Scheme.Hom.preimage_iSup]
        simp only [hpre]
        rw [ih]
        trivial
      exact hx
  refine ⟨{ D := fun e => (seq β hsq q₀ e).1.1
            aff := fun e => (seq β hsq q₀ e).2
            cover := hcover
            pre := fun e => (seq_lifts hsq q₀ e).1
            ρ := fun e => (seq β hsq q₀ e).1.2
            ρ_pull := fun e => (seq_lifts hsq q₀ e).2
            ρ_self := fun i => ratio_self (s₀ i) le_rfl (r i i) (hrel i i)
            basic := fun i j => basicOpen_ratio s₀ r hrel i j
            cocycle := fun i j l => ratio_cocycle s₀ r hrel i j l
            surj := hsurj }, fun i => rfl, hrel⟩
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standard_charts_formalTower_of_veryAmple : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H₀ : LB (Y 0).left) (n : ℕ) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → VeryAmpleBy (Y 0).hom H₀ s₀ → ∃ C : Charts I Y β n, (∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m) := by
  atlas_forward_decl GlobalTheory.FormalAlg.exists_charts_of_veryAmpleBy
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FormalAlg

theorem lift_localUnits_of_thickening :
    ∀ (R : Type) [CommRing R] (J : Ideal R) (X X₀ : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (γ : X₀ ⟶ X) (q : X₀ ⟶ Spec (CommRingCat.of (R ⧸ J))), IsPullback γ q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → Surjective γ → ∀ (L : LB X), L.IsLB → ∀ D : X.Opens, IsAffineOpen D → ∀ u : ∀ m : L.ι, Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, (∀ z m m', γ z ∈ D ⊓ L.U m → γ z ∈ D ⊓ L.U m' → gm (𝟙 X₀) z _ (u m) = gm γ z _ (L.g m m') * gm (𝟙 X₀) z _ (u m')) → ∃ τ : ∀ m : L.ι, Γ(X, D ⊓ L.U m)ˣ, (∀ m, (γ.app (D ⊓ L.U m)).hom (τ m).val = (u m).val) ∧ ∀ x m m', x ∈ D ⊓ L.U m → x ∈ D ⊓ L.U m' → gm (𝟙 X) x _ (τ m) = gm (𝟙 X) x _ (L.g m m') * gm (𝟙 X) x _ (τ m') := by
  intro R _ J X X₀ f γ q hpb hsurj L hL D hD u hu
  have hLp := LB.isLB_pull hL γ
  let O : L.ι → X₀.Opens := fun m => γ ⁻¹ᵁ (D ⊓ L.U m)
  have hO : ∀ m, O m ≤ γ ⁻¹ᵁ D := fun m => γ.preimage_mono inf_le_left
  have hc : γ ⁻¹ᵁ D ≤ ⨆ m, O m := by
    intro z hz
    obtain ⟨m, hm⟩ := exists_chart hL (γ z)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨m, show γ z ∈ D ⊓ L.U m from ⟨hz, hm⟩⟩
  have hU : ∀ m, O m ≤ (L.pull γ).U (fun _ => m) := fun m z hz => mem_pull.2 hz.2

  have hg : ∀ z a b, γ z ∈ L.U a → γ z ∈ L.U b →
      gm (𝟙 X₀) z ((L.pull γ).U (fun _ => a) ⊓ (L.pull γ).U (fun _ => b))
        ((L.pull γ).g (fun _ => a) (fun _ => b)) = gm γ z _ (L.g a b) := by
    intro z a b ha hb
    have hp : (𝟙 X₀) z ∈ (L.pull γ).U (fun _ => a) ⊓ (L.pull γ).U (fun _ => b) :=
      ⟨mem_pull.2 ha, mem_pull.2 hb⟩
    show gm (𝟙 X₀) z _ (∏ _k : PUnit, (res _ (pullU γ _ (L.g a b))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    refine (gm_res (𝟙 X₀) z _ hp _).trans ((gm_pull (𝟙 X₀) γ z (L.U a ⊓ L.U b) ⟨ha, hb⟩ _).trans ?_)
    rw [Category.id_comp]
  have hcomp : ∀ a b, rs X₀ (inf_le_left : O a ⊓ O b ≤ O a) (u a).val =
      rs X₀ (inf_le_inf (hU a) (hU b)) ((L.pull γ).g (fun _ => a) (fun _ => b)).val *
        rs X₀ (inf_le_right : O a ⊓ O b ≤ O b) (u b).val := by
    intro a b
    have e : res (inf_le_left : O a ⊓ O b ≤ O a) (u a) =
        res (inf_le_inf (hU a) (hU b)) ((L.pull γ).g (fun _ => a) (fun _ => b)) *
          res (inf_le_right : O a ⊓ O b ≤ O b) (u b) := by
      apply unit_ext
      intro z hz
      have hz' : (𝟙 X₀) z ∈ O a ⊓ O b := hz
      rw [map_mul, gm_res _ z _ hz', gm_res _ z _ hz', gm_res _ z _ hz',
        hg z a b hz.1.2 hz.2.2]
      exact hu z a b hz.1 hz.2
    have e' := congrArg Units.val e
    simp only [Units.val_mul, GlobalTheory.LB.val_res] at e'
    exact e'
  obtain ⟨t, ht, -⟩ := SecOn.existsUnique_of_local hLp O hO hc (fun m _ => m) hU
    (fun m => (u m).val) hcomp
  obtain ⟨s, hs⟩ := secOn_pull_surjective_of_surjective R (R ⧸ J) (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective X X₀ f q γ hpb L hL D hD t
  have hcoord : ∀ m, (γ.app (D ⊓ L.U m)).hom (GlobalTheory.LB.coord s m) = (u m).val := by
    intro m
    have e := ht m
    rw [← hs] at e
    erw [SecOn.coord_pull γ s (fun _ => m), GlobalTheory.LB.resG_appLE] at e
    rw [Scheme.Hom.app_eq_appLE]
    exact e
  have hunit : ∀ m, IsUnit (GlobalTheory.LB.coord s m) := by
    intro m
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    obtain ⟨z, rfl⟩ := γ.surjective x
    apply isUnit_of_map_unit (γ.stalkMap z).hom
    erw [Scheme.Hom.germ_stalkMap_apply γ (D ⊓ L.U m) z hx, hcoord m]
    exact (u m).isUnit.map _
  refine ⟨fun m => (hunit m).unit, fun m => hcoord m, ?_⟩
  intro x m m' hx hx'
  have hi : D ⊓ L.U m ⊓ L.U m' ≤ D ⊓ L.U m := inf_le_left
  have hj : D ⊓ L.U m ⊓ L.U m' ≤ D ⊓ L.U m' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hij : D ⊓ L.U m ⊓ L.U m' ≤ L.U m ⊓ L.U m' :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have e : res hi (hunit m).unit = res hij (L.g m m') * res hj (hunit m').unit := by
    apply Units.ext
    simp only [Units.val_mul, GlobalTheory.LB.val_res, IsUnit.unit_spec]
    exact SecOn.compat s m m' hi hj hij
  have hxx : (𝟙 X) x ∈ D ⊓ L.U m ⊓ L.U m' := ⟨hx, hx'.2⟩
  have e' := congrArg (gm (𝟙 X) x _) e
  rw [map_mul, gm_res _ x _ hxx, gm_res _ x _ hxx, gm_res _ x _ hxx] at e'
  exact e'

end GlobalTheory.FormalAlg
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_local_units_along_nilpotent_thickening : ∀ (R : Type) [CommRing R] (J : Ideal R) (X X₀ : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (γ : X₀ ⟶ X) (q : X₀ ⟶ Spec (CommRingCat.of (R ⧸ J))), IsPullback γ q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → Surjective γ → ∀ (L : LB X), L.IsLB → ∀ D : X.Opens, IsAffineOpen D → ∀ u : ∀ m : L.ι, Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, (∀ z m m', γ z ∈ D ⊓ L.U m → γ z ∈ D ⊓ L.U m' → gm (𝟙 X₀) z _ (u m) = gm γ z _ (L.g m m') * gm (𝟙 X₀) z _ (u m')) → ∃ τ : ∀ m : L.ι, Γ(X, D ⊓ L.U m)ˣ, (∀ m, (γ.app (D ⊓ L.U m)).hom (τ m).val = (u m).val) ∧ ∀ x m m', x ∈ D ⊓ L.U m → x ∈ D ⊓ L.U m' → gm (𝟙 X) x _ (τ m) = gm (𝟙 X) x _ (L.g m m') * gm (𝟙 X) x _ (τ m') := by
  atlas_forward_decl GlobalTheory.FormalAlg.lift_localUnits_of_thickening
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

namespace GlobalTheory.FormalAlg

theorem Charts.tower_preimage_germ : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (n : ℕ) (C : Charts I Y β n) (γ : ∀ e, (Y 0).left ⟶ (Y e).left), γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e : ℕ) (i : Fin (n + 1)), γ e ⁻¹ᵁ C.D e i = C.D 0 i ∧ ∀ (j : Fin (n + 1)) (z : (Y 0).left), z ∈ C.D 0 i → gs (γ e) z (C.D e i) (C.ρ e i j) = gs (𝟙 _) z (C.D 0 i) (C.ρ 0 i j) := by
  intro R _ I Y β n C γ h0 hγ e
  induction e with
  | zero =>
    intro i
    subst_vars
    refine ⟨?_, fun j z _ => ?_⟩
    · rw [h0]; rfl
    · rw [h0]
  | succ e ih =>
    intro i
    obtain ⟨hpre, hgerm⟩ := ih i
    have hp : γ (e + 1) ⁻¹ᵁ C.D (e + 1) i = C.D 0 i := by
      rw [← hγ e, Scheme.Hom.comp_preimage, C.pre, hpre]
    refine ⟨hp, fun j z hz => ?_⟩
    have hz' : γ e z ∈ C.D e i := by rw [← hpre] at hz; exact hz
    have hz'' : β e (γ e z) ∈ C.D (e + 1) i := by
      have : γ e z ∈ β e ⁻¹ᵁ C.D (e + 1) i := by rw [C.pre]; exact hz'
      exact this
    rw [← hgerm j z hz, ← C.ρ_pull e i j, ← hγ e, ← gs_pull (γ e) (β e) z _ hz'',
      ← gs_res (γ e) z (C.pre e i).ge hz']
    rfl

end GlobalTheory.FormalAlg
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickeningTowerCharts_preimage_and_germ_pullback : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (n : ℕ) (C : Charts I Y β n) (γ : ∀ e, (Y 0).left ⟶ (Y e).left), γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e : ℕ) (i : Fin (n + 1)), γ e ⁻¹ᵁ C.D e i = C.D 0 i ∧ ∀ (j : Fin (n + 1)) (z : (Y 0).left), z ∈ C.D 0 i → gs (γ e) z (C.D e i) (C.ρ e i j) = gs (𝟙 _) z (C.D 0 i) (C.ρ 0 i j) := by
  atlas_forward_decl GlobalTheory.FormalAlg.Charts.tower_preimage_germ
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

namespace GlobalTheory.Div.FramePull

variable {X X₀ : Scheme.{0}}

theorem isUnit_res_of_le {V U : X₀.Opens} (f : Γ(X₀, U)) (h : V ≤ X₀.basicOpen f) :
    IsUnit ((X₀.presheaf.map (homOfLE (h.trans (X₀.basicOpen_le f))).op).hom f) := by
  have e : (X₀.presheaf.map (homOfLE (h.trans (X₀.basicOpen_le f))).op).hom f =
      (X₀.presheaf.map (homOfLE h).op).hom ((X₀.presheaf.map (homOfLE (X₀.basicOpen_le f)).op).hom f) := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  rw [e]
  exact (X₀.toRingedSpace.isUnit_res_basicOpen f).map _

theorem le_basicOpen {H : LB X₀} (s : LB.Sec H) (a : H.ι) :
    nonzeroLocus s ⊓ H.U a ≤ X₀.basicOpen (s.f a) := by
  rintro z ⟨hz, ha⟩
  obtain ⟨a', ha'⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  have e := congrArg X₀.basicOpen (s.compat a a')
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (H.g a a').isUnit, Scheme.basicOpen_res,
    Scheme.basicOpen_res] at e
  have hm : z ∈ H.U a ⊓ H.U a' ⊓ X₀.basicOpen (s.f a) := by
    rw [e]; exact ⟨⟨ha, X₀.basicOpen_le _ ha'⟩, ⟨ha, X₀.basicOpen_le _ ha'⟩, ha'⟩
  exact hm.2

theorem gm_gen_div {M L' : LB X₀} {w : LB.Iso L' M} (hw : w.IsGen) (z : X₀) (p q : M.ι × L'.ι)
    (hp : z ∈ M.U p.1 ⊓ L'.U p.2) (hq : z ∈ M.U q.1 ⊓ L'.U q.2) :
    gm (𝟙 X₀) z _ (w.s p) = gm (𝟙 X₀) z (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) *
      (gm (𝟙 X₀) z (L'.U p.2 ⊓ L'.U q.2) (L'.g p.2 q.2))⁻¹ * gm (𝟙 X₀) z _ (w.s q) := by
  have hm : z ∈ (LB.div M L').U p ⊓ (LB.div M L').U q := ⟨hp, hq⟩
  have := congrArg (gm (𝟙 X₀) z _) (hw p q)
  rw [gm_res _ z _ hm, map_mul, gm_res _ z _ hm] at this
  rw [this]
  refine congrArg (· * _) ?_
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ z _ hm _)
    ((map_inv _ _).trans (congrArg _ (gm_res _ z _ hm _))))

theorem gm_pull_g (L : LB X) (γ : X₀ ⟶ X) (z : X₀) (m m' : L.ι) (hm : γ z ∈ L.U m) (hm' : γ z ∈ L.U m') :
    gm (𝟙 X₀) z ((L.pull γ).U (fun _ => m) ⊓ (L.pull γ).U (fun _ => m'))
      ((L.pull γ).g (fun _ => m) (fun _ => m')) = gm γ z _ (L.g m m') := by
  have hp : z ∈ (L.pull γ).U (fun _ => m) ⊓ (L.pull γ).U (fun _ => m') := ⟨mem_pull.2 hm, mem_pull.2 hm'⟩
  show gm (𝟙 X₀) z _ (∏ _k : PUnit, (res _ (pullU γ _ (L.g m m'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  refine (gm_res _ z _ hp _).trans ((gm_pull (𝟙 X₀) γ z (L.U m ⊓ L.U m') ⟨hm, hm'⟩ _).trans ?_)
  rw [Category.id_comp]

theorem grp₁ {M : Type} [CommGroup M] (G S W : M) (k : ℕ) :
    (G * S) ^ k * (G ^ (k : ℤ) * 1⁻¹ * W)⁻¹ = S ^ k * W⁻¹ := by
  rw [zpow_natCast, inv_one, mul_one, mul_pow, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]

theorem grp₂ {M : Type} [CommGroup M] (S Γ W : M) (k : ℕ) :
    S ^ k * ((1 : M) ^ (k : ℤ) * Γ⁻¹ * W)⁻¹ = Γ * (S ^ k * W⁻¹) := by
  rw [one_zpow, one_mul, mul_inv, inv_inv, mul_left_comm]

theorem frame_pull : ∀ (X X₀ : Scheme.{0}) (γ : X₀ ⟶ X) (H₀ : LB X₀) (s : LB.Sec H₀) (k : ℕ) (L : LB X), L.IsLB →
    H₀.IsLB → ∀ (w : LB.Iso (L.pull γ) (pw H₀ k)), w.IsGen → ∀ (D : X.Opens), γ ⁻¹ᵁ D = nonzeroLocus s →
    ∃ u : ∀ m : L.ι, Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, (∀ z m m', γ z ∈ D ⊓ L.U m → γ z ∈ D ⊓ L.U m' →
      gm (𝟙 X₀) z _ (u m) = gm γ z _ (L.g m m') * gm (𝟙 X₀) z _ (u m')) ∧
      ∀ z m a, γ z ∈ D ⊓ L.U m → z ∈ H₀.U a →
        gs (𝟙 X₀) z _ (s.f a) ^ k = (gm (𝟙 X₀) z _ (u m)).val * (gm (𝟙 X₀) z _ (w.s (a, fun _ => m))).val := by
  intro X X₀ γ H₀ s k L hL hH w hw D hD
  let W : L.ι → H₀.ι → X₀.Opens := fun m a => γ ⁻¹ᵁ (D ⊓ L.U m) ⊓ H₀.U a
  have hWb : ∀ m a, W m a ≤ X₀.basicOpen (s.f a) := fun m a z hz =>
    le_basicOpen s a ⟨hD ▸ (show z ∈ γ ⁻¹ᵁ D from hz.1.1), hz.2⟩
  have hWw : ∀ m a, W m a ≤ (LB.div (pw H₀ k) (L.pull γ)).U (a, fun _ => m) := fun m a z hz =>
    ⟨hz.2, mem_pull.2 hz.1.2⟩
  let S : ∀ m a, Γ(X₀, W m a)ˣ := fun m a => (isUnit_res_of_le (s.f a) (hWb m a)).unit
  let v : ∀ m a, Γ(X₀, W m a)ˣ := fun m a => S m a ^ k * (res (hWw m a) (w.s (a, fun _ => m)))⁻¹
  have hS : ∀ m a z (hz : z ∈ W m a), (gm (𝟙 X₀) z _ (S m a)).val = gs (𝟙 X₀) z _ (s.f a) := by
    intro m a z hz
    rw [← gs_unit _ z _ hz, IsUnit.unit_spec]
    exact gs_res _ z _ hz _
  have hv : ∀ m a z (hz : z ∈ W m a), gm (𝟙 X₀) z _ (v m a) =
      gm (𝟙 X₀) z _ (S m a) ^ k * (gm (𝟙 X₀) z _ (w.s (a, fun _ => m)))⁻¹ := by
    intro m a z hz
    simp only [v, map_mul, map_pow, map_inv]
    rw [gm_res _ z _ hz]

  have hwg : ∀ z a a' m m', z ∈ H₀.U a → z ∈ H₀.U a' → γ z ∈ L.U m → γ z ∈ L.U m' →
      gm (𝟙 X₀) z _ (w.s (a, fun _ => m)) = gm (𝟙 X₀) z (H₀.U a ⊓ H₀.U a') (H₀.g a a') ^ (k : ℤ) *
        (gm γ z _ (L.g m m'))⁻¹ * gm (𝟙 X₀) z _ (w.s (a', fun _ => m')) := by
    intro z a a' m m' ha ha' hm hm'
    rw [gm_gen_div hw z (a, fun _ => m) (a', fun _ => m') ⟨ha, mem_pull.2 hm⟩ ⟨ha', mem_pull.2 hm'⟩,
      gm_pull_g L γ z m m' hm hm']
    exact congrArg (fun t => t * _ * _) (map_zpow _ _ _)
  have hSg : ∀ m m' a a' z (hz : z ∈ W m a) (hz' : z ∈ W m' a'),
      gm (𝟙 X₀) z _ (S m a) = gm (𝟙 X₀) z (H₀.U a ⊓ H₀.U a') (H₀.g a a') * gm (𝟙 X₀) z _ (S m' a') := by
    intro m m' a a' z hz hz'
    apply Units.ext
    rw [Units.val_mul, hS m a z hz, hS m' a' z hz']
    exact gs_sec_chart s (𝟙 X₀) z hz.2 hz'.2
  have glue : ∀ m, ∃ t : Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, ∀ a, res (inf_le_left : W m a ≤ _) t = v m a := by
    intro m
    refine glue_unit (γ ⁻¹ᵁ (D ⊓ L.U m)) (W m) (fun a => inf_le_left) (fun z hz => ?_) (v m) ?_
    · obtain ⟨a, ha⟩ := exists_chart hH z
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, hz, ha⟩
    · intro a a' z hz
      rw [hv m a z hz.1, hv m a' z hz.2, hSg m m a a' z hz.1 hz.2,
        hwg z a a' m m hz.1.2 hz.2.2 hz.1.1.2 hz.1.1.2, gm_self hL γ z hz.1.1.2]
      exact grp₁ _ _ _ k
  choose u hu using glue
  have hug : ∀ m a z (hz : z ∈ W m a), gm (𝟙 X₀) z _ (u m) = gm (𝟙 X₀) z _ (v m a) := by
    intro m a z hz
    rw [← hu m a, gm_res _ z _ hz]
  refine ⟨u, fun z m m' hm hm' => ?_, fun z m a hm ha => ?_⟩
  · obtain ⟨a, ha⟩ := exists_chart hH z
    have hz : z ∈ W m a := ⟨hm, ha⟩
    have hz' : z ∈ W m' a := ⟨hm', ha⟩
    rw [hug m a z hz, hug m' a z hz', hv m a z hz, hv m' a z hz', hSg m m' a a z hz hz',
      gm_self hH (𝟙 X₀) z ha, one_mul, hwg z a a m m' ha ha hm.2 hm'.2, gm_self hH (𝟙 X₀) z ha]
    exact grp₂ _ _ _ k
  · have hz : z ∈ W m a := ⟨hm, ha⟩
    rw [hug m a z hz, hv m a z hz, ← hS m a z hz, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_mul_cancel_right]

end GlobalTheory.Div.FramePull
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_frames_of_pullback_power_on_nonzeroLocus : ∀ (X X₀ : Scheme.{0}) (γ : X₀ ⟶ X) (H₀ : LB X₀) (s : LB.Sec H₀) (k : ℕ) (L : LB X), L.IsLB → H₀.IsLB → ∀ (w : LB.Iso (L.pull γ) (pw H₀ k)), w.IsGen → ∀ (D : X.Opens), γ ⁻¹ᵁ D = nonzeroLocus s → ∃ u : ∀ m : L.ι, Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, (∀ z m m', γ z ∈ D ⊓ L.U m → γ z ∈ D ⊓ L.U m' → gm (𝟙 X₀) z _ (u m) = gm γ z _ (L.g m m') * gm (𝟙 X₀) z _ (u m')) ∧ ∀ z m a, γ z ∈ D ⊓ L.U m → z ∈ H₀.U a → gs (𝟙 X₀) z _ (s.f a) ^ k = (gm (𝟙 X₀) z _ (u m)).val * (gm (𝟙 X₀) z _ (w.s (a, fun _ => m))).val := by
  atlas_forward_decl GlobalTheory.Div.FramePull.frame_pull
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FramesBundle

theorem cg_cancel {G : Type} [CommGroup G] (a b c : G) : (a * b) * (a * c)⁻¹ = b * c⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem cg_cocycle {G : Type} [CommGroup G] (a b c : G) : (b * a⁻¹) * (c * b⁻¹) = c * a⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem cg_gen {G : Type} [CommGroup G] (a g c : G) : a⁻¹ = ((g * c) * a⁻¹ * g⁻¹) * c⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem frames_bundle : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (n : ℕ) (D : Fin (n + 1) → X.Opens), ⨆ i, D i = ⊤ → ∀ (τ : ∀ (i : Fin (n + 1)) (m : L.ι), Γ(X, D i ⊓ L.U m)ˣ), (∀ i x m m', x ∈ D i ⊓ L.U m → x ∈ D i ⊓ L.U m' → gm (𝟙 X) x _ (τ i m) = gm (𝟙 X) x _ (L.g m m') * gm (𝟙 X) x _ (τ i m')) → ∃ g : ∀ i j, Γ(X, D i ⊓ D j)ˣ, (⟨Fin (n + 1), D, g⟩ : LB X).IsLB ∧ LBIso L ⟨Fin (n + 1), D, g⟩ ∧ ∀ i j m, res (inf_le_left : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ D j) (g i j) = res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D j ⊓ L.U m) (τ j m) * (res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ L.U m) (τ i m))⁻¹ := by
  intro X L hL n D hD τ hτ
  have hg : ∀ i j, ∃ s : Γ(X, D i ⊓ D j)ˣ, ∀ m,
      res (inf_le_left : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ D j) s =
        res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D j ⊓ L.U m) (τ j m) *
          (res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ L.U m) (τ i m))⁻¹ := by
    intro i j
    refine glue_unit (D i ⊓ D j) (fun m => D i ⊓ D j ⊓ L.U m) (fun m => inf_le_left) ?_ _ ?_
    · intro x hx
      obtain ⟨m, hm⟩ := exists_chart hL x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨m, ⟨hx, hm⟩⟩
    · intro m m' x hx
      rw [map_mul, map_mul, map_inv, map_inv, gm_res _ x _ hx.1, gm_res _ x _ hx.1, gm_res _ x _ hx.2,
        gm_res _ x _ hx.2, hτ j x m m' ⟨hx.1.1.2, hx.1.2⟩ ⟨hx.2.1.2, hx.2.2⟩,
        hτ i x m m' ⟨hx.1.1.1, hx.1.2⟩ ⟨hx.2.1.1, hx.2.2⟩, cg_cancel]
  choose g hg' using hg
  have key : ∀ i j m x, x ∈ D i ⊓ D j ⊓ L.U m →
      gm (𝟙 X) x (D i ⊓ D j) (g i j) = gm (𝟙 X) x (D j ⊓ L.U m) (τ j m) * (gm (𝟙 X) x (D i ⊓ L.U m) (τ i m))⁻¹ := by
    intro i j m x hx
    rw [← gm_res _ x (inf_le_left : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ D j) hx, hg' i j m, map_mul, map_inv,
      gm_res _ x _ hx, gm_res _ x _ hx]
  refine ⟨g, ⟨hD, ?_, ?_⟩, ⟨⟨fun p => (τ p.1 p.2)⁻¹⟩, ?_⟩, hg'⟩
  · intro i
    apply unit_ext
    intro x hx
    rw [gm_res _ x _ hx, map_one]
    obtain ⟨m, hm⟩ := exists_chart hL x
    exact (key i i m x ⟨⟨hx, hx⟩, hm⟩).trans (mul_inv_cancel _)
  · intro i j k
    apply unit_ext
    intro x hx
    rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx]
    obtain ⟨m, hm⟩ := exists_chart hL x
    have h1 := key i j m x ⟨⟨hx.1.1, hx.1.2⟩, hm⟩
    have h2 := key j k m x ⟨⟨hx.1.2, hx.2⟩, hm⟩
    have h3 := key i k m x ⟨⟨hx.1.1, hx.2⟩, hm⟩
    exact (congrArg₂ (· * ·) h1 h2).trans ((cg_cocycle _ _ _).trans h3.symm)
  · rintro ⟨i, m⟩ ⟨j, m'⟩
    apply unit_ext
    intro x hx
    have hx' : x ∈ D i ⊓ L.U m ⊓ (D j ⊓ L.U m') := hx
    have eL : ∀ h : D i ⊓ L.U m ⊓ (D j ⊓ L.U m') ≤ D i ⊓ L.U m,
        gm (𝟙 X) x (D i ⊓ L.U m ⊓ (D j ⊓ L.U m')) (res h (τ i m)⁻¹) = (gm (𝟙 X) x _ (τ i m))⁻¹ := by
      intro h
      rw [map_inv, map_inv, gm_res _ x _ hx']
    have eR : ∀ (h1 : D i ⊓ L.U m ⊓ (D j ⊓ L.U m') ≤ D i ⊓ D j) (h2 : D i ⊓ L.U m ⊓ (D j ⊓ L.U m') ≤ L.U m ⊓ L.U m')
        (h3 : D i ⊓ L.U m ⊓ (D j ⊓ L.U m') ≤ D j ⊓ L.U m'),
        gm (𝟙 X) x (D i ⊓ L.U m ⊓ (D j ⊓ L.U m')) (res h1 (g i j) * (res h2 (L.g m m'))⁻¹ * res h3 (τ j m')⁻¹) =
          gm (𝟙 X) x _ (g i j) * (gm (𝟙 X) x _ (L.g m m'))⁻¹ * (gm (𝟙 X) x _ (τ j m'))⁻¹ := by
      intro h1 h2 h3
      rw [map_mul, map_mul, map_inv, map_inv, map_inv, gm_res _ x _ hx', gm_res _ x _ hx', gm_res _ x _ hx']
    have h1 := key i j m x ⟨⟨hx'.1.1, hx'.2.1⟩, hx'.1.2⟩
    have h2 := hτ j x m m' ⟨hx'.2.1, hx'.1.2⟩ ⟨hx'.2.1, hx'.2.2⟩
    refine (eL _).trans (Eq.trans ?_ (eR _ _ _).symm)
    rw [h1, h2]
    exact cg_gen _ _ _

end GlobalTheory.FramesBundle
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_lineBundle_of_compatible_local_frames : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (n : ℕ) (D : Fin (n + 1) → X.Opens), ⨆ i, D i = ⊤ → ∀ (τ : ∀ (i : Fin (n + 1)) (m : L.ι), Γ(X, D i ⊓ L.U m)ˣ), (∀ i x m m', x ∈ D i ⊓ L.U m → x ∈ D i ⊓ L.U m' → gm (𝟙 X) x _ (τ i m) = gm (𝟙 X) x _ (L.g m m') * gm (𝟙 X) x _ (τ i m')) → ∃ g : ∀ i j, Γ(X, D i ⊓ D j)ˣ, (⟨Fin (n + 1), D, g⟩ : LB X).IsLB ∧ LBIso L ⟨Fin (n + 1), D, g⟩ ∧ ∀ i j m, res (inf_le_left : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ D j) (g i j) = res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D j ⊓ L.U m) (τ j m) * (res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ L.U m) (τ i m))⁻¹ := by
  atlas_forward_decl GlobalTheory.FramesBundle.frames_bundle
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem GlobalTheory.FormalAlg.exists_chart_cocycle_of_pull : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (H₀ : LB (Y 0).left) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → ((∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m)) → ∀ γ : ∀ e, (Y 0).left ⟶ (Y e).left, γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e k : ℕ) (L : LB (Y e).left), L.IsLB → LBIso (L.pull (γ e)) (GlobalTheory.AbLaw.pw H₀ k) → ∃ g : ∀ i j, Γ((Y e).left, C.D e i ⊓ C.D e j)ˣ, (⟨Fin (n + 1), C.D e, g⟩ : LB (Y e).left).IsLB ∧ LBIso L ⟨Fin (n + 1), C.D e, g⟩ ∧ ∀ i j, (g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k ∈ towerIdeal Y e I (C.D e i ⊓ C.D e j) := by
  rintro R _ I Y β hβ n C H₀ s₀ hH₀ ⟨hD, hρs⟩ γ hγ0 hγs e k L hL ⟨w, hw⟩
  have hpb : IsPullback (γ e) (Y 0).hom ((Y e).hom ≫ thick R I e) (thick R I 0) :=
    (GlobalTheory.T.isPullback_thick_tower_squares R I Y β hβ).2 γ hγ0 hγs e
  have hsurj : ∀ e, Surjective (γ e) := by
    intro e
    induction e with
    | zero => rw [hγ0]; infer_instance
    | succ e ih =>
      rw [← hγs e]
      have := MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip (GlobalTheory.GenSystem.surjective_thickTrans R I e)
      infer_instance
  have hpre := fun i => GlobalTheory.T.thickeningTowerCharts_preimage_and_germ_pullback R I Y β n C γ hγ0 hγs e i
  have hu := fun i => GlobalTheory.T.exists_local_frames_of_pullback_power_on_nonzeroLocus _ _ (γ e) H₀ (s₀ i) k L hL hH₀ w hw (C.D e i) ((hpre i).1.trans (hD i))
  choose u hu1 hu2 using hu
  have ht := fun i => GlobalTheory.T.lift_local_units_along_nilpotent_thickening R (I ^ (0 + 1)) (Y e).left (Y 0).left ((Y e).hom ≫ thick R I e) (γ e) (Y 0).hom
    hpb (hsurj e) L hL (C.D e i) (C.aff e i) (u i) (hu1 i)
  choose τ hτ1 hτ2 using ht
  obtain ⟨g, hgLB, hgIso, hg⟩ := GlobalTheory.T.cech_lineBundle_of_compatible_local_frames (Y e).left L hL n (C.D e) (C.cover e) τ hτ2
  refine ⟨g, hgLB, hgIso, fun i j => ?_⟩
  have hVaff : IsAffineOpen (C.D e i ⊓ C.D e j) := by
    have := (C.aff e i).basicOpen (C.ρ e i j)
    rwa [(GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hβ n C).1 e i j] at this
  obtain ⟨-, -, hker⟩ := GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (0 + 1)) (Y e).left (Y 0).left ((Y e).hom ≫ thick R I e) (γ e) (Y 0).hom hpb
  have hk := (hker _ hVaff).2

  have hτu : ∀ i m z (hz : γ e z ∈ C.D e i ⊓ L.U m), gm (γ e) z _ (τ i m) = gm (𝟙 _) z _ (u i m) := by
    intro i m z hz
    have h1 := gm_pull (𝟙 _) (γ e) z _ hz (τ i m)
    rw [Category.id_comp] at h1
    rw [← h1]
    congr 1
    exact Units.ext (hτ1 i m)
  have hmem : (g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k ∈
      RingHom.ker ((γ e).app (C.D e i ⊓ C.D e j)).hom := by
    rw [RingHom.mem_ker]
    apply fn_ext
    intro z hz
    have hz' : γ e z ∈ C.D e i ⊓ C.D e j := hz
    obtain ⟨m, hm⟩ := exists_chart hL (γ e z)
    obtain ⟨a, ha⟩ := exists_chart hH₀ z
    have hzi : z ∈ C.D 0 i := (hpre i).1 ▸ hz'.1
    have hzj : z ∈ C.D 0 j := (hpre j).1 ▸ hz'.2
    have hm3 : γ e z ∈ C.D e i ⊓ C.D e j ⊓ L.U m := ⟨hz', hm⟩

    have hgz : gs (γ e) z _ (g i j).val = (gm (𝟙 _) z _ (u j m)).val * ((gm (𝟙 _) z _ (u i m))⁻¹).val := by
      rw [gs_unit _ z _ hz', ← gm_res (γ e) z (inf_le_left : C.D e i ⊓ C.D e j ⊓ L.U m ≤ C.D e i ⊓ C.D e j) hm3,
        hg i j m, map_mul, map_inv, gm_res _ z _ hm3, gm_res _ z _ hm3, hτu j m z ⟨hz'.2, hm⟩,
        hτu i m z ⟨hz'.1, hm⟩, Units.val_mul]

    have hsj := hu2 j z m a ⟨hz'.2, hm⟩ ha
    have hsi := hu2 i z m a ⟨hz'.1, hm⟩ ha
    have hrel : gs (𝟙 _) z _ ((s₀ j).f a) = gs (𝟙 _) z _ (C.ρ 0 i j) * gs (𝟙 _) z _ ((s₀ i).f a) := by
      have h := congrArg (gs (𝟙 _) z (C.D 0 i ⊓ H₀.U a)) (hρs i j a)
      have hmz : (𝟙 (Y 0).left) z ∈ C.D 0 i ⊓ H₀.U a := ⟨hzi, ha⟩
      rwa [gs_mul _ z _ hmz, gs_res _ z _ hmz, gs_res _ z _ hmz, gs_res _ z _ hmz] at h
    have hρz : gs (γ e) z _ (rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k) =
        gs (𝟙 _) z _ (C.ρ 0 i j) ^ k := by
      rw [gs_eq _ z _ hz', map_pow, map_pow, ← gs_eq _ z _ hz', gs_res _ z _ hz', (hpre i).2 j z hzi]
    have hu' : (gm (𝟙 _) z _ (u j m)).val = gs (𝟙 _) z _ (C.ρ 0 i j) ^ k * (gm (𝟙 _) z _ (u i m)).val := by
      have hW := (gm (𝟙 (Y 0).left) z _ (w.s (a, fun _ => m))).isUnit
      apply hW.mul_left_cancel
      rw [mul_comm _ (gm (𝟙 _) z _ (u j m)).val, ← hsj, hrel, mul_pow, hsi]
      ring
    have hsub := gs_pull (𝟙 _) (γ e) z (C.D e i ⊓ C.D e j) hz' ((g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k)
    rw [Category.id_comp] at hsub
    have h0 : gs (𝟙 _) z (γ e ⁻¹ᵁ (C.D e i ⊓ C.D e j)) 0 = 0 := by rw [gs_eq _ z _ hz, map_zero, map_zero]
    rw [h0, hsub, gs_eq _ z _ hz', map_sub, map_sub, ← gs_eq _ z _ hz', ← gs_eq _ z _ hz', hgz, hρz, hu']
    rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one, sub_self]
  rw [hk] at hmem
  simpa only [towerIdeal, zero_add, pow_one] using hmem
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chart_cocycle_of_pullback_power_standard : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (H₀ : LB (Y 0).left) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → ((∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m)) → ∀ γ : ∀ e, (Y 0).left ⟶ (Y e).left, γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e k : ℕ) (L : LB (Y e).left), L.IsLB → LBIso (L.pull (γ e)) (GlobalTheory.AbLaw.pw H₀ k) → ∃ g : ∀ i j, Γ((Y e).left, C.D e i ⊓ C.D e j)ˣ, (⟨Fin (n + 1), C.D e, g⟩ : LB (Y e).left).IsLB ∧ LBIso L ⟨Fin (n + 1), C.D e, g⟩ ∧ ∀ i j, (g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k ∈ towerIdeal Y e I (C.D e i ⊓ C.D e j) := by
  atlas_forward_decl GlobalTheory.FormalAlg.exists_chart_cocycle_of_pull
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg.LiftCech

variable {R : Type} [CommRing R]

theorem map_cst_rs {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (J : Ideal R) {U V : X.Opens}
    (h : V ≤ U) {x : Γ(X, U)} (hx : x ∈ J.map (cst f U)) : rs X h x ∈ J.map (cst f V) := by
  have h' := Ideal.mem_map_of_mem (rs X h) hx
  rw [Ideal.map_map] at h'
  have e : (rs X h).comp (cst f U) = cst f V := RingHom.ext fun r => rs_cst f h r
  rwa [e] at h'

theorem gs_sub' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by
  simp only [gs_eq f y U h, map_sub]

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs
  split <;> simp

end GlobalTheory.FormalAlg.LiftCech

open GlobalTheory.FormalAlg.LiftCech in

theorem GlobalTheory.FormalAlg.lift_cech : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e k : ℕ), (∀ c : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j), (∀ i j, c i j ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) → (∀ i j l, rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (c i j) + rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) l) (c i l)) → ∃ a : ∀ i, Γ((Y (e + 1)).left, C.D (e + 1) i), (∀ i, a i ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) ∧ ∀ i j, c i j = rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (a i) - rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j)) → ∀ g : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j)ˣ, (⟨Fin (n + 1), C.D (e + 1), g⟩ : LB (Y (e + 1)).left).IsLB → (∀ i j, (g i j).val - rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k ∈ towerIdeal Y (e + 1) I _) → ∀ σ : ∀ i, Γ((Y e).left, β e ⁻¹ᵁ C.D (e + 1) i), (∀ z i j, β e z ∈ C.D (e + 1) i → β e z ∈ C.D (e + 1) j → gs (𝟙 _) z _ (σ i) = gs (β e) z _ (g i j).val * gs (𝟙 _) z _ (σ j)) → ∃ σ' : LB.Sec (⟨Fin (n + 1), C.D (e + 1), g⟩ : LB (Y (e + 1)).left), ∀ i, ((β e).app (C.D (e + 1) i)).hom (σ'.f i) = σ i := by
  intro R _ I Y β hβ n C e k hH g hg hgρ σ hσ
  have hbp := (GlobalTheory.T.isPullback_thick_tower_squares R I Y β hβ).1 e
  have hk := GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (e + 1)) _ _ _ (β e) (Y e).hom hbp
  have hbas := (GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hβ n C).1 (e + 1)
  have hz := (GlobalTheory.T.thickeningTower_liftedRatios_generate_surjective R I Y β hβ n C).1 (e + 1)
  have hA : ∀ i j, IsAffineOpen (C.D (e + 1) i ⊓ C.D (e + 1) j) := fun i j =>
    hbas i j ▸ (C.aff (e + 1) i).basicOpen _
  have hker : ∀ (V : (Y (e + 1)).left.Opens), IsAffineOpen V → ∀ x,
      ((β e).app V).hom x = 0 ↔ x ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) V := fun V hV x => by
    rw [← RingHom.mem_ker, (hk.2.2 V hV).2]; rfl
  have hmem : ∀ (J : Ideal R) {U V : (Y (e + 1)).left.Opens} (h : V ≤ U) {x : Γ((Y (e + 1)).left, U)},
      x ∈ towerIdeal Y (e + 1) J U → rs (Y (e + 1)).left h x ∈ towerIdeal Y (e + 1) J V :=
    fun J _ _ h _ hx => map_cst_rs _ J h hx
  have hmul : ∀ (V : (Y (e + 1)).left.Opens) (x y : Γ((Y (e + 1)).left, V)), x ∈ towerIdeal Y (e + 1) I V →
      y ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) V → x * y = 0 := by
    intro V x y hx hy
    have h := Ideal.mul_mem_mul hx hy
    unfold towerIdeal at h
    rw [← Ideal.map_mul, ← pow_succ'] at h
    have h0 := hz V
    unfold towerIdeal at h0
    rw [h0] at h
    exact (Submodule.mem_bot _).1 h
  choose τ hτ using fun i => (hk.2.2 _ (C.aff (e + 1) i)).1 (σ i)
  have key : ∀ (x : (Y e).left) i, β e x ∈ C.D (e + 1) i →
      gs (β e) x (C.D (e + 1) i) (τ i) = gs (𝟙 _) x _ (σ i) := fun x i hxi => by
    rw [← hτ i, gs_pull (𝟙 _) (β e) x _ hxi, Category.id_comp]
  let c : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j) := fun i j =>
    rs _ (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (τ i) -
      (g i j).val * rs _ (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (τ j)
  have hcdef : ∀ i j, c i j = rs _ (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (τ i) -
      (g i j).val * rs _ (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (τ j) := fun _ _ => rfl
  have hc : ∀ i j, c i j ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _ := by
    intro i j
    rw [← hker _ (hA i j)]
    apply fn_ext
    intro x hx
    have hxi : β e x ∈ C.D (e + 1) i := hx.1
    have hxj : β e x ∈ C.D (e + 1) j := hx.2
    rw [gs_pull (𝟙 _) (β e) x _ hx, Category.id_comp, gs_zero',
      hcdef, gs_sub' _ _ _ hx, gs_mul _ _ _ hx, gs_res _ _ _ hx, gs_res _ _ _ hx, key x i hxi, key x j hxj,
      hσ x i j hxi hxj, sub_self]
  have hcoc : ∀ i j l, rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (c i j) + rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) l) (c i l) := by
    intro i j l
    have h1 : rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (g i j).val * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) := by
      rw [← sub_eq_zero, ← sub_mul]
      refine hmul _ _ _ ?_ (hmem _ _ (hc j l))
      have h := hmem I (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (hgρ i j)
      rwa [map_sub, map_pow, rs_rs] at h
    have hco := congrArg Units.val (hg.cocycle i j l)
    simp only [res, Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at hco
    rw [← h1, hcdef, hcdef, hcdef]
    simp only [map_sub, map_mul, rs_rs]
    linear_combination (-(rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) l) (τ l))) * hco
  obtain ⟨a, ha, hca⟩ := hH c hc hcoc
  refine ⟨⟨fun i => τ i - a i, fun i j => ?_⟩, fun i => ?_⟩
  · have h2 : (g i j).val * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j) = rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j) := by
      rw [← sub_eq_zero, ← sub_mul]
      exact hmul _ _ _ (hgρ i j) (hmem _ _ (ha j))
    have h3 := hca i j
    rw [hcdef] at h3
    change rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (τ i - a i) = (g i j).val * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (τ j - a j)
    rw [map_sub, map_sub]
    linear_combination h3 + h2
  · change ((β e).app (C.D (e + 1) i)).hom (τ i - a i) = σ i
    rw [map_sub, hτ i, (hker _ (C.aff (e + 1) i) (a i)).2 (ha i), sub_zero]
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_sections_next_thickening_standardCharts : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e k : ℕ), (∀ c : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j), (∀ i j, c i j ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) → (∀ i j l, rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (c i j) + rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) l) (c i l)) → ∃ a : ∀ i, Γ((Y (e + 1)).left, C.D (e + 1) i), (∀ i, a i ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) ∧ ∀ i j, c i j = rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (a i) - rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j)) → ∀ g : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j)ˣ, (⟨Fin (n + 1), C.D (e + 1), g⟩ : LB (Y (e + 1)).left).IsLB → (∀ i j, (g i j).val - rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k ∈ towerIdeal Y (e + 1) I _) → ∀ σ : ∀ i, Γ((Y e).left, β e ⁻¹ᵁ C.D (e + 1) i), (∀ z i j, β e z ∈ C.D (e + 1) i → β e z ∈ C.D (e + 1) j → gs (𝟙 _) z _ (σ i) = gs (β e) z _ (g i j).val * gs (𝟙 _) z _ (σ j)) → ∃ σ' : LB.Sec (⟨Fin (n + 1), C.D (e + 1), g⟩ : LB (Y (e + 1)).left), ∀ i, ((β e).app (C.D (e + 1) i)).hom (σ'.f i) = σ i := by
  atlas_forward_decl GlobalTheory.FormalAlg.lift_cech
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.FormalAlg

theorem glue_chart {X X' : Scheme.{0}} (φ : X' ⟶ X) {M L' : LB X} {L : LB X'} (ω : LB.Iso L' M)
    (hω : ω.IsGen) (u : LB.Iso L (L'.pull φ)) (hu : PGen u) (hM : M.IsLB) (hL' : L'.IsLB) (hL : L.IsLB)
    (σ : LB.Sec L) (i : M.ι) :
    ∃ a : Γ(X', φ ⁻¹ᵁ M.U i), ∀ z b c, φ z ∈ M.U i → φ z ∈ L'.U b → z ∈ L.U c →
      gs (𝟙 _) z _ a = (gv ω φ z i b).val * ((gw u (𝟙 _) z b c).val * gs (𝟙 _) z _ (σ.f c)) := by
  let W : L'.ι × L.ι → X'.Opens := fun p => φ ⁻¹ᵁ (M.U i ⊓ L'.U p.1) ⊓ L.U p.2
  have l₀ : ∀ p, W p ≤ φ ⁻¹ᵁ M.U i := fun p x hx => hx.1.1
  have l₁ : ∀ p, W p ≤ φ ⁻¹ᵁ (M.U i ⊓ L'.U p.1) := fun p x hx => hx.1
  have l₂ : ∀ p, W p ≤ (L'.pull φ).U (fun _ => p.1) ⊓ L.U p.2 := fun p x hx => ⟨mem_pull.2 hx.1.2, hx.2⟩
  have l₃ : ∀ p, W p ≤ L.U p.2 := fun p x hx => hx.2
  have key : ∀ (y : X') (b b' : L'.ι) (c c' : L.ι), φ y ∈ M.U i → φ y ∈ L'.U b → φ y ∈ L'.U b' →
      y ∈ L.U c → y ∈ L.U c' →
      (gv ω φ y i b).val * ((gw u (𝟙 _) y b c).val * gs (𝟙 _) y _ (σ.f c)) =
        (gv ω φ y i b').val * ((gw u (𝟙 _) y b' c').val * gs (𝟙 _) y _ (σ.f c')) := by
    intro y b b' c c' hi hb hb' hc hc'
    have h1 := gm_isGen hω φ y i i b b' hi hi hb hb'
    have h2 := hu X' (𝟙 _) y b b' c c' hb hb' hc hc'
    have h3 := GlobalTheory.SecPullIso.gs_sec_trans σ (𝟙 _) y hc hc'
    rw [gm_self hM φ y hi, one_mul] at h1
    rw [Category.id_comp] at h2
    rw [h1, h2, h3]
    generalize gm φ y _ (L'.g b b') = B
    generalize gm (𝟙 X') y _ (L.g c c') = C
    generalize gv ω φ y i b' = D
    generalize gw u (𝟙 _) y b' c' = E
    generalize gs (𝟙 X') y _ (σ.f c') = s
    simp only [Units.val_mul]
    have hB := B.inv_mul
    have hC := C.inv_mul
    linear_combination ((D : _) * E * s * (C⁻¹ : _ˣ) * C) * hB + ((D : _) * E * s) * hC
  obtain ⟨v, hv⟩ : ∃ v : ∀ p, Γ(X', W p), ∀ z p, z ∈ W p →
      gs (𝟙 _) z (W p) (v p) = (gv ω φ z i p.1).val * ((gw u (𝟙 _) z p.1 p.2).val * gs (𝟙 _) z _ (σ.f p.2)) :=
    ⟨fun p => (res (l₁ p) (pullU φ _ (ω.s (i, p.1)))).val * ((res (l₂ p) (u.s (fun _ => p.1, p.2))).val *
        (X'.presheaf.map (homOfLE (l₃ p)).op).hom (σ.f p.2)), fun z p hz => by
      rw [gs_mul _ z _ hz, gs_mul _ z _ hz, gs_unit _ z _ hz, gs_unit _ z _ hz, gm_res (𝟙 X') z (l₁ p) hz,
        show gm (𝟙 X') z (W p) (res (l₂ p) (u.s (fun _ => p.1, p.2))) = gw u (𝟙 _) z p.1 p.2 from gm_res (𝟙 X') z (l₂ p) hz _, gs_res (𝟙 X') z (l₃ p) hz, show gm (𝟙 X') z (φ ⁻¹ᵁ (M.U i ⊓ L'.U p.1)) (pullU φ _ (ω.s (i, p.1))) = gv ω φ z i p.1 from
          (gm_pull (𝟙 _) φ z _ (l₁ p hz) _).trans (by rw [Category.id_comp]; rfl)]⟩
  obtain ⟨a, ha, -⟩ := X'.sheaf.existsUnique_gluing' W (φ ⁻¹ᵁ M.U i) (fun p => homOfLE (l₀ p)) (fun y hy => by
      obtain ⟨b, hb⟩ := exists_chart hL' (φ y)
      obtain ⟨c, hc⟩ := exists_chart hL y
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(b, c), ⟨hy, hb⟩, hc⟩) v
    (fun p q => fn_ext (V := W p ⊓ W q) fun y hy => by
      refine (gs_res (𝟙 _) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 _) y inf_le_right hy _).symm)
      rw [hv y p hy.1, hv y q hy.2]
      exact key y p.1 q.1 p.2 q.2 hy.1.1.1 hy.1.1.2 hy.2.1.2 hy.1.2 hy.2.2)
  refine ⟨a, fun z b c h₁ h₂ h₃ => ?_⟩
  have hz : z ∈ W (b, c) := ⟨⟨h₁, h₂⟩, h₃⟩
  exact (gs_res (𝟙 _) z (l₀ (b, c)) hz a).symm.trans ((congrArg (gs (𝟙 _) z (W (b, c))) (ha (b, c))).trans
    (hv z (b, c) hz))

theorem lift_step : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (H₀ : LB (Y 0).left) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → ((∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m)) → ∀ γ : ∀ e, (Y 0).left ⟶ (Y e).left, γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e k : ℕ), (∀ c : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j), (∀ i j, c i j ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) → (∀ i j l, rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (c i j) + rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) l) (c i l)) → ∃ a : ∀ i, Γ((Y (e + 1)).left, C.D (e + 1) i), (∀ i, a i ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) ∧ ∀ i j, c i j = rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (a i) - rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j)) → ∀ (L : LB (Y e).left) (L' : LB (Y (e + 1)).left) (u : LB.Iso L (L'.pull (β e))), L.IsLB → L'.IsLB → u.IsGen → LBIso (L'.pull (γ (e + 1))) (GlobalTheory.AbLaw.pw H₀ k) → ∀ σ : LB.Sec L, ∃ σ' : LB.Sec L', Rel (β e) u σ' σ := by
  intro R _ I Y β hβ n C H₀ s₀ hH₀ hs₀ γ hγ0 hγ e k hc L L' u hL hL' hu hpw σ
  obtain ⟨g, hMLB, ⟨ω, hω⟩, hcong⟩ := GlobalTheory.T.exists_chart_cocycle_of_pullback_power_standard R I Y β hβ n C H₀ s₀ hH₀ hs₀ γ hγ0 hγ (e + 1) k L' hL' hpw
  have hup : PGen u := (isGen_iff u).1 hu
  choose σi hσi using fun i => glue_chart (M := (⟨Fin (n + 1), C.D (e + 1), g⟩ : LB (Y (e + 1)).left)) (β e) ω hω u
    hup hMLB hL' hL σ i
  have hcoc : ∀ z i j, β e z ∈ C.D (e + 1) i → β e z ∈ C.D (e + 1) j →
      gs (𝟙 _) z _ (σi i) = gs (β e) z _ (g i j).val * gs (𝟙 _) z _ (σi j) := by
    intro z i j hi hj
    obtain ⟨b, hb⟩ := exists_chart hL' (β e z)
    obtain ⟨c, hc'⟩ := exists_chart hL z
    rw [hσi i z b c hi hb hc', hσi j z b c hj hb hc']
    have h1 := gm_isGen hω (β e) z i j b b hi hj hb hb
    rw [gm_self hL' (β e) z hb, inv_one, mul_one] at h1
    rw [h1, gs_unit (β e) z (C.D (e + 1) i ⊓ C.D (e + 1) j) ⟨hi, hj⟩, Units.val_mul, mul_assoc]
  obtain ⟨σ'', hσ''⟩ := GlobalTheory.T.lift_sections_next_thickening_standardCharts R I Y β hβ n C e k hc g hMLB hcong σi hcoc
  let w := isoPullId ω (F := 𝟙 _) rfl
  have hw : w.IsGen := (isGen_iff w).2 (isoPullId_pgen hω rfl)
  obtain ⟨σ', hσ'⟩ := GlobalTheory.SecPullIso.exists_pull (𝟙 _) _ L' w hMLB hL' hw σ''
  refine ⟨σ', fun z b c hb hc' => ?_⟩
  obtain ⟨i, hi⟩ := exists_chart hMLB (β e z)
  have hR : Rel (𝟙 _) w σ'' σ' := hσ'
  have e1 := hR.pull (β e) z i b hi hb
  rw [Category.comp_id, gw_isoPullId ω rfl (β e) z i b hi hb] at e1
  have e2 : gs (β e) z _ (σ''.f i) = gs (𝟙 _) z _ (σi i) := by
    rw [← hσ'' i, gs_pull (𝟙 _) (β e) z _ hi, Category.id_comp]
  rw [e2, hσi i z b c hi hb hc'] at e1
  exact ((Units.mul_right_inj (gv ω (β e) z i b)).1 e1).symm

end GlobalTheory.FormalAlg
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickeningTower_lift_sections_one_level : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (H₀ : LB (Y 0).left) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → ((∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m)) → ∀ γ : ∀ e, (Y 0).left ⟶ (Y e).left, γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e k : ℕ), (∀ c : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j), (∀ i j, c i j ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) → (∀ i j l, rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (c i j) + rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) l) (c i l)) → ∃ a : ∀ i, Γ((Y (e + 1)).left, C.D (e + 1) i), (∀ i, a i ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) ∧ ∀ i j, c i j = rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (a i) - rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j)) → ∀ (L : LB (Y e).left) (L' : LB (Y (e + 1)).left) (u : LB.Iso L (L'.pull (β e))), L.IsLB → L'.IsLB → u.IsGen → LBIso (L'.pull (γ (e + 1))) (GlobalTheory.AbLaw.pw H₀ k) → ∀ σ : LB.Sec L, ∃ σ' : LB.Sec L', Rel (β e) u σ' σ := by
  atlas_forward_decl GlobalTheory.FormalAlg.lift_step
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

namespace GlobalTheory.FormalAlg

theorem exists_lift_sections_tower : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H₀ : LB (Y 0).left) (n : ℕ) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → VeryAmpleBy (Y 0).hom H₀ s₀ → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ (L : ∀ e, LB (Y e).left) (u : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e))), (∀ e, (L e).IsLB ∧ (u e).IsGen) → LBIso (L 0) (GlobalTheory.AbLaw.pw H₀ k) → ∀ σ₀ : LB.Sec (L 0), ∃ σ : ∀ e, LB.Sec (L e), σ 0 = σ₀ ∧ ∀ e, Rel (β e) (u e) (σ (e + 1)) (σ e) := by
  intro R _ _ I Y β hY H₀ n s₀ hH hva
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_standard_charts_formalTower_of_veryAmple R I Y β hY H₀ n s₀ hH hva
  obtain ⟨k₀, hk₀⟩ := GlobalTheory.T.thickening_tower_cech_h1_uniform R I Y β hY n C
  refine ⟨k₀, fun k hk L u hL hL0 σ₀ => ?_⟩
  let γ : ∀ e, (Y 0).left ⟶ (Y e).left := fun e =>
    Nat.rec (motive := fun e => (Y 0).left ⟶ (Y e).left) (𝟙 _) (fun e g => g ≫ β e) e
  have hγs : ∀ e, γ e ≫ β e = γ (e + 1) := fun e => rfl
  have hP : (GlobalTheory.AbLaw.pw H₀ k).IsLB := isLB_pw hH _
  have hiso : ∀ e, LBIso ((L e).pull (γ e)) (GlobalTheory.AbLaw.pw H₀ k) := by
    intro e
    induction e with
    | zero => exact LBIso.chartPull (chartPullPull (L 0) (𝟙 _)) (chartPullId _) hL0
    | succ e ih =>
      refine LBIso.trans (pull_isLB (hL (e + 1)).1 _) (pull_isLB (hL e).1 _) hP ?_ ih
      exact LBIso.chartPull (chartPullSame (L (e + 1)) (fun _ => γ (e + 1)) (fun _ => β e) (fun _ => 1) (γ e)
        (fun _ => rfl)) (chartPullPull (L e) (γ e)) (LBIso.symm ⟨u e, (hL e).2⟩)
  have step : ∀ e (σ : LB.Sec (L e)), ∃ σ' : LB.Sec (L (e + 1)), Rel (β e) (u e) σ' σ := fun e σ =>
    GlobalTheory.T.thickeningTower_lift_sections_one_level R I Y β hY n C H₀ s₀ hH hC γ rfl hγs e k (hk₀ k hk (e + 1)) (L e) (L (e + 1)) (u e)
      (hL e).1 (hL (e + 1)).1 (hL e).2 (hiso (e + 1)) σ
  choose f hf using step
  let σ : ∀ e, LB.Sec (L e) := fun e => Nat.rec (motive := fun e => LB.Sec (L e)) σ₀ (fun e s => f e s) e
  exact ⟨σ, rfl, fun e => hf e (σ e)⟩

end GlobalTheory.FormalAlg
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniform_lift_sections_thickeningTower : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H₀ : LB (Y 0).left) (n : ℕ) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → VeryAmpleBy (Y 0).hom H₀ s₀ → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ (L : ∀ e, LB (Y e).left) (u : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e))), (∀ e, (L e).IsLB ∧ (u e).IsGen) → LBIso (L 0) (GlobalTheory.AbLaw.pw H₀ k) → ∀ σ₀ : LB.Sec (L 0), ∃ σ : ∀ e, LB.Sec (L e), σ 0 = σ₀ ∧ ∀ e, Rel (β e) (u e) (σ (e + 1)) (σ e) := by
  atlas_forward_decl GlobalTheory.FormalAlg.exists_lift_sections_tower
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.GenTwist
variable {X : Scheme.{0}} {M H : LB X}

theorem tw_one_g (p q : M.ι) (k l : H.ι) :
    (((tw M H 1).g (p, k) (q, l) : Γ(X, (tw M H 1).U (p, k) ⊓ (tw M H 1).U (q, l))ˣ) :
      Γ(X, (tw M H 1).U (p, k) ⊓ (tw M H 1).U (q, l))) =
    rs X (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
      M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U p ⊓ M.U q) (M.g p q) *
    rs X (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ H.U k ⊓ H.U l) (H.g k l) := by
  have e : (tw M H 1).g (p, k) (q, l) = (res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
      M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U p ⊓ M.U q) (M.g p q) *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ H.U k ⊓ H.U l) (H.g k l ^ (-(1 : ℤ))))⁻¹ :
        Γ(X, M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l))ˣ) := rfl
  rw [e, map_zpow, zpow_neg, zpow_one, inv_inv]
  rfl

def prodSec (u : LB.Sec M) (s : LB.Sec H) : LB.Sec (tw M H 1) where
  f := fun pk => rs X (inf_le_left : M.U pk.1 ⊓ H.U pk.2 ≤ M.U pk.1) (u.f pk.1) *
    rs X (inf_le_right : M.U pk.1 ⊓ H.U pk.2 ≤ H.U pk.2) (s.f pk.2)
  compat := fun pk ql => by
    have key : ∀ (p q : M.ι) (k l : H.ι),
        rs X (inf_le_left : M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U p ⊓ H.U k)
          (rs X inf_le_left (u.f p) * rs X inf_le_right (s.f k)) =
        (rs X (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U p ⊓ M.U q) (M.g p q) *
         rs X (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ H.U k ⊓ H.U l) (H.g k l)) *
        rs X (inf_le_right : M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U q ⊓ H.U l)
          (rs X inf_le_left (u.f q) * rs X inf_le_right (s.f l)) := by
      intro p q k l
      have hu := congrArg (rs X (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U p ⊓ M.U q)) (u.compat p q)
      have hs := congrArg (rs X (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ H.U k ⊓ H.U l)) (s.compat k l)
      simp only [rs_rs, map_mul] at hu hs ⊢
      rw [hu, hs]
      ring
    exact (key pk.1 ql.1 pk.2 ql.2).trans (congrArg (· * _) (tw_one_g (M := M) (H := H) pk.1 ql.1 pk.2 ql.2).symm)

theorem nonzeroLocus_prodSec (u : LB.Sec M) (s : LB.Sec H) :
    nonzeroLocus (prodSec u s) = nonzeroLocus u ⊓ nonzeroLocus s := by
  have hb : ∀ (p : M.ι) (k : H.ι), X.basicOpen ((prodSec u s).f ((p, k) : (tw M H 1).ι)) =
      X.basicOpen (u.f p) ⊓ X.basicOpen (s.f k) := by
    intro p k
    change X.basicOpen (rs X (inf_le_left : M.U p ⊓ H.U k ≤ M.U p) (u.f p) *
      rs X (inf_le_right : M.U p ⊓ H.U k ≤ H.U k) (s.f k)) = _
    rw [Scheme.basicOpen_mul]
    erw [Scheme.basicOpen_res, Scheme.basicOpen_res]
    refine le_antisymm (inf_le_inf inf_le_right inf_le_right)
      (le_inf (le_inf (le_inf ((inf_le_left).trans (X.basicOpen_le _)) ((inf_le_right).trans (X.basicOpen_le _)))
        inf_le_left) (le_inf (le_inf ((inf_le_left).trans (X.basicOpen_le _))
          ((inf_le_right).trans (X.basicOpen_le _))) inf_le_right))
  refine le_antisymm (iSup_le fun pk => ?_) ?_
  · exact (hb pk.1 pk.2).le.trans (inf_le_inf (le_iSup (fun k => X.basicOpen (u.f k)) pk.1)
      (le_iSup (fun k => X.basicOpen (s.f k)) pk.2))
  · change (⨆ p, X.basicOpen (u.f p)) ⊓ (⨆ k, X.basicOpen (s.f k)) ≤ _
    rw [iSup_inf_eq]
    refine iSup_le fun p => ?_
    rw [inf_iSup_eq]
    exact iSup_le fun k => (hb p k).ge.trans
      (le_iSup (fun pk => X.basicOpen ((prodSec u s).f pk)) ((p, k) : (tw M H 1).ι))

theorem eval₂Hom_ratios_surjective (hM : M.IsLB) {m : ℕ} (u : Fin (m + 1) → LB.Sec M)
    (hu : ⨆ b, nonzeroLocus (u b) = ⊤) (a : Fin (m + 1)) {D N : X.Opens} (hD : IsAffineOpen D)
    (hN : N = nonzeroLocus (u a) ⊓ D) (ρ : Fin (m + 1) → Γ(X, N))
    (hρ : ∀ c q, rs X (inf_le_right : N ⊓ M.U q ≤ M.U q) ((u c).f q) =
      rs X (inf_le_left : N ⊓ M.U q ≤ N) (ρ c) * rs X (inf_le_right : N ⊓ M.U q ≤ M.U q) ((u a).f q)) :
    Function.Surjective (MvPolynomial.eval₂Hom (rs X (hN.le.trans inf_le_right : N ≤ D)) ρ) := by
  subst hN
  have hVD : nonzeroLocus (u a) ⊓ D ≤ D := inf_le_right
  have hV : IsAffineOpen (nonzeroLocus (u a) ⊓ D) := GlobalTheory.isAffineOpen_nonzeroLocus_inf hM (u a) hD
  letI : Algebra Γ(X, D) Γ(X, nonzeroLocus (u a) ⊓ D) := (rs X hVD).toAlgebra
  intro x
  suffices hx : x ∈ Algebra.adjoin Γ(X, D) (Set.range ρ) by
    rw [Algebra.adjoin_range_eq_range_aeval] at hx
    obtain ⟨P, rfl⟩ := hx
    exact ⟨P, rfl⟩
  let T : Set Γ(X, D) := {t | ∃ b p, X.basicOpen t ≤ X.basicOpen ((u b).f p)}
  have hT : Ideal.span T = ⊤ := by
    rw [← hD.self_le_iSup_basicOpen_iff]
    intro y hy
    obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.1 (hu.ge (Set.mem_univ y))
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 hb
    obtain ⟨t, ht, hyt⟩ := hD.exists_basicOpen_le ⟨y, hp⟩ hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨t, b, p, ht⟩, hyt⟩
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem
    (Algebra.adjoin Γ(X, D) (Set.range ρ)).toSubmodule T hT x ?_
  rintro ⟨t, b, p, ht⟩
  have hWD : X.basicOpen t ≤ D := X.basicOpen_le t
  have hWp : X.basicOpen t ≤ M.U p := ht.trans (X.basicOpen_le _)
  have hW : IsAffineOpen (X.basicOpen t) := hD.basicOpen t
  let α : Γ(X, X.basicOpen t) := rs X hWp ((u a).f p)
  let β : Γ(X, X.basicOpen t) := rs X hWp ((u b).f p)
  have hβ : IsUnit β := by
    have h0 : IsUnit (rs X (X.basicOpen_le ((u b).f p)) ((u b).f p)) :=
      X.toRingedSpace.isUnit_res_basicOpen _
    have h1 := h0.map (rs X ht)
    rwa [rs_rs] at h1
  have hW'W : X.basicOpen α ≤ X.basicOpen t := X.basicOpen_le α
  have hW'eq : X.basicOpen α = X.basicOpen t ⊓ X.basicOpen ((u a).f p) := Scheme.basicOpen_res _ _ _
  have hW'V : X.basicOpen α ≤ nonzeroLocus (u a) ⊓ D := by
    rw [hW'eq]
    exact le_inf (inf_le_right.trans (GlobalTheory.basicOpen_le_nonzeroLocus _ _)) (inf_le_left.trans hWD)
  have hOW' : X.basicOpen (rs X hVD t) ≤ X.basicOpen α := by
    have e0 : X.basicOpen (rs X hVD t) = (nonzeroLocus (u a) ⊓ D) ⊓ X.basicOpen t :=
      Scheme.basicOpen_res _ _ _
    rw [e0, hW'eq]
    refine le_inf inf_le_right ?_
    rw [← GlobalTheory.nonzeroLocus_inf_chart]
    exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans hWp)
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X (X.basicOpen t)
    hW.isCompact hW.isQuasiSeparated α (rs X hW'V x)
  obtain ⟨k, z, hz⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X D
    hD.isCompact hD.isQuasiSeparated t y
  obtain ⟨k', z', hz'⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X D
    hD.isCompact hD.isQuasiSeparated t ((hβ.unit⁻¹ : Γ(X, X.basicOpen t)ˣ) : Γ(X, X.basicOpen t))
  change rs X hW'W y = (rs X hW'W α) ^ n * rs X hW'V x at hy
  change rs X hWD z = (rs X hWD t) ^ k * y at hz
  change rs X hWD z' = (rs X hWD t) ^ k' * ((hβ.unit⁻¹ : Γ(X, X.basicOpen t)ˣ) : Γ(X, X.basicOpen t)) at hz'
  have hr := congrArg (rs X (le_inf hW'V (hW'W.trans hWp) : X.basicOpen α ≤ (nonzeroLocus (u a) ⊓ D) ⊓ M.U p))
    (hρ b p)
  simp only [map_mul, rs_rs] at hr
  set I : Γ(X, X.basicOpen t) := ((hβ.unit⁻¹ : Γ(X, X.basicOpen t)ˣ) : Γ(X, X.basicOpen t)) with hIdef
  have hIβ : I * β = 1 := hβ.val_inv_mul
  have hz1 := congrArg (rs X hW'W) hz
  have hz1' := congrArg (rs X hW'W) hz'
  have hIβ' := congrArg (rs X hW'W) hIβ
  simp only [map_mul, map_pow, map_one, rs_rs] at hz1 hz1' hIβ'
  have hα : rs X hW'W α = rs X (hW'W.trans hWp) ((u a).f p) := rs_rs _ _ _
  have hβ' : rs X hW'W β = rs X (hW'W.trans hWp) ((u b).f p) := rs_rs _ _ _
  let c : Γ(X, D) := z * z' ^ n
  have e1 : rs X hW'V ((rs X hVD t) ^ (k + n * k') * x - rs X hVD c * ρ b ^ n) = 0 := by
    simp only [c, map_sub, map_mul, map_pow, rs_rs]
    rw [hz1, hz1', hy]
    have hARI : rs X hW'W α * rs X hW'V (ρ b) * rs X hW'W I = 1 := by
      rw [hα, mul_comm (rs X _ ((u a).f p)), ← hr, ← hβ', mul_comm, hIβ']
    calc _ = rs X (hW'W.trans hWD) t ^ (k + n * k') * rs X hW'V x -
          rs X (hW'W.trans hWD) t ^ (k + n * k') * rs X hW'V x *
            (rs X hW'W α * rs X hW'V (ρ b) * rs X hW'W I) ^ n := by ring
      _ = 0 := by rw [hARI, one_pow, mul_one, sub_self]
  obtain ⟨l, hl⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hV.isCompact
    ((rs X hVD t) ^ (k + n * k') * x - rs X hVD c * ρ b ^ n) (rs X hVD t) (by
      change rs X (X.basicOpen_le _) _ = 0
      rw [← rs_rs hW'V hOW', e1, map_zero])
  refine ⟨l + (k + n * k'), ?_⟩
  rw [Subalgebra.mem_toSubmodule, Algebra.smul_def]
  have e2 : algebraMap Γ(X, D) Γ(X, nonzeroLocus (u a) ⊓ D) (t ^ (l + (k + n * k'))) * x =
      algebraMap Γ(X, D) Γ(X, nonzeroLocus (u a) ⊓ D) (t ^ l * c) * ρ b ^ n := by
    change rs X hVD (t ^ (l + (k + n * k'))) * x = rs X hVD (t ^ l * c) * ρ b ^ n
    rw [mul_sub, sub_eq_zero] at hl
    rw [map_pow, map_mul, map_pow, pow_add, mul_assoc, hl, mul_assoc]
  change algebraMap Γ(X, D) Γ(X, nonzeroLocus (u a) ⊓ D) (t ^ (l + (k + n * k'))) * x ∈ _
  rw [e2]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self b)) _)

theorem veryAmpleBy_tw_of_generated : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H M : LB X) (n m : ℕ) (s : Fin (n + 1) → LB.Sec H) (u : Fin (m + 1) → LB.Sec M), H.IsLB → M.IsLB → VeryAmpleBy f H s → (⨆ a, nonzeroLocus (u a) = ⊤) → ∃ (n' : ℕ) (s' : Fin (n' + 1) → LB.Sec (GlobalTheory.AbLaw.tw M H 1)), VeryAmpleBy f (GlobalTheory.AbLaw.tw M H 1) s' := by
  intro R _ X f H M n m s u hH hM hs hu
  let e : Fin (m * n + m + n + 1) ≃ Fin (m + 1) × Fin (n + 1) :=
    (finCongr (by ring)).trans finProdFinEquiv.symm
  refine ⟨m * n + m + n, fun j => prodSec (u (e j).1) (s (e j).2), ?_, fun j => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ a, nonzeroLocus (u a) by rw [hu]; trivial)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs.1]; trivial)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨e.symm (a, i), ?_⟩
    rw [nonzeroLocus_prodSec, e.apply_symm_apply]
    exact ⟨ha, hi⟩
  obtain ⟨aff, r, hr, sj⟩ := hs.2 (e j).2
  have loc := nonzeroLocus_prodSec (u (e j).1) (s (e j).2)
  have hNE := loc.le.trans inf_le_left
  have hND := loc.le.trans inf_le_right
  have o : r (e j).2 = 1 := Segre.ratio_self _ _ (hr _)
  choose ρ₀ hρ₀ using fun c => GlobalTheory.AmpleSpan.exists_isRatio (u c) (u (e j).1)
  have o' : ρ₀ (e j).1 = 1 := Segre.ratio_self _ _ (hρ₀ _)
  refine ⟨?_, fun b => rs X hNE (ρ₀ (e b).1) * rs X hND (r (e b).2), fun b kk => ?_, ?_⟩
  · rw [loc]
    exact GlobalTheory.isAffineOpen_nonzeroLocus_inf hM _ aff
  · have h1 : rs X (inf_le_right : nonzeroLocus (u (e j).1) ⊓ M.U kk.1 ≤ M.U kk.1) ((u (e b).1).f kk.1) =
        rs X inf_le_left (ρ₀ (e b).1) * rs X inf_le_right ((u (e j).1).f kk.1) := hρ₀ _ _
    have h2 := hr (e b).2 kk.2
    have hk1 : nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ (M.U kk.1 ⊓ H.U kk.2) ≤
        nonzeroLocus (u (e j).1) ⊓ M.U kk.1 :=
      le_inf (inf_le_left.trans hNE) (inf_le_right.trans inf_le_left)
    have hk2 : nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ (M.U kk.1 ⊓ H.U kk.2) ≤
        nonzeroLocus (s (e j).2) ⊓ H.U kk.2 :=
      le_inf (inf_le_left.trans hND) (inf_le_right.trans inf_le_right)
    replace h1 := congrArg (rs X hk1) h1
    replace h2 := congrArg (rs X hk2) h2
    simp only [map_mul, rs_rs] at h1 h2
    change rs X (inf_le_right : nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ (M.U kk.1 ⊓ H.U kk.2) ≤
          M.U kk.1 ⊓ H.U kk.2)
        (rs X inf_le_left ((u (e b).1).f kk.1) * rs X inf_le_right ((s (e b).2).f kk.2)) =
      rs X (inf_le_left : nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ (M.U kk.1 ⊓ H.U kk.2) ≤
          nonzeroLocus (prodSec (u (e j).1) (s (e j).2)))
        (rs X hNE (ρ₀ (e b).1) * rs X hND (r (e b).2)) *
      rs X (inf_le_right : nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ (M.U kk.1 ⊓ H.U kk.2) ≤
          M.U kk.1 ⊓ H.U kk.2)
        (rs X inf_le_left ((u (e j).1).f kk.1) * rs X inf_le_right ((s (e j).2).f kk.2))
    simp only [map_mul, rs_rs]
    rw [h1, h2]
    ring
  · have hgen := eval₂Hom_ratios_surjective hM u hu (e j).1 aff loc (fun c => rs X hNE (ρ₀ c))
      (fun c q => by
        have h : rs X (inf_le_right : nonzeroLocus (u (e j).1) ⊓ M.U q ≤ M.U q) ((u c).f q) =
            rs X inf_le_left (ρ₀ c) * rs X inf_le_right ((u (e j).1).f q) := hρ₀ c q
        have h' := congrArg (rs X (le_inf (inf_le_left.trans hNE) inf_le_right :
          nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ M.U q ≤ nonzeroLocus (u (e j).1) ⊓ M.U q)) h
        simp only [map_mul, rs_rs] at h' ⊢
        exact h')
    rw [← RingHom.range_eq_top, eq_top_iff]
    rintro x -
    obtain ⟨P, rfl⟩ := hgen x
    induction P using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.eval₂Hom_C]
      obtain ⟨F, rfl⟩ := sj c
      induction F using MvPolynomial.induction_on with
      | C c₀ =>
        refine ⟨MvPolynomial.C c₀, ?_⟩
        rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
        simp only [AbLaw.cst, RingHom.comp_apply, rs_rs]
      | add F G hF hG => rw [map_add, map_add]; exact Subring.add_mem _ hF hG
      | mul_X F l hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (e.symm ((e j).1, l)), ?_⟩
        simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o', map_one, _root_.one_mul]
    | add P Q hP hQ => rw [map_add]; exact Subring.add_mem _ hP hQ
    | mul_X P c hP =>
      rw [map_mul]
      refine Subring.mul_mem _ hP ⟨MvPolynomial.X (e.symm (c, (e j).2)), ?_⟩
      simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o, map_one, _root_.mul_one]
end GlobalTheory.GenTwist
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.veryAmple_twist_of_generated_and_veryAmple : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H M : LB X) (n m : ℕ) (s : Fin (n + 1) → LB.Sec H) (u : Fin (m + 1) → LB.Sec M), H.IsLB → M.IsLB → VeryAmpleBy f H s → (⨆ a, nonzeroLocus (u a) = ⊤) → ∃ (n' : ℕ) (s' : Fin (n' + 1) → LB.Sec (GlobalTheory.AbLaw.tw M H 1)), VeryAmpleBy f (GlobalTheory.AbLaw.tw M H 1) s' := by
  atlas_forward_decl GlobalTheory.GenTwist.veryAmpleBy_tw_of_generated
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

namespace GlobalTheory.FormalAlg.ConsecPowers

theorem units_identity {G : Type*} [CommGroup G] (u P Q R β γ ε : G) (d t : ℤ) :
    (u * P * β⁻¹) * (u * Q * γ⁻¹) ^ (d * t) * (u * R * ε⁻¹) ^ d =
      u ^ (d * (t + 1) + 1) * (β * (γ ^ d) ^ t * (ε ^ d) ^ (1 : ℤ))⁻¹ * (P * Q ^ (d * t) * R ^ d) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_inv]
  module

theorem pw_pw {X : Scheme.{0}} (L : LB X) (a b : ℤ) : pw (pw L a) b = pw L (a * b) := by
  show (⟨L.ι, L.U, fun i j => (L.g i j ^ a) ^ b⟩ : LB X) = ⟨L.ι, L.U, fun i j => L.g i j ^ (a * b)⟩
  congr 1
  funext i j
  exact (zpow_mul _ _ _).symm

theorem lbIso_tw_tw {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (d t : ℤ) :
    LBIso (tw (tw L (pw L d) t) (pw L d) 1) (pw L (d * (t + 1) + 1)) := by
  refine GlobalTheory.LBAlg.lbIso_of_germs
    (A := tw (tw L (pw L d) t) (pw L d) 1) (B := pw L (d * (t + 1) + 1))
    (fun p => res (show (pw L (d * (t + 1) + 1)).U p.1 ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U p.2 ≤
          L.U p.1 ⊓ L.U p.2.1.1 from fun _ hx => ⟨hx.1, hx.2.1.1⟩) (L.g p.1 p.2.1.1) *
      res (show (pw L (d * (t + 1) + 1)).U p.1 ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U p.2 ≤
          L.U p.1 ⊓ L.U p.2.1.2 from fun _ hx => ⟨hx.1, hx.2.1.2⟩) (L.g p.1 p.2.1.2) ^ (d * t) *
      res (show (pw L (d * (t + 1) + 1)).U p.1 ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U p.2 ≤
          L.U p.1 ⊓ L.U p.2.2 from fun _ hx => ⟨hx.1, hx.2.2⟩) (L.g p.1 p.2.2) ^ d) ?_
  rintro x ⟨a, ⟨b, c⟩, e⟩ ⟨a', ⟨b', c'⟩, e'⟩ ha hp ha' hq
  have hb : x ∈ L.U b := hp.1.1
  have hc : x ∈ L.U c := hp.1.2
  have he : x ∈ L.U e := hp.2
  have hb' : x ∈ L.U b' := hq.1.1
  have hc' : x ∈ L.U c' := hq.1.2
  have he' : x ∈ L.U e' := hq.2
  have inv : ∀ {j j' : L.ι}, x ∈ L.U j → x ∈ L.U j' →
      gm (𝟙 X) x (L.U j' ⊓ L.U j) (L.g j' j) = (gm (𝟙 X) x (L.U j ⊓ L.U j') (L.g j j'))⁻¹ :=
    fun hj hj' => eq_inv_of_mul_eq_one_right
      ((gm_cocycle hL (𝟙 X) x hj hj' hj).trans (gm_self hL (𝟙 X) x hj))
  have rel : ∀ {i i' j j' : L.ι}, x ∈ L.U i → x ∈ L.U i' → x ∈ L.U j → x ∈ L.U j' →
      gm (𝟙 X) x (L.U i ⊓ L.U j) (L.g i j) = gm (𝟙 X) x (L.U i ⊓ L.U i') (L.g i i') *
        gm (𝟙 X) x (L.U i' ⊓ L.U j') (L.g i' j') * (gm (𝟙 X) x (L.U j ⊓ L.U j') (L.g j j'))⁻¹ := by
    intro i i' j j' hi hi' hj hj'
    rw [← gm_cocycle hL (𝟙 X) x hi hi' hj, ← gm_cocycle hL (𝟙 X) x hi' hj' hj, inv hj hj', mul_assoc]
  have sec : ∀ (a₀ b₀ c₀ e₀ : L.ι) (h : (𝟙 X : X ⟶ X) x ∈ (pw L (d * (t + 1) + 1)).U a₀ ⊓
      (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀)),
      gm (𝟙 X) x ((pw L (d * (t + 1) + 1)).U a₀ ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀))
        (res (show (pw L (d * (t + 1) + 1)).U a₀ ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀) ≤
          L.U a₀ ⊓ L.U b₀ from fun _ hx => ⟨hx.1, hx.2.1.1⟩) (L.g a₀ b₀) *
        res (show (pw L (d * (t + 1) + 1)).U a₀ ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀) ≤
          L.U a₀ ⊓ L.U c₀ from fun _ hx => ⟨hx.1, hx.2.1.2⟩) (L.g a₀ c₀) ^ (d * t) *
        res (show (pw L (d * (t + 1) + 1)).U a₀ ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀) ≤
          L.U a₀ ⊓ L.U e₀ from fun _ hx => ⟨hx.1, hx.2.2⟩) (L.g a₀ e₀) ^ d) =
      gm (𝟙 X) x (L.U a₀ ⊓ L.U b₀) (L.g a₀ b₀) * gm (𝟙 X) x (L.U a₀ ⊓ L.U c₀) (L.g a₀ c₀) ^ (d * t) *
        gm (𝟙 X) x (L.U a₀ ⊓ L.U e₀) (L.g a₀ e₀) ^ d := by
    intro a₀ b₀ c₀ e₀ h
    rw [map_mul, map_mul, map_zpow, map_zpow, gm_res _ x _ h, gm_res _ x _ h, gm_res _ x _ h]
  have eB : gm (𝟙 X) x ((pw L (d * (t + 1) + 1)).U a ⊓ (pw L (d * (t + 1) + 1)).U a')
      ((pw L (d * (t + 1) + 1)).g a a') = gm (𝟙 X) x (L.U a ⊓ L.U a') (L.g a a') ^ (d * (t + 1) + 1) :=
    map_zpow (gm (𝟙 X) x (L.U a ⊓ L.U a')) (L.g a a') _
  have eA : gm (𝟙 X) x ((tw (tw L (pw L d) t) (pw L d) 1).U ((b, c), e) ⊓
      (tw (tw L (pw L d) t) (pw L d) 1).U ((b', c'), e'))
      ((tw (tw L (pw L d) t) (pw L d) 1).g ((b, c), e) ((b', c'), e')) =
      gm (𝟙 X) x (L.U b ⊓ L.U b') (L.g b b') * (gm (𝟙 X) x (L.U c ⊓ L.U c') (L.g c c') ^ d) ^ t *
        (gm (𝟙 X) x (L.U e ⊓ L.U e') (L.g e e') ^ d) ^ (1 : ℤ) := by
    have g1 : gm (𝟙 X) x ((pw L d).U c ⊓ (pw L d).U c') ((pw L d).g c c') =
        gm (𝟙 X) x (L.U c ⊓ L.U c') (L.g c c') ^ d := map_zpow _ _ _
    have g2 : gm (𝟙 X) x ((pw L d).U e ⊓ (pw L d).U e') ((pw L d).g e e') =
        gm (𝟙 X) x (L.U e ⊓ L.U e') (L.g e e') ^ d := map_zpow _ _ _
    refine (GlobalTheory.LBAlg.gm_tw (tw L (pw L d) t) (pw L d) 1 (𝟙 X) x ((b, c), e) ((b', c'), e') ⟨hp, hq⟩).trans ?_
    exact congrArg₂ (· * ·) ((GlobalTheory.LBAlg.gm_tw L (pw L d) t (𝟙 X) x (b, c) (b', c') ⟨hp.1, hq.1⟩).trans
      (congrArg₂ (· * ·) rfl (congrArg (· ^ t) g1))) (congrArg (· ^ (1 : ℤ)) g2)
  refine (sec a b c e ⟨ha, hp⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ (· * ·) eB.symm
    (congrArg (·⁻¹) eA.symm)) (sec a' b' c' e' ⟨ha', hq⟩).symm))
  rw [rel ha ha' hb hb', rel ha ha' hc hc', rel ha ha' he he']
  exact units_identity _ _ _ _ _ _ _ d t

end GlobalTheory.FormalAlg.ConsecPowers

namespace GlobalTheory.FormalAlg.ConsecPowers

theorem exists_veryAmpleBy_pw_and_succ : ∀ (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) (L : LB X.left), L.IsLB → RelAmple X L → ∃ d : ℕ, 1 ≤ d ∧ ∀ c : ℕ, c = d ∨ c = d + 1 → ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec (GlobalTheory.AbLaw.pw L c)), VeryAmpleBy X.hom (GlobalTheory.AbLaw.pw L c) s := by
  intro R _ X L hL hA
  obtain ⟨d₁, hd₁, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R X L hL).1 hA
  have hH := isLB_pw hL (d₁ : ℤ)
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.TwistGen.twist_generated R X.left X.hom _ n s hH hs L hL
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t₀ ≤ (t : ℤ) := ⟨t₀.toNat, Int.self_le_toNat t₀⟩
  obtain ⟨m, u, hu⟩ := ht₀ (t : ℤ) ht
  refine ⟨d₁ * (t + 1), Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), fun c hc => ?_⟩
  rcases hc with rfl | rfl
  · obtain ⟨n', s', hs'⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw R X.left X.hom _ n s hH hs (t + 1) (by omega)
    have e : GlobalTheory.AbLaw.pw L ((d₁ * (t + 1) : ℕ) : ℤ) = GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw L (d₁ : ℤ)) ((t + 1 : ℕ) : ℤ) := by
      rw [pw_pw]
      push_cast
      rfl
    rw [e]
    exact ⟨n', s', hs'⟩
  · obtain ⟨n', s', hs'⟩ := GlobalTheory.T.veryAmple_twist_of_generated_and_veryAmple R X.left X.hom (GlobalTheory.AbLaw.pw L (d₁ : ℤ)) (tw L (GlobalTheory.AbLaw.pw L (d₁ : ℤ)) (t : ℤ))
      n m s u hH (isLB_tw hL hH _) hs hu
    obtain ⟨s'', hs''⟩ := GlobalTheory.exists_veryAmpleBy_of_lbIso (isLB_tw (isLB_tw hL hH _) hH 1) (isLB_pw hL _)
      (lbIso_tw_tw hL (d₁ : ℤ) (t : ℤ)) hs'
    have e : ((d₁ * (t + 1) + 1 : ℕ) : ℤ) = (d₁ : ℤ) * ((t : ℤ) + 1) + 1 := by push_cast; ring
    rw [e]
    exact ⟨n', s'', hs''⟩

end GlobalTheory.FormalAlg.ConsecPowers
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_consecutive_veryAmple_powers_relAmple : ∀ (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) (L : LB X.left), L.IsLB → RelAmple X L → ∃ d : ℕ, 1 ≤ d ∧ ∀ c : ℕ, c = d ∨ c = d + 1 → ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec (GlobalTheory.AbLaw.pw L c)), VeryAmpleBy X.hom (GlobalTheory.AbLaw.pw L c) s := by
  atlas_forward_decl GlobalTheory.FormalAlg.ConsecPowers.exists_veryAmpleBy_pw_and_succ
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.FormalAlg.TowerVA

theorem exists_compatible_of_lift (R : Type) [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (N : ∀ e, LB (Y e).left) (hN : ∀ e, (N e).IsLB) (p k c : ℕ) (hk : 1 ≤ k) (hc : (c : ℤ) = (p : ℤ) * (k : ℤ))
    (n : ℕ) (s : Fin (n + 1) → LB.Sec (GlobalTheory.AbLaw.pw (N 0) p))
    (hs : VeryAmpleBy (Y 0).hom (GlobalTheory.AbLaw.pw (N 0) p) s)
    (hlift : ∀ (L : ∀ e, LB (Y e).left) (u : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e))),
      (∀ e, (L e).IsLB ∧ (u e).IsGen) → LBIso (L 0) (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw (N 0) p) k) →
        ∀ σ₀ : LB.Sec (L 0), ∃ σ : ∀ e, LB.Sec (L e), σ 0 = σ₀ ∧ ∀ e, Rel (β e) (u e) (σ (e + 1)) (σ e))
    (v : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) c) ((GlobalTheory.AbLaw.pw (N (e + 1)) c).pull (β e))) (hv : ∀ e, (v e).IsGen) :
    ∃ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (GlobalTheory.AbLaw.pw (N e) c)),
      (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) ∧ ∀ e, VeryAmpleBy (Y e).hom (GlobalTheory.AbLaw.pw (N e) c) (s e) := by
  have hEq : GlobalTheory.AbLaw.pw (N 0) c = GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw (N 0) p) k := by
    rw [hc]
    exact congrArg (fun g => (⟨(N 0).ι, (N 0).U, g⟩ : LB (Y 0).left))
      (funext fun i => funext fun j => zpow_mul ((N 0).g i j) _ _)
  have h0 : ∃ (n' : ℕ) (s' : Fin (n' + 1) → LB.Sec (GlobalTheory.AbLaw.pw (N 0) c)),
      VeryAmpleBy (Y 0).hom (GlobalTheory.AbLaw.pw (N 0) c) s' := by
    rw [hEq]
    exact GlobalTheory.AbLaw.veryAmpleBy_pw _ _ _ _ n s (isLB_pw (hN 0) _) hs k hk
  obtain ⟨n', s0, hs0⟩ := h0
  have hL : ∀ e, (GlobalTheory.AbLaw.pw (N e) c).IsLB ∧ (v e).IsGen := fun e => ⟨isLB_pw (hN e) _, hv e⟩
  have hiso : LBIso (GlobalTheory.AbLaw.pw (N 0) c) (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw (N 0) p) k) :=
    hEq ▸ lbIso_refl (isLB_pw (hN 0) _)
  choose σ hσ0 hσ using fun j => hlift (fun e => GlobalTheory.AbLaw.pw (N e) c) v hL hiso (s0 j)
  refine ⟨n', fun e j => σ j e, fun e j => hσ j e, ?_⟩
  rintro (_ | e)
  · show VeryAmpleBy _ _ (fun j => σ j 0)
    simp only [hσ0]
    exact hs0
  · obtain ⟨j₀, hj, w, hw, hr⟩ := tower I Y β hβ (fun e => GlobalTheory.AbLaw.pw (N e) c) v hL (fun e j => σ j e)
      (fun e j => hσ j e) e
    simp only [hσ0] at hr
    exact GlobalTheory.AbLaw.veryAmpleBy_of_isNilpotent _ _ _ (Ideal.Quotient.factor_surjective _)
      (GlobalTheory.Degen.isNilpotent_ker_factor_pow I _) _ _ _ _ j₀ hj _ _ w n' _ _ (hL _).1 (hL _).1
      ((isGen_iff _).2 hw) hr hs0

theorem exists_veryAmple_compatible : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ N : ∀ e, LB (Y e).left, (∀ e, (N e).IsLB) → RelAmple (Y 0) (N 0) → ∃ a : ℕ, 1 ≤ a ∧ ∀ c : ℕ, c = a ∨ c = a + 1 → ∀ v : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) c) ((GlobalTheory.AbLaw.pw (N (e + 1)) c).pull (β e)), (∀ e, (v e).IsGen) → ∃ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (GlobalTheory.AbLaw.pw (N e) c)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) ∧ ∀ e, VeryAmpleBy (Y e).hom (GlobalTheory.AbLaw.pw (N e) c) (s e) := by
  intro R _ _ I Y β hβ N hN hamp
  obtain ⟨d, hd1, hd⟩ := GlobalTheory.T.exists_consecutive_veryAmple_powers_relAmple (R ⧸ I ^ (0 + 1)) (Y 0) (N 0) (hN 0) hamp
  obtain ⟨n₁, s₁, hs₁⟩ := hd d (Or.inl rfl)
  obtain ⟨n₂, s₂, hs₂⟩ := hd (d + 1) (Or.inr rfl)
  obtain ⟨k₁, hk₁⟩ := GlobalTheory.T.exists_uniform_lift_sections_thickeningTower R I Y β hβ _ n₁ s₁ (isLB_pw (hN 0) _) hs₁
  obtain ⟨k₂, hk₂⟩ := GlobalTheory.T.exists_uniform_lift_sections_thickeningTower R I Y β hβ _ n₂ s₂ (isLB_pw (hN 0) _) hs₂
  refine ⟨d * (1 + (d + 1) * max k₁ k₂), Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
  have ht1 : ∀ m t : ℕ, 1 ≤ m → t ≤ 1 + m * t := fun m t hm => by nlinarith
  rintro c (rfl | rfl) v hv
  · exact exists_compatible_of_lift R I Y β hβ N hN d (1 + (d + 1) * max k₁ k₂) _ (by omega) (by push_cast; ring)
      n₁ s₁ hs₁ (hk₁ _ (le_trans (le_max_left _ _) (ht1 _ _ (by omega)))) v hv
  · exact exists_compatible_of_lift R I Y β hβ N hN (d + 1) (1 + d * max k₁ k₂) _ (by omega) (by push_cast; ring)
      n₂ s₂ hs₂ (hk₂ _ (le_trans (le_max_right _ _) (ht1 _ _ hd1))) v hv

end GlobalTheory.FormalAlg.TowerVA
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_veryAmple_compatible_sections_thickeningTower : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ N : ∀ e, LB (Y e).left, (∀ e, (N e).IsLB) → RelAmple (Y 0) (N 0) → ∃ a : ℕ, 1 ≤ a ∧ ∀ c : ℕ, c = a ∨ c = a + 1 → ∀ v : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) c) ((GlobalTheory.AbLaw.pw (N (e + 1)) c).pull (β e)), (∀ e, (v e).IsGen) → ∃ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (GlobalTheory.AbLaw.pw (N e) c)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) ∧ ∀ e, VeryAmpleBy (Y e).hom (GlobalTheory.AbLaw.pw (N e) c) (s e) := by
  atlas_forward_decl GlobalTheory.FormalAlg.TowerVA.exists_veryAmple_compatible
end
