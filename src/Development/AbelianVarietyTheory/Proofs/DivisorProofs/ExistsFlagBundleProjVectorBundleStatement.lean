import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratingSectionsProjectiveMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveRelationUniqueQuotient
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf

section
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot

open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.LB (resG_resG)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineQuot

theorem bijective_of_basis_unit {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (B' : Module.Basis (Fin 1) R M) (B : Module.Basis (Fin 1) R N)
    (f : M →ₗ[R] N) (u : Rˣ) (h : f (B' 0) = (u : R) • B 0) : Function.Bijective f := by
  have hsum (P : Type) [AddCommGroup P] [Module R P] (C : Module.Basis (Fin 1) R P) (m : P) :
      m = C.repr m 0 • C 0 := by
    conv_lhs => rw [← C.sum_repr m]
    simp
  constructor
  · refine (injective_iff_map_eq_zero f).2 fun m hm => ?_
    rw [hsum M B' m, map_smul, h, smul_smul] at hm
    have h1 : B'.repr m 0 * u = 0 := by
      simpa using congrArg (fun n => B.repr n 0) hm
    have h2 : B'.repr m 0 = 0 := (Units.mul_left_eq_zero u).1 h1
    rw [hsum M B' m, h2, zero_smul]
  · intro n
    refine ⟨(B.repr n 0 * ((u⁻¹ : Rˣ) : R)) • B' 0, ?_⟩
    rw [map_smul, h, smul_smul, mul_assoc, Units.inv_mul, mul_one, ← hsum N B n]

theorem gen_of_jointEpi : ∀ (T : Scheme.{0}) (L Q : T.Modules) (N : ℕ) (s : Fin (N + 1) → (L ⟶ Q)),
    IsVB L 1 → IsVB Q 1 → JointEpi s → Gen s := by
  intro T L Q N s hL hQ hs x
  have := Abelian.hasFiniteBiproducts (C := T.Modules)
  let p : (⨁ fun _ : Fin (N + 1) => L) ⟶ Q := biproduct.desc s
  have hp : Epi p := (Preadditive.epi_iff_cancel_zero p).2 fun Z a ha => hs Z a fun j => by
    have := congrArg (biproduct.ι (fun _ : Fin (N + 1) => L) j ≫ ·) ha
    simpa [p] using this
  obtain ⟨U₁, e', -, hx₁, -, he'⟩ := hL.exists_affine (V := ⊤) (x := x) trivial
  obtain ⟨U₂, e, -, hx₂, h₂, he⟩ := hQ.exists_affine hx₁
  obtain ⟨W, hW, hxW, t, ht⟩ := exists_app_eq_of_epi p (e 0) hx₂
  have hW' : W ≤ U₁ := hW.trans h₂
  let u : Fin (N + 1) → Γ(L, W) := fun j => (biproduct.π (fun _ : Fin (N + 1) => L) j).app W t
  have hsum : ∑ j, (s j).app W (u j) = resM Q hW (e 0) := by
    rw [← ht]
    have hpd : p = ∑ j, biproduct.π (fun _ : Fin (N + 1) => L) j ≫ s j := biproduct.desc_eq
    let ev : ((⨁ fun _ : Fin (N + 1) => L) ⟶ Q) →+ Γ(Q, W) :=
      AddMonoidHom.mk' (fun φ => φ.app W t) fun _ _ => rfl
    have := map_sum ev (fun j => biproduct.π (fun _ : Fin (N + 1) => L) j ≫ s j) Finset.univ
    rw [← hpd] at this
    exact this.symm
  let B' := he'.basis hW'
  let B := he.basis hW
  let a : Fin (N + 1) → Γ(T, W) := fun j => B'.repr (u j) 0
  let c : Fin (N + 1) → Γ(T, W) := fun j => B.repr ((s j).app W (resM L hW' (e' 0))) 0
  have hone (P : Type) [AddCommGroup P] [Module Γ(T, W) P] (C : Module.Basis (Fin 1) Γ(T, W) P)
      (m : P) : m = C.repr m 0 • C 0 := by
    conv_lhs => rw [← C.sum_repr m]
    simp
  have hu (j : Fin (N + 1)) : u j = a j • resM L hW' (e' 0) := by
    rw [← IsFrame.basis_apply he' hW']; exact hone _ B' (u j)
  have hc (j : Fin (N + 1)) : (s j).app W (resM L hW' (e' 0)) = c j • resM Q hW (e 0) := by
    rw [← IsFrame.basis_apply he hW]; exact hone _ B _
  have hac : ∑ j, a j * c j = 1 := by
    have h1 : (∑ j, a j * c j) • B 0 = (1 : Γ(T, W)) • B 0 := by
      rw [one_smul, Finset.sum_smul]
      calc ∑ j, (a j * c j) • B 0 = ∑ j, (s j).app W (u j) :=
            Finset.sum_congr rfl fun j _ => by
              rw [hu, Scheme.Modules.Hom.app_smul, hc, smul_smul, IsFrame.basis_apply]
        _ = B 0 := by rw [hsum, IsFrame.basis_apply]
    simpa using congrArg (fun n => B.repr n 0) h1
  obtain ⟨j, hj⟩ : ∃ j, x ∈ T.basicOpen (c j) := by
    by_contra hno
    push_neg at hno
    have hmem (j : Fin (N + 1)) : T.presheaf.germ W x hxW (c j) ∈ IsLocalRing.maximalIdeal _ :=
      fun hu' => hno j ((T.mem_basicOpen (c j) x hxW).2 hu')
    have : T.presheaf.germ W x hxW (∑ j, a j * c j) ∈ IsLocalRing.maximalIdeal _ := by
      rw [map_sum]
      exact Ideal.sum_mem _ fun j _ => by
        rw [map_mul]; exact Ideal.mul_mem_left _ _ (hmem j)
    rw [hac, map_one] at this
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 this)
  refine ⟨j, T.basicOpen (c j), hj, fun V hV => ?_⟩
  have hVW : V ≤ W := hV.trans (T.basicOpen_le (c j))
  have hunit : IsUnit (resG T hVW (c j)) := by
    have h0 := (T.toRingedSpace.isUnit_res_basicOpen (c j)).map (resG T hV)
    have : resG T hV (resG T (T.basicOpen_le (c j)) (c j)) = resG T hVW (c j) := resG_resG _ _ _
    rw [← this]; exact h0
  have key : GlobalTheory.QCoh.appLinear (s j) V ((he'.basis (hVW.trans hW')) 0) =
      ((hunit.unit : Γ(T, V)ˣ) : Γ(T, V)) • (he.basis (hVW.trans hW)) 0 := by
    rw [IsUnit.unit_spec, GlobalTheory.QCoh.appLinear_apply, IsFrame.basis_apply, IsFrame.basis_apply,
      ← resM_resM hW' hVW, app_resM, hc, resM_smul, resM_resM]
  have hb := bijective_of_basis_unit (R := Γ(T, V)) _ _ _ _ key
  exact hb

end GlobalTheory.LineQuot

end
end

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jointly_epi_sections_generate : ∀ (T : Scheme.{0}) (L Q : T.Modules) (N : ℕ) (s : Fin (N + 1) → (L ⟶ Q)), IsVB L 1 → IsVB Q 1 → JointEpi s → Gen s := by
  atlas_forward_decl GlobalTheory.LineQuot.gen_of_jointEpi
end

section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generating_sections_projective_map : ∀ (k : Type) [CommRing k] (N : ℕ) (T : Scheme.{0}) (f : T ⟶ Sp k) (L Q : T.Modules) (s : Fin (N + 1) → (L ⟶ Q)), IsVB L 1 → IsVB Q 1 → Gen s → ∃ φ : T ⟶ PSpace k N, φ ≫ PSpace.str k N = f ∧ Rel φ s := by
  first | exact @GlobalTheory.LineQuot.exists_toPSpace | exact GlobalTheory.LineQuot.exists_toPSpace | (intros; apply GlobalTheory.LineQuot.exists_toPSpace <;> assumption)
end

section
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.LineQuot

theorem isUnit_pullRatio_of_frame {k : Type} [CommRing k] {N : ℕ} {T : Scheme.{0}} {L Q : T.Modules}
    {s : Fin (N + 1) → (L ⟶ Q)} {χ : T ⟶ PSpace k N} (hχ : Rel χ s) {V : T.Opens} {i j : Fin (N + 1)}
    (hi : V ≤ χ ⁻¹ᵁ ProjSpace.chart k N i) (hb : Function.Bijective ((s j).app V))
    {e : Fin 1 → Γ(Q, V)} (he : IsFrame e) : IsUnit (ProjSpace.pullRatio χ V i hi j) := by
  set b := he.basis (le_refl V)
  obtain ⟨t, ht⟩ := hb.2 (b 0)
  set c := b.repr ((s i).app V t) 0
  have hc : (s i).app V t = c • b 0 := by
    conv_lhs => rw [← b.sum_repr ((s i).app V t)]
    simp [Fin.sum_univ_one, c]
  have h1 := hχ i j V hi t
  rw [ht, hc, smul_smul] at h1
  have h2 := congrArg (fun x => b.repr x 0) h1
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
    mul_one] at h2
  exact .of_mul_eq_one _ h2.symm

theorem pullRatio_smul_eq {k : Type} [CommRing k] {N : ℕ} {T : Scheme.{0}} {L Q : T.Modules}
    {s : Fin (N + 1) → (L ⟶ Q)} {χ : T ⟶ PSpace k N} (hχ : Rel χ s) {V : T.Opens} {j : Fin (N + 1)}
    (hj : V ≤ χ ⁻¹ᵁ ProjSpace.chart k N j) (t : Γ(L, V)) (m : Fin (N + 1)) :
    (s m).app V t = ProjSpace.pullRatio χ V j hj m • (s j).app V t :=
  hχ j m V hj t

theorem le_preimage_chart {k : Type} [CommRing k] {N : ℕ} {T : Scheme.{0}} {L Q : T.Modules}
    {s : Fin (N + 1) → (L ⟶ Q)} {χ : T ⟶ PSpace k N} (hχ : Rel χ s) {V : T.Opens} {i j : Fin (N + 1)}
    (hi : V ≤ χ ⁻¹ᵁ ProjSpace.chart k N i) (hb : Function.Bijective ((s j).app V))
    {e : Fin 1 → Γ(Q, V)} (he : IsFrame e) : V ≤ χ ⁻¹ᵁ ProjSpace.chart k N j := by
  have h := ProjSpace.basicOpen_pullRatio (φ := χ) (W := V) (i := i) (hi := hi) (j := j)
  rw [T.basicOpen_of_isUnit (isUnit_pullRatio_of_frame hχ hi hb he)] at h
  exact h.le.trans inf_le_right

theorem exists_mem_preimage_chart {k : Type} [CommRing k] {N : ℕ} {T : Scheme.{0}} (χ : T ⟶ PSpace k N)
    (y : T) : ∃ i, y ∈ χ ⁻¹ᵁ ProjSpace.chart k N i := by
  have : χ y ∈ (⨆ i, ProjSpace.chart k N i : (PSpace k N).Opens) := by
    rw [ProjSpace.iSup_chart]; trivial
  exact (TopologicalSpace.Opens.mem_iSup (s := fun i => ProjSpace.chart k N i)).1 this

theorem eq_of_rel : ∀ (k : Type) [CommRing k] (N : ℕ) (T : Scheme.{0}) (L Q : T.Modules)
    (s : Fin (N + 1) → (L ⟶ Q)) (φ ψ : T ⟶ PSpace k N), IsVB L 1 → IsVB Q 1 → Gen s →
    φ ≫ PSpace.str k N = ψ ≫ PSpace.str k N → Rel φ s → Rel ψ s → φ = ψ := by
  intro k _ N T L Q s φ ψ _ hQ hG hstr hφ hψ
  refine ProjSpace.hom_ext hstr fun y => ?_
  obtain ⟨j, W, hyW, hbij⟩ := hG y
  obtain ⟨i, hi⟩ := exists_mem_preimage_chart φ y
  obtain ⟨l, hl⟩ := exists_mem_preimage_chart ψ y
  obtain ⟨V, e, -, hyV, hV, he⟩ := hQ.exists_affine
    (V := W ⊓ φ ⁻¹ᵁ ProjSpace.chart k N i ⊓ ψ ⁻¹ᵁ ProjSpace.chart k N l) ⟨⟨hyW, hi⟩, hl⟩
  have hb := hbij V (hV.trans (inf_le_left.trans inf_le_left))
  have hjφ := le_preimage_chart hφ (hV.trans (inf_le_left.trans inf_le_right)) hb he
  have hjψ := le_preimage_chart hψ (hV.trans inf_le_right) hb he
  refine ⟨V, hyV, j, hjφ, hjψ, fun m => ?_⟩
  set b := he.basis (le_refl V)
  obtain ⟨t, ht⟩ := hb.2 (b 0)
  have h := (pullRatio_smul_eq hφ hjφ t m).symm.trans (pullRatio_smul_eq hψ hjψ t m)
  rw [ht] at h
  have h2 := congrArg (fun x => b.repr x 0) h
  simpa only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
    mul_one] using h2

end GlobalTheory.LineQuot
end
end

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_map_unique_of_relation : ∀ (k : Type) [CommRing k] (N : ℕ) (T : Scheme.{0}) (L Q : T.Modules) (s : Fin (N + 1) → (L ⟶ Q)) (φ ψ : T ⟶ PSpace k N), IsVB L 1 → IsVB Q 1 → Gen s → φ ≫ PSpace.str k N = ψ ≫ PSpace.str k N → Rel φ s → Rel ψ s → φ = ψ := by
  atlas_forward_decl GlobalTheory.LineQuot.eq_of_rel
end

section
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot

set_option autoImplicit false

noncomputable section

open GlobalTheory.Twist (resM resM_resM resM_smul app_resM sec_ext_of_cover)

namespace GlobalTheory.LineQuot

theorem rel_pullback : ∀ (k : Type) [CommRing k] (N : ℕ) (S T : Scheme.{0}) (g : S ⟶ T) (L Q : T.Modules)
    (s : Fin (N + 1) → (L ⟶ Q)) (φ : T ⟶ PSpace k N), IsVB L 1 → IsVB Q 1 → Rel φ s →
    Rel (g ≫ φ) fun j => (Scheme.Modules.pullback g).map (s j) := by
  intro k _ N S T g L Q s φ hL _ hs i j W hW t
  haveI := hL.isQuasicoherent
  beta_reduce
  set A := (Scheme.Modules.pullback g).map (s j)
  set B := (Scheme.Modules.pullback g).map (s i)

  have hsmul : ∀ (U : S.Opens) (hU : U ≤ (g ≫ φ) ⁻¹ᵁ ProjSpace.chart k N i) (c : Γ(S, U))
      (u : Γ((Scheme.Modules.pullback g).obj L, U)),
      A.app U u = ProjSpace.pullRatio (g ≫ φ) U i hU j • B.app U u →
      A.app U (c • u) = ProjSpace.pullRatio (g ≫ φ) U i hU j • B.app U (c • u) := by
    intro U hU c u h
    rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, h, smul_smul, smul_smul, mul_comm]
  have hW' : W ≤ g ⁻¹ᵁ (φ ⁻¹ᵁ ProjSpace.chart k N i) := hW
  have loc : ∀ y : W, ∃ (V : T.Opens) (e : Fin 1 → Γ(L, V)), (y : S) ∈ g ⁻¹ᵁ V ∧ V ≤ φ ⁻¹ᵁ ProjSpace.chart k N i ∧
      IsFrame e := fun y => by
    obtain ⟨V, e, -, hy, hV, he⟩ := hL.exists_affine (x := g y) (V := φ ⁻¹ᵁ ProjSpace.chart k N i) (hW' y.2)
    exact ⟨V, e, hy, hV, he⟩
  choose V e hy hV he using loc
  refine sec_ext_of_cover (fun y => W ⊓ g ⁻¹ᵁ V y) (fun _ => inf_le_left)
    (fun y hyW => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hyW⟩, hyW, hy _⟩) fun y => ?_
  have hU : W ⊓ g ⁻¹ᵁ V y ≤ (g ≫ φ) ⁻¹ᵁ ProjSpace.chart k N i := inf_le_left.trans hW
  have hgV : g ⁻¹ᵁ V y ≤ (g ≫ φ) ⁻¹ᵁ ProjSpace.chart k N i := g.preimage_mono (hV y)

  have hpb : A.app (g ⁻¹ᵁ V y) (QCoh.pullbackSections g L (le_refl _) (e y 0)) =
      ProjSpace.pullRatio (g ≫ φ) (g ⁻¹ᵁ V y) i hgV j • B.app (g ⁻¹ᵁ V y) (QCoh.pullbackSections g L (le_refl _) (e y 0)) := by
    rw [QCoh.pullback_map_app_pullbackSections, QCoh.pullback_map_app_pullbackSections,
      hs i j (V y) (hV y) (e y 0), QCoh.pullbackSections_smul, ProjSpace.appLE_pullRatio]
  have hres : A.app (W ⊓ g ⁻¹ᵁ V y) (resM _ inf_le_right (QCoh.pullbackSections g L (le_refl _) (e y 0))) =
      ProjSpace.pullRatio (g ≫ φ) (W ⊓ g ⁻¹ᵁ V y) i hU j •
        B.app (W ⊓ g ⁻¹ᵁ V y) (resM _ inf_le_right (QCoh.pullbackSections g L (le_refl _) (e y 0))) := by
    rw [app_resM, app_resM, hpb, resM_smul, ProjSpace.resG_pullRatio]
  obtain ⟨a, ha⟩ := ((he y).pullback g (W ⊓ g ⁻¹ᵁ V y) inf_le_right).2 (resM _ inf_le_left t)
  rw [Fintype.linearCombination_apply, Fin.sum_univ_one] at ha
  rw [← app_resM, resM_smul, ← app_resM, ProjSpace.resG_pullRatio, ← ha]
  exact hsmul _ _ _ _ hres

end GlobalTheory.LineQuot

end
end

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_relation_pullback : ∀ (k : Type) [CommRing k] (N : ℕ) (S T : Scheme.{0}) (g : S ⟶ T) (L Q : T.Modules) (s : Fin (N + 1) → (L ⟶ Q)) (φ : T ⟶ PSpace k N), IsVB L 1 → IsVB Q 1 → Rel φ s → Rel (g ≫ φ) fun j => (Scheme.Modules.pullback g).map (s j) := by
  atlas_forward_decl GlobalTheory.LineQuot.rel_pullback
end

section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_relation_unique_quotient : ∀ (k : Type) [CommRing k] (N : ℕ) (T : Scheme.{0}) (L Q Q' : T.Modules) (s : Fin (N + 1) → (L ⟶ Q)) (s' : Fin (N + 1) → (L ⟶ Q')) (φ : T ⟶ PSpace k N), IsVB L 1 → IsVB Q 1 → JointEpi s → Gen s → Rel φ s → Rel φ s' → ∃ e : Q ⟶ Q', ∀ j, s j ≫ e = s' j := by
  first | exact @GlobalTheory.LineQuot.exists_factor_of_rel | exact GlobalTheory.LineQuot.exists_factor_of_rel | (intros; apply GlobalTheory.LineQuot.exists_factor_of_rel <;> assumption)
end

section
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LineQuot

set_option backward.isDefEq.respectTransparency false in

theorem exists_taut_quot : ∀ (k : Type) [CommRing k] (N : ℕ) (T : Scheme.{0}) (φ : T ⟶ PSpace k N) (L : T.Modules), IsVB L 1 → ∃ (Q : T.Modules) (s : Fin (N + 1) → (L ⟶ Q)), IsVB Q 1 ∧ JointEpi s ∧ Rel φ s := by
  intro k _ N T φ L hL
  have hM : ((ProjSpace.O1 k N).pull φ).IsLB := LB.isLB_pull (ProjSpace.O1_isLB k N) φ
  refine ⟨twist L ((ProjSpace.O1 k N).pull φ),
    fun j => Twist.secHom L (Cartier.secPull (ProjSpace.coord k N j) φ), hL.twist hM, ?_, ?_⟩
  · intro Z a ha
    have hc := ProjSpace.iSup_nonzeroLocus_secPull (ProjSpace.iSup_nonzeroLocus_coord k N) φ
    ext V q
    refine Twist.sec_ext_of_cover
      (fun j => V ⊓ Out.nonzeroLocus (Cartier.secPull (ProjSpace.coord k N j) φ)) (fun _ => inf_le_left)
      (GlobalTheory.LB.le_iSup_inf hc V) fun j => ?_
    rw [← Twist.app_resM, ← Twist.app_resM]
    obtain ⟨t, ht⟩ := (Twist.bijective_secHom_app (F := L) hM (Cartier.secPull (ProjSpace.coord k N j) φ)
      (V := V ⊓ Out.nonzeroLocus (Cartier.secPull (ProjSpace.coord k N j) φ)) inf_le_right).2
      (Twist.resM _ inf_le_left q)
    rw [← ht]
    have e := congrArg (fun m => (Scheme.Modules.Hom.app m (V ⊓ Out.nonzeroLocus (Cartier.secPull (ProjSpace.coord k N j) φ))) t) (ha j)
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at e
    rw [e]
    simp
  · intro i j W h t
    have hW : W ≤ ((ProjSpace.O1 k N).pull φ).U (fun _ => i) := h.trans (Cartier.pull_U (ProjSpace.O1 k N) φ fun _ => i).ge
    apply (Twist.chartEquiv hM (fun _ => i) hW).injective
    rw [LinearEquiv.map_smul, Twist.chartEquiv_secHom_app, Twist.chartEquiv_secHom_app,
      ProjSpace.resG_secPull_coord, ProjSpace.resG_secPull_coord, ProjSpace.pullRatio_self, one_smul]

end GlobalTheory.LineQuot

end
end

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_map_universal_line : ∀ (k : Type) [CommRing k] (N : ℕ) (T : Scheme.{0}) (φ : T ⟶ PSpace k N) (L : T.Modules), IsVB L 1 → ∃ (Q : T.Modules) (s : Fin (N + 1) → (L ⟶ Q)), IsVB Q 1 ∧ JointEpi s ∧ Rel φ s := by
  atlas_forward_decl GlobalTheory.LineQuot.exists_taut_quot
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover)

namespace GlobalTheory.ZeroLocus

variable {Y T : Scheme.{0}} {G Q : Y.Modules}

theorem mem_annihilator_cokernel_iff (u : G ⟶ Q) [G.IsQuasicoherent] [Q.IsQuasicoherent]
    {U : Y.Opens} (hU : IsAffineOpen U) {e : Fin 1 → Γ(Q, U)} (he : IsFrame e) (a : Γ(Y, U)) :
    a ∈ Module.annihilator Γ(Y, U) Γ(cokernel u, U) ↔ ∃ t, u.app U t = a • e 0 := by
  have hex := QCoh.exact_cokernel_π_app u hU
  have hsur := QCoh.surjective_cokernel_π_app u hU
  have hsm (b : Γ(Y, U)) (s : Γ(Q, U)) :
      (cokernel.π u).app U (b • s) = b • (cokernel.π u).app U s :=
    Scheme.Modules.Hom.app_smul _ b s
  rw [Module.mem_annihilator]
  constructor
  · intro H
    refine (hex _).1 ?_
    rw [hsm]
    exact H _
  · rintro ⟨t, ht⟩ m
    obtain ⟨s, rfl⟩ := hsur m
    have h0 : a • (cokernel.π u).app U (e 0) = 0 := by
      rw [← hsm]
      exact (hex _).2 ⟨t, ht⟩
    have hs := (he.basis le_rfl).sum_repr s
    rw [Fin.sum_univ_one, IsFrame.basis_apply, resM_self] at hs
    rw [← hs, hsm, smul_comm, h0, smul_zero]

theorem pullbackSections_smul_self (h : T ⟶ Y) {U : Y.Opens} (a : Γ(Y, U)) (s : Γ(Q, U)) :
    QCoh.pullbackSections h Q (le_refl (h ⁻¹ᵁ U)) (a • s) =
      h.app U a • QCoh.pullbackSections h Q (le_refl (h ⁻¹ᵁ U)) s := by
  rw [QCoh.pullbackSections_smul, Scheme.Hom.appLE_eq_app]

theorem eq_zero_of_pullbackSections (f : T ⟶ Y) {E : T.Modules}
    (α : (Scheme.Modules.pullback f).obj G ⟶ E)
    (H : ∀ (V : Y.Opens) (s : Γ(G, V)), α.app _ (QCoh.pullbackSections f G (le_refl (f ⁻¹ᵁ V)) s) = 0) :
    α = 0 := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext s
  have := H V s
  rw [QCoh.pullbackSections_apply] at this
  erw [Twist.resM_self] at this
  exact this

theorem exists_closed_zeroLocus : ∀ (Y : Scheme.{0}) (G Q : Y.Modules) (u : G ⟶ Q), G.IsQuasicoherent → IsVB Q 1 →
    ∃ (Z : Scheme.{0}) (j : Z ⟶ Y), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (h : T ⟶ Y),
      (Scheme.Modules.pullback h).map u = 0 ↔ ∃ h' : T ⟶ Z, h' ≫ j = h := by
  intro Y G Q u hG hQ
  haveI := hQ.isFiniteQC
  let I := QCoh.annihilatorSheaf (cokernel u)
  have hI (U : Y.Opens) (hU : IsAffineOpen U) {e : Fin 1 → Γ(Q, U)} (he : IsFrame e) (a : Γ(Y, U)) :
      (I.subschemeι.app U).hom a = 0 ↔ ∃ t, u.app U t = a • e 0 := by
    rw [← RingHom.mem_ker, I.ker_subschemeι_app ⟨U, hU⟩, QCoh.annihilatorSheaf_ideal]
    exact mem_annihilator_cokernel_iff u hU he a
  refine ⟨I.subscheme, I.subschemeι, inferInstance, fun T h => ⟨fun H => ?_, ?_⟩⟩
  · choose U e hU hy hle he using fun y : Y => hQ.exists_affine (V := ⊤) (x := y) trivial
    refine ProjSpace.exists_lift_of_cover I.subschemeι h U hU
      (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hy y⟩) fun y s hs => ?_
    obtain ⟨t, ht⟩ := (hI _ (hU y) (he y) s).1 hs
    have h1 : ((Scheme.Modules.pullback h).map u).app (h ⁻¹ᵁ U y)
        (QCoh.pullbackSections h G (le_refl _) t) = 0 := by rw [H]; rfl
    rw [QCoh.pullback_map_app_pullbackSections, ht, pullbackSections_smul_self] at h1
    have hf := ((he y).pullback h) (h ⁻¹ᵁ U y) le_rfl
    have : (fun _ : Fin 1 => h.app (U y) s) = 0 := hf.1 (by
      simp only [Fintype.linearCombination_apply, Fin.sum_univ_one, resM_self, map_zero]
      exact h1)
    simpa using congrFun this 0
  · rintro ⟨h', rfl⟩
    refine eq_zero_of_pullbackSections _ _ fun V t => ?_
    rw [QCoh.pullback_map_app_pullbackSections]
    choose W e hW hyW hWV he using fun y : V => hQ.exists_affine y.2
    refine sec_ext_of_cover (fun y => (h' ≫ I.subschemeι) ⁻¹ᵁ W y)
      (fun y => Scheme.Hom.preimage_mono _ (hWV y))
      (fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨_, hx⟩, hyW _⟩) fun y => ?_
    rw [map_zero]
    have e1 := QCoh.res_pullbackSections (h' ≫ I.subschemeι) Q (le_refl ((h' ≫ I.subschemeι) ⁻¹ᵁ V))
      (Scheme.Hom.preimage_mono _ (hWV y)) (u.app V t)
    have e2 := QCoh.pullbackSections_res (h' ≫ I.subschemeι) Q (le_refl ((h' ≫ I.subschemeι) ⁻¹ᵁ W y)) (hWV y)
      (u.app V t)
    refine (e1.trans e2.symm).trans ?_
    obtain ⟨c, hc⟩ := (he y (W y) le_rfl).2 (u.app (W y) (resM G (hWV y) t))
    rw [Fintype.linearCombination_apply, Fin.sum_univ_one, resM_self] at hc
    have ha : (I.subschemeι.app (W y)).hom (c 0) = 0 := (hI _ (hW y) (he y) (c 0)).2 ⟨_, hc.symm⟩
    change QCoh.pullbackSections _ Q _ (resM Q (hWV y) (u.app V t)) = 0
    rw [← app_resM, ← hc, pullbackSections_smul_self]
    have hz : (ConcreteCategory.hom ((h' ≫ I.subschemeι).app (W y))) (c 0) = 0 :=
      (congrArg (h'.app (I.subschemeι ⁻¹ᵁ W y)).hom ha).trans (map_zero _)
    rw [hz, zero_smul]

end GlobalTheory.ZeroLocus

end
end

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vanishing_locus_closed_subscheme : ∀ (Y : Scheme.{0}) (G Q : Y.Modules) (u : G ⟶ Q), G.IsQuasicoherent → IsVB Q 1 → ∃ (Z : Scheme.{0}) (j : Z ⟶ Y), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (h : T ⟶ Y), (Scheme.Modules.pullback h).map u = 0 ↔ ∃ h' : T ⟶ Z, h' ≫ j = h := by
  atlas_forward_decl GlobalTheory.ZeroLocus.exists_closed_zeroLocus
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot

namespace GlobalTheory.Vert.Flag

variable {X : Scheme.{0}} {E K : X.Modules} {r : ℕ}

theorem exists_extend {i : K ⟶ E} (hi : IsSubbundle i) (hE : IsVB E (r + 1)) (fl : Vert.Flag K r) :
    ∃ fl' : Vert.Flag E (r + 1), ∀ j : Fin (r + 1),
      ∃ e : fl'.F j.castSucc ≅ fl.F j, e.hom ≫ fl.ι j ≫ i = fl'.ι j.castSucc := by
  let G : Fin (r + 2) → Σ A : X.Modules, (A ⟶ E) :=
    fun j => Fin.lastCases (motive := fun _ => Σ A : X.Modules, (A ⟶ E)) ⟨E, 𝟙 E⟩
      (fun k => ⟨fl.F k, fl.ι k ≫ i⟩) j
  have hlast : G (Fin.last (r + 1)) = ⟨E, 𝟙 E⟩ := Fin.lastCases_last ..
  have hcast (k : Fin (r + 1)) : G k.castSucc = ⟨fl.F k, fl.ι k ≫ i⟩ := Fin.lastCases_castSucc ..
  have hsub (j : Fin (r + 2)) : IsSubbundle (G j).2 := by
    induction j using Fin.lastCases with
    | last => rw [hlast]; exact VB.isSubbundle_of_isIso _
    | cast k => rw [hcast]; exact isSubbundle_ι_comp hi fl k
  have hvb (j : Fin (r + 2)) : IsVB (G j).1 j := by
    induction j using Fin.lastCases with
    | last => rw [hlast]; exact hE
    | cast k => rw [hcast]; exact fl.isVB k
  have hstep (k : Fin (r + 1)) :
      ∃ f : (G k.castSucc).1 ⟶ (G k.succ).1, f ≫ (G k.succ).2 = (G k.castSucc).2 := by
    induction k using Fin.lastCases with
    | last =>
      rw [Fin.succ_last, hlast, hcast]
      exact ⟨fl.ι _ ≫ i, Category.comp_id _⟩
    | cast k =>
      rw [← Fin.castSucc_succ, hcast, hcast]
      exact ⟨fl.step k, fl.step_ι_assoc k i⟩
  choose step step_ι using hstep
  have hiso : IsIso (G (Fin.last (r + 1))).2 := by
    rw [hlast]; exact IsIso.id E
  refine ⟨⟨fun j => (G j).1, fun j => (G j).2, hsub, hvb, step, step_ι, hiso⟩, fun j => ?_⟩
  change ∃ e : (G j.castSucc).1 ≅ fl.F j, e.hom ≫ fl.ι j ≫ i = (G j.castSucc).2
  rw [hcast]
  exact ⟨Iso.refl _, Category.id_comp _⟩

theorem exists_comp_ι_of_le (fl : Vert.Flag E r) {i j : Fin (r + 1)} (h : i ≤ j) :
    ∃ t : fl.F i ⟶ fl.F j, t ≫ fl.ι j = fl.ι i := by
  induction j using Fin.induction with
  | zero => obtain rfl := Fin.le_zero_iff.1 h; exact ⟨𝟙 _, Category.id_comp _⟩
  | succ j ih =>
    obtain rfl | h' := h.eq_or_lt
    · exact ⟨𝟙 _, Category.id_comp _⟩
    · obtain ⟨t, ht⟩ := ih (Fin.le_castSucc_iff.2 h')
      exact ⟨t ≫ fl.step j, by rw [Category.assoc, fl.step_ι, ht]⟩

theorem exists_trunc {i : K ⟶ E} (fl' : Vert.Flag E (r + 1)) (a : K ≅ fl'.F (Fin.last r).castSucc)
    (ha : a.hom ≫ fl'.ι (Fin.last r).castSucc = i) : ∃ fl : Vert.Flag K r, ∀ j : Fin (r + 1),
      ∃ e : fl.F j ≅ fl'.F j.castSucc, e.hom ≫ fl'.ι j.castSucc = fl.ι j ≫ i := by
  subst ha
  choose t ht using fun j : Fin (r + 1) =>
    fl'.exists_comp_ι_of_le (Fin.castSucc_le_castSucc_iff.2 (Fin.le_last j))
  have hm (j : Fin (r + 1)) : Mono (t j) := mono_of_mono_fac (ht j)
  have hl : t (Fin.last r) = 𝟙 _ := by rw [← cancel_mono (fl'.ι _), ht, Category.id_comp]
  have hs (j : Fin (r + 1)) : IsSubbundle (t j) := by
    refine ⟨hm j, r - j, VB.isVB_X₁_of_shortExact X _ (r - j) _
      (shortExact_cokernel_comp (t j) (fl'.ι (Fin.last r).castSucc)) ?_ (fl'.isVB_cokernel _)⟩
    have h := (fl'.isVB_cokernel j.castSucc).of_iso (cokernelIsoOfEq (ht j).symm)
    rwa [show r + 1 - (j.castSucc : ℕ) = r - j + (r + 1 - ((Fin.last r).castSucc : ℕ)) by
      have := j.2; simp; omega] at h
  let fl : Vert.Flag (fl'.F (Fin.last r).castSucc) r :=
    ⟨fun j => fl'.F j.castSucc, t, hs, fun j => fl'.isVB j.castSucc, fun j => fl'.step j.castSucc, fun j => by
      rw [← cancel_mono (fl'.ι _), Category.assoc, ht, ht]; exact fl'.step_ι j.castSucc,
      by rw [hl]; exact IsIso.id _⟩
  refine ⟨fl.ofIso a.symm, fun j => ⟨Iso.refl _, ?_⟩⟩
  change 𝟙 _ ≫ _ = (t j ≫ a.inv) ≫ _
  simp [ht]

end GlobalTheory.Vert.Flag

namespace GlobalTheory.LineQuot

section Rel

variable {T : Scheme.{0}} {R : Type} [CommRing R] {N : ℕ} {L L' Q Q' : T.Modules} {φ : T ⟶ PSpace R N}
  {s : Fin (N + 1) → (L ⟶ Q)}

theorem Rel.pre (h : Rel φ s) (a : L' ⟶ L) : Rel φ fun j => a ≫ s j :=
  fun i j W hW t => h i j W hW (a.app W t)

theorem Rel.post (h : Rel φ s) (a : Q ⟶ Q') : Rel φ fun j => s j ≫ a := fun i j W hW t =>
  (congrArg (a.app W) (h i j W hW t)).trans (Scheme.Modules.Hom.app_smul ..)

end Rel

theorem map_biproduct_ext {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D] (Φ : C ⥤ D)
    [Φ.Additive] {ι : Type} [Fintype ι] (f : ι → C) [HasBiproduct f] {Z : D} {a b : Φ.obj (⨁ f) ⟶ Z}
    (h : ∀ j, Φ.map (biproduct.ι f j) ≫ a = Φ.map (biproduct.ι f j) ≫ b) : a = b := by
  have e (c : Φ.obj (⨁ f) ⟶ Z) : c = ∑ j, Φ.map (biproduct.π f j) ≫ Φ.map (biproduct.ι f j) ≫ c := by
    simp only [← Functor.map_comp_assoc, ← Preadditive.sum_comp, ← Functor.map_sum, biproduct.total, Φ.map_id,
      Category.id_comp]
  rw [e a, e b]
  simp only [h]

theorem exists_isLineQuot_sum {k : Type} [CommRing k] {B : Scheme.{0}} (q : B ⟶ Sp k) (N : ℕ) {L : B.Modules}
    (hL : IsVB L 1) [HasBiproduct fun _ : Fin (N + 1) => L] :
    ∃ (Q : (pullback q (PSpace.str k N)).Modules) (p : _ ⟶ Q),
      IsLineQuot (pullback.fst q (PSpace.str k N)) (⨁ fun _ : Fin (N + 1) => L) p := by
  classical
  set π := pullback.fst q (PSpace.str k N) with hπ
  set φ₀ := pullback.snd q (PSpace.str k N) with hφ₀
  obtain ⟨Q, s, hQ, hs, hr⟩ := GlobalTheory.T.projective_map_universal_line k N _ φ₀ _ (hL.pullback π)
  let u (j : Fin (N + 1)) : L ⟶ ⨁ fun _ : Fin (N + 1) => L := biproduct.ι (fun _ : Fin (N + 1) => L) j
  obtain ⟨p, hp⟩ : ∃ p : (Scheme.Modules.pullback π).obj (⨁ fun _ : Fin (N + 1) => L) ⟶ Q,
      ∀ j, (Scheme.Modules.pullback π).map (u j) ≫ p = s j :=
    ⟨∑ j, (Scheme.Modules.pullback π).map (biproduct.π _ j) ≫ s j, fun j => by
      simp only [u, Preadditive.comp_sum, ← Functor.map_comp_assoc]
      rw [Finset.sum_eq_single j (fun i _ hi => by rw [biproduct.ι_π_ne _ hi.symm]; simp) (by simp)]
      simp⟩
  have hepi : Epi p := (Preadditive.epi_iff_cancel_zero _).2 fun Z a ha => hs Z a fun j => by
    rw [← hp, Category.assoc, ha, comp_zero]
  refine ⟨Q, p, hQ, hepi, fun T g Q' p' hQ' hp' => ?_⟩
  let s' (j : Fin (N + 1)) := (Scheme.Modules.pullback g).map (u j) ≫ p'
  have hs' : Gen s' := GlobalTheory.T.jointly_epi_sections_generate T _ _ N s' (hL.pullback g) hQ' fun Z a ha => by
    rw [← cancel_epi p']
    exact map_biproduct_ext _ _ fun j => by simpa [s', u] using ha j
  have key (g' : T ⟶ pullback q (PSpace.str k N)) (w : g' ≫ π = g) (e : (Scheme.Modules.pullback g').obj Q ⟶ Q') :
      (Scheme.Modules.pullback g').map p ≫ e = (cmp g' π w).hom.app _ ≫ p' ↔
        ∀ j, (Scheme.Modules.pullback g').map (s j) ≫ e = (cmp g' π w).hom.app _ ≫ s' j := by
    have H (j) : (Scheme.Modules.pullback g').map ((Scheme.Modules.pullback π).map (u j)) ≫
        (Scheme.Modules.pullback g').map p ≫ e = (Scheme.Modules.pullback g').map (s j) ≫ e := by
      rw [← Functor.map_comp_assoc, hp]
    refine ⟨fun h j => by rw [← H, h, cmp_naturality_assoc], fun h =>
      map_biproduct_ext (Scheme.Modules.pullback π ⋙ Scheme.Modules.pullback g') _ fun j => ?_⟩
    exact (H j).trans ((h j).trans (cmp_naturality_assoc g' π w (u j) p').symm)
  obtain ⟨φ, hφ, hφr⟩ := GlobalTheory.T.generating_sections_projective_map k N T (g ≫ q) _ _ s' (hL.pullback g) hQ' hs'
  have w : pullback.lift g φ hφ.symm ≫ π = g := pullback.lift_fst ..
  have w' : pullback.lift g φ hφ.symm ≫ φ₀ = φ := pullback.lift_snd ..
  refine ⟨pullback.lift g φ hφ.symm, ⟨w, ?_⟩, ?_⟩
  · generalize pullback.lift g φ hφ.symm = g' at w w'
    have hj : JointEpi fun j => (Scheme.Modules.pullback g').map (s j) := fun Z a ha => by
      rw [← cancel_epi ((Scheme.Modules.pullback g').map p)]
      refine map_biproduct_ext (Scheme.Modules.pullback π ⋙ Scheme.Modules.pullback g') _ fun j => ?_
      have := ha j
      dsimp only at this
      rw [← hp, Functor.map_comp, Category.assoc] at this
      exact this.trans (by simp)
    have h₁ := (hL.pullback π).pullback g'
    obtain ⟨e, he⟩ := GlobalTheory.T.projective_relation_unique_quotient k N T _ _ Q' _ _ φ h₁ (hQ.pullback g') hj (GlobalTheory.T.jointly_epi_sections_generate T _ _ N _ h₁ (hQ.pullback g') hj)
      (w' ▸ GlobalTheory.T.projective_relation_pullback k N _ _ g' _ _ s φ₀ (hL.pullback π) hQ hr) (hφr.pre ((cmp g' π w).hom.app L))
    exact ⟨e, (key g' w e).2 he⟩
  · rintro g' ⟨w₁, e, he⟩
    have h₁ := ((GlobalTheory.T.projective_relation_pullback k N _ _ g' _ _ s φ₀ (hL.pullback π) hQ hr).post e).pre ((cmp g' π w₁).inv.app L)
    simp only [(key g' w₁ e).1 he, Iso.inv_hom_id_app_assoc] at h₁
    refine pullback.hom_ext (w₁.trans w.symm) (Eq.trans ?_ w'.symm)
    refine GlobalTheory.T.projective_map_unique_of_relation k N T _ _ s' _ _ (hL.pullback g) hQ' hs' ?_ h₁ hφr
    rw [hφ, Category.assoc, ← pullback.condition, ← Category.assoc, w₁]

theorem IsLineQuot.exists_closed {Y B : Scheme.{0}} {π : Y ⟶ B} {F E : B.Modules} [F.IsQuasicoherent]
    [E.IsQuasicoherent] {Q : Y.Modules} {p : (Scheme.Modules.pullback π).obj F ⟶ Q} (h : IsLineQuot π F p)
    (a : F ⟶ E) [Epi a] : ∃ (Z : Scheme.{0}) (j : Z ⟶ Y) (Q₁ : Z.Modules) (p₁ : _ ⟶ Q₁),
      IsClosedImmersion j ∧ IsLineQuot (j ≫ π) E p₁ := by
  obtain ⟨hQ, hp, H⟩ := h
  obtain ⟨Z, j, hj, hZ⟩ := GlobalTheory.T.vanishing_locus_closed_subscheme Y _ Q ((Scheme.Modules.pullback π).map (kernel.ι a) ≫ p) inferInstance hQ
  have hex := (ShortComplex.exact_kernel a).map_of_epi_of_preservesCokernel (Scheme.Modules.pullback (j ≫ π))
    (inferInstanceAs (Epi a)) inferInstance
  have : Epi ((ShortComplex.mk (kernel.ι a) a (kernel.condition a)).map (Scheme.Modules.pullback (j ≫ π))).g :=
    inferInstanceAs (Epi ((Scheme.Modules.pullback (j ≫ π)).map a))
  obtain ⟨p₁, hp₁⟩ : ∃ p₁ : (Scheme.Modules.pullback (j ≫ π)).obj E ⟶ (Scheme.Modules.pullback j).obj Q,
      (Scheme.Modules.pullback (j ≫ π)).map a ≫ p₁ =
        (cmp j π rfl).inv.app F ≫ (Scheme.Modules.pullback j).map p := hex.desc' _ (by
    have := (hZ Z j).2 ⟨𝟙 _, Category.id_comp _⟩
    change (Scheme.Modules.pullback (j ≫ π)).map (kernel.ι a) ≫ _ = _
    rw [← cancel_epi ((cmp j π rfl).hom.app (kernel a)), ← cmp_naturality_assoc, Iso.hom_inv_id_app_assoc,
      ← Functor.map_comp, this, comp_zero])
  refine ⟨Z, j, _, p₁, hj, hQ.pullback j, epi_of_epi_fac hp₁, fun T g Q' p' hQ' hp' => ?_⟩
  have key (h : T ⟶ Z) (g₁ : T ⟶ Y) (w₀ : h ≫ j = g₁) (w₁ : g₁ ≫ π = g) (w : h ≫ j ≫ π = g)
      (e₁ : (Scheme.Modules.pullback g₁).obj Q ⟶ Q') :
      (Scheme.Modules.pullback h).map p₁ ≫ (cmp h j w₀).hom.app Q ≫ e₁ = (cmp h (j ≫ π) w).hom.app E ≫ p' ↔
        (Scheme.Modules.pullback g₁).map p ≫ e₁ =
          (cmp g₁ π w₁).hom.app F ≫ (Scheme.Modules.pullback g).map a ≫ p' := by
    rw [← cancel_epi ((Scheme.Modules.pullback h).map ((Scheme.Modules.pullback (j ≫ π)).map a)),
      ← Functor.map_comp_assoc, hp₁, cmp_naturality_assoc,
      ← cancel_epi ((Scheme.Modules.pullback h).map ((cmp j π rfl).hom.app F)), ← Functor.map_comp_assoc,
      Iso.hom_inv_id_app_assoc, cmp_naturality_assoc, cmp_assoc_assoc h j π rfl w w₀ w₁, cancel_epi]
  obtain ⟨g₁, ⟨w₁, e₁, he₁⟩, hu⟩ := H T g Q' ((Scheme.Modules.pullback g).map a ≫ p') hQ' inferInstance
  have : Epi e₁ := epi_of_epi_fac he₁
  have := SameLine.isIso_of_epi e₁ (hQ.pullback g₁) hQ'
  obtain ⟨h, w₀⟩ := (hZ T g₁).1 (by
    rw [← cancel_mono e₁, Functor.map_comp, Category.assoc, he₁, cmp_naturality_assoc, ← Functor.map_comp_assoc,
      kernel.condition]
    simp)
  have w : h ≫ j ≫ π = g := by rw [← Category.assoc, w₀, w₁]
  refine ⟨h, ⟨w, _, (key h g₁ w₀ w₁ w e₁).2 he₁⟩, ?_⟩
  rintro h' ⟨w', e', he'⟩
  rw [← cancel_mono j, w₀]
  exact hu _ ⟨(Category.assoc ..).trans w', (cmp h' j rfl).inv.app Q ≫ e', (key h' _ rfl _ w' _).1 (by simpa using he')⟩

theorem exists_isLineQuot_isProjOver {k : Type} [CommRing k] {B : Scheme.{0}} {q : B ⟶ Sp k} (hq : IsProjOver q)
    {E : B.Modules} {r : ℕ} (hE : IsVB E r) : ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (Q : Y.Modules) (p : _ ⟶ Q),
      IsLineQuot π E p ∧ IsProjOver (π ≫ q) := by
  have := hE.isFiniteQC
  have := hE.isQuasicoherent
  have := Abelian.hasFiniteBiproducts (C := B.Modules)
  obtain ⟨-, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hq
  obtain ⟨n, N, φ, hφ⟩ := (hA.eventually_exists_epi_sigma E).exists
  have hL := isVB_toMod (Twist.isLB_lbZPow hA.isLB (-n))
  generalize LB.toMod (lbZPow A (-n)) = L at φ hφ hL
  have := hL.isQuasicoherent
  let a : (⨁ fun _ : Fin (N + 1) => L) ⟶ E := biproduct.desc (Fin.cons 0 fun j => Sigma.ι (fun _ => L) j ≫ φ)
  have : Epi a := (Preadditive.epi_iff_cancel_zero _).2 fun Z b hb => by
    rw [← cancel_epi φ]
    refine Sigma.hom_ext _ _ fun j => ?_
    simpa [a] using biproduct.ι _ j.succ ≫= hb
  obtain ⟨Q, p, h⟩ := exists_isLineQuot_sum q N hL
  obtain ⟨Z, j, Q₁, p₁, hj, h₁⟩ := h.exists_closed a
  refine ⟨Z, _, Q₁, p₁, h₁, ?_⟩
  rw [Category.assoc]
  exact ProjSpace.isProjOver_comp_of_isClosedImmersion j
    (ProjSpace.isProjOver_pullback hq ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩)

end GlobalTheory.LineQuot

namespace GlobalTheory.LineQuot

open GlobalTheory.CovTest

theorem isVB_kernel {X : Scheme.{0}} {E Q : X.Modules} {r : ℕ} (hE : IsVB E (r + 1)) (hQ : IsVB Q 1) (p : E ⟶ Q)
    [Epi p] : IsVB (kernel p) r :=
  isVB_X₁_of_shortExact X (.mk (kernel.ι p) p (kernel.condition p)) r 1 { exact := ShortComplex.exact_kernel p } hE hQ

theorem IsLineQuot.tower {B Y₁ Y₂ : Scheme.{0}} {π₁ : Y₁ ⟶ B} {E : B.Modules} {r : ℕ} (hE : IsVB E (r + 1))
    {Q : Y₁.Modules} {p : (Scheme.Modules.pullback π₁).obj E ⟶ Q} (h : IsLineQuot π₁ E p) {π₂ : Y₂ ⟶ Y₁}
    {fl : Unit → Vert.Flag ((Scheme.Modules.pullback π₂).obj (kernel p)) r}
    (h₂ : IsFlagBundle π₂ (fun _ : Unit => kernel p) (fun _ => r) fl) :
    ∃ fl₂, IsFlagBundle (π₂ ≫ π₁) (fun _ : Unit => E) (fun _ => r + 1) fl₂ := by
  obtain ⟨hQ, hp, H⟩ := h
  have hH := isVB_kernel (hE.pullback π₁) hQ p
  have hι : IsSubbundle (kernel.ι p) := isSubbundle_of_shortExact
    (S := .mk (kernel.ι p) p (kernel.condition p)) { exact := ShortComplex.exact_kernel p } hQ
  have hsub {T : Scheme.{0}} (g₁ : T ⟶ Y₁) := SubPull.isSubbundle_pullback _ _ g₁ _ _ _ r hH hι
  have hex {T : Scheme.{0}} (g₁ : T ⟶ Y₁) := (ShortComplex.exact_kernel p).map_of_epi_of_preservesCokernel
    (Scheme.Modules.pullback g₁) hp inferInstance
  obtain ⟨fl₁, hfl₁⟩ := Vert.Flag.exists_extend (hsub π₂) ((hE.pullback π₁).pullback π₂) (fl ())
  choose e₀ he₀ using hfl₁
  refine ⟨fun _ => fl₁.ofIso ((cmp π₂ π₁ rfl).app E), fun T g fl' => ?_⟩
  have hB (g' : T ⟶ Y₂) (g₁ : T ⟶ Y₁) (w₂ : g' ≫ π₂ = g₁) (w₁ : g₁ ≫ π₁ = g) (w : g' ≫ π₂ ≫ π₁ = g) (j : Fin (r + 1)) :
      (Scheme.Modules.pullback g').map (fl₁.ι j.castSucc ≫ (cmp π₂ π₁ rfl).hom.app E) ≫
        (cmp g' (π₂ ≫ π₁) w).hom.app E = (Scheme.Modules.pullback g').map (e₀ j).hom ≫
          ((Scheme.Modules.pullback g').map ((fl ()).ι j) ≫ (cmp g' π₂ w₂).hom.app _) ≫
            (Scheme.Modules.pullback g₁).map (kernel.ι p) ≫ (cmp g₁ π₁ w₁).hom.app E := by
    rw [← he₀]
    simp only [Functor.map_comp, Category.assoc]
    rw [cmp_assoc g' π₂ π₁ rfl w w₂ w₁, cmp_naturality_assoc]
  set i' := (fl' ()).ι (Fin.last r).castSucc with hi'
  have hQ' : IsVB (cokernel i') 1 := by simpa using (fl' ()).isVB_cokernel (Fin.last r).castSucc
  obtain ⟨g₁, ⟨w₁, e, he⟩, hu⟩ := H T g _ (cokernel.π i') hQ' inferInstance
  have : Epi e := epi_of_epi_fac he
  have := SameLine.isIso_of_epi e (hQ.pullback g₁) hQ'
  have := (hsub g₁).mono
  have : Mono ((ShortComplex.mk (kernel.ι p) p (kernel.condition p)).map (Scheme.Modules.pullback g₁)).f := this
  obtain ⟨a, ha⟩ : ∃ a, a ≫ i' = (Scheme.Modules.pullback g₁).map (kernel.ι p) ≫ (cmp g₁ π₁ w₁).hom.app E :=
    (ShortComplex.exact_cokernel i').lift' _ (by
      rw [Category.assoc, ← he, ← Functor.map_comp_assoc, kernel.condition]; simp)
  obtain ⟨b, hb⟩ : ∃ b, b ≫ (Scheme.Modules.pullback g₁).map (kernel.ι p) = i' ≫ (cmp g₁ π₁ w₁).inv.app E :=
    (hex g₁).lift' _ (by
      change _ ≫ (Scheme.Modules.pullback g₁).map p = 0
      rw [← cancel_mono e, Category.assoc, Category.assoc, he]; simp)
  obtain ⟨fl'', hfl''⟩ := Vert.Flag.exists_trunc (fl' ())
    ⟨a, b, by rw [← cancel_mono ((Scheme.Modules.pullback g₁).map (kernel.ι p)), Category.assoc, hb,
      reassoc_of% ha]; simp, by rw [← cancel_mono i', Category.assoc, ha, reassoc_of% hb]; simp⟩ ha
  choose ε hε using hfl''
  obtain ⟨g', ⟨w₂, hδ⟩, hu₂⟩ := h₂ T g₁ fun _ => fl''
  have w : g' ≫ π₂ ≫ π₁ = g := by rw [← Category.assoc, w₂, w₁]
  refine ⟨g', ⟨w, fun _ i => ?_⟩, ?_⟩
  · induction i using Fin.lastCases with
    | last =>
      exact ⟨asIso ((Scheme.Modules.pullback g').map ((fl₁.ofIso ((cmp π₂ π₁ rfl).app E)).ι (Fin.last _)) ≫
        (cmp g' (π₂ ≫ π₁) w).hom.app E) ≪≫ (asIso ((fl' ()).ι (Fin.last _))).symm, by simp [cmp_hom_app]⟩
    | cast j =>
      obtain ⟨δ, hδ⟩ := hδ () j
      refine ⟨(Scheme.Modules.pullback g').mapIso (e₀ j) ≪≫ δ ≪≫ ε j, Eq.trans ?_ (hB g' g₁ w₂ w₁ w j).symm⟩
      rw [cmp_hom_app, ← hδ]
      simp [hε]
  · rintro g'' ⟨w', hη⟩
    have w₂' : g'' ≫ π₂ = g₁ := by
      obtain ⟨η, hη⟩ := hη () (Fin.last r).castSucc
      have w₁' := (Category.assoc ..).trans w'
      have hz := hη.trans (hB g'' _ rfl w₁' w' (Fin.last r))
      have : Epi ((ShortComplex.mk (kernel.ι p) p (kernel.condition p)).map (Scheme.Modules.pullback (g'' ≫ π₂))).g :=
        inferInstanceAs (Epi ((Scheme.Modules.pullback (g'' ≫ π₂)).map p))
      refine hu _ ⟨w₁', (hex (g'' ≫ π₂)).desc' _ ?_⟩
      change (Scheme.Modules.pullback (g'' ≫ π₂)).map (kernel.ι p) ≫ _ = 0
      rw [← cancel_epi ((Scheme.Modules.pullback g'').map ((fl ()).ι (Fin.last r)) ≫ (cmp g'' π₂ rfl).hom.app _),
        ← cancel_epi ((Scheme.Modules.pullback g'').map (e₀ (Fin.last r)).hom), Category.assoc, ← reassoc_of% hz, ← hi']
      simp
    refine hu₂ _ ⟨w₂', fun _ j => ?_⟩
    obtain ⟨η, hη⟩ := hη () j.castSucc
    have hz := hη.trans (hB g'' _ w₂' w₁ w' j)
    refine ⟨((Scheme.Modules.pullback g'').mapIso (e₀ j)).symm ≪≫ η ≪≫ (ε j).symm, ?_⟩
    rw [← cancel_mono ((Scheme.Modules.pullback g₁).map (kernel.ι p) ≫ (cmp g₁ π₁ w₁).hom.app E),
      ← cancel_epi ((Scheme.Modules.pullback g'').map (e₀ j).hom), ← cmp_hom_app, ← hz, Category.assoc, ← hε]
    simp [← Functor.map_comp_assoc]

open ZeroObject in

theorem exists_isFlagBundle_isProjOver : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (B : Scheme.{0}) (q : B ⟶ Sp k) (E : B.Modules) (r : ℕ), IsProjOver q → GlobalTheory.VB.IsVB E r → ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ _ : Unit, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback π).obj E) r), GlobalTheory.CovTest.IsFlagBundle π (fun _ : Unit => E) (fun _ => r) fl ∧ IsProjOver (π ≫ q) := by
  intro k _ _ B q E r hq hE
  induction r generalizing B with
  | zero =>
    have h := hE.pullback (𝟙 B)
    refine ⟨B, 𝟙 B, fun _ => ⟨fun _ => _, fun _ => 𝟙 _, fun _ => isSubbundle_of_isIso _, fun i => by simpa using h,
      finZeroElim, finZeroElim, inferInstance⟩, fun T g fl' => ⟨g, ⟨Category.comp_id g, fun a i => ?_⟩,
        fun _ ⟨w, _⟩ => (Category.comp_id _).symm.trans w⟩, by rwa [Category.id_comp]⟩
    have z := isVB_zero_iff.1 (h.pullback g)
    exact ⟨z.iso (isVB_zero_iff.1 (by simpa using (fl' a).isVB i)), z.eq_of_src _ _⟩
  | succ r ih =>
    obtain ⟨Y₁, π₁, Q, p, h, h₁⟩ := exists_isLineQuot_isProjOver hq hE
    have := h.2.1
    obtain ⟨Y₂, π₂, fl, h₂, h₃⟩ := ih Y₁ (π₁ ≫ q) _ h₁ (isVB_kernel (hE.pullback π₁) h.1 p)
    obtain ⟨fl₂, h₄⟩ := h.tower hE h₂
    exact ⟨Y₂, _, fl₂, h₄, by rwa [Category.assoc]⟩

end GlobalTheory.LineQuot

end
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flag_bundle_proj_vector_bundle : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (B : Scheme.{0}) (q : B ⟶ Sp k) (E : B.Modules) (r : ℕ), IsProjOver q → GlobalTheory.VB.IsVB E r → ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ _ : Unit, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback π).obj E) r), GlobalTheory.CovTest.IsFlagBundle π (fun _ : Unit => E) (fun _ => r) fl ∧ IsProjOver (π ≫ q) := by
  first | exact @GlobalTheory.LineQuot.exists_isFlagBundle_isProjOver | exact GlobalTheory.LineQuot.exists_isFlagBundle_isProjOver | (intros; apply GlobalTheory.LineQuot.exists_isFlagBundle_isProjOver <;> assumption)
end
