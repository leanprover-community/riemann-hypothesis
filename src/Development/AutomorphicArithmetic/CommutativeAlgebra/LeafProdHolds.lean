import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafChartRing
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecSigmaBijectiveStatement
import Development.EtaleCohomology.KummerTheory.InjSlice
import Development.AbelianVarietyTheory.Definitions.Divisors.E5

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Et

theorem UpperTheory.sections_bijective_disjoint_cover :
    ∀ (R : Type) [CommRing R] (G : Shv R) {Y : Scheme.{0}} {ι : Type} (V : ι → Scheme.{0}) (j : ∀ a, V a ⟶ Y) [∀ a, IsOpenImmersion (j a)],
      (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) → (∀ y : Y, ∃ a, y ∈ Set.range (j a)) → Function.Bijective fun (x : Sec G Y) (a : ι) => Sec.res (j a) x := by
  intro R _ G Y ι V j _ hd hc
  have hop : IsOpenImmersion (Sigma.desc j) :=
    isOpenImmersion_sigmaDesc V j (fun a b hab => hd a b hab)
  have htop : (Sigma.desc j).opensRange = ⊤ := by
    refine top_unique fun y _ => ?_
    obtain ⟨a, z, rfl⟩ := hc y
    refine ⟨(Sigma.ι V a) z, ?_⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
  have hiso : IsIso (Sigma.desc j) := isIso_of_isOpenImmersion_of_opensRange_eq_top _ htop
  have hb : Function.Bijective (fun x : Sec G Y => Sec.res (Sigma.desc j) x) := by
    have h1 : ∀ x : Sec G Y, Sec.res (inv (Sigma.desc j)) (Sec.res (Sigma.desc j) x) = x := by
      intro x
      have := congrArg (fun f => (G.obj.map f.op).hom x) (IsIso.inv_hom_id (Sigma.desc j))
      simpa [Sec.res] using this
    have h2 : ∀ x : Sec G (∐ V), Sec.res (Sigma.desc j) (Sec.res (inv (Sigma.desc j)) x) = x := by
      intro x
      have := congrArg (fun f => (G.obj.map f.op).hom x) (IsIso.hom_inv_id (Sigma.desc j))
      simpa [Sec.res] using this
    exact Function.bijective_iff_has_inverse.2 ⟨_, h1, h2⟩
  have heq : (fun (x : Sec G Y) (a : ι) => Sec.res (j a) x) =
      (fun (b : Sec G (∐ V)) (a : ι) => Sec.res (Sigma.ι V a) b) ∘
        (fun x : Sec G Y => Sec.res (Sigma.desc j) x) := by
    funext x a
    have e : G.obj.map (j a).op = G.obj.map (Sigma.desc j).op ≫ G.obj.map (Sigma.ι V a).op := by
      rw [← Functor.map_comp, ← op_comp, Sigma.ι_desc]
    show (G.obj.map (j a).op).hom x = _
    rw [e]
    rfl
  rw [heq]
  exact (GlobalTheory.T.sec_sigma_res_bijective R G V).comp hb

end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Et

theorem UpperTheory.cohomology_representatives :
    SlopeTestRemainingChoices → ∀ (R : Type) [CommRing R] (I : Cx R) (U : Scheme.{0}) (m n k : ℤ), m + 1 = n → n + 1 = k →
      (∀ z : Sec (I.X n) U, Sec.map (I.d n k) z = 0 → ∃ c, Rep z c) ∧ (∀ c, ∃ z : Sec (I.X n) U, Rep z c) ∧
      (∀ (z : Sec (I.X n) U) c, Rep z c → Sec.map (I.d n k) z = 0 ∧ (c = 0 ↔ ∃ y : Sec (I.X m) U, Sec.map (I.d m n) y = z)) ∧
      (∀ (z z' : Sec (I.X n) U) c c', Rep z c → Rep z' c' → Rep (z + z') (c + c') ∧ Rep (z - z') (c - c') ∧ (c = c' ↔ ∃ y : Sec (I.X m) U, z = z' + Sec.map (I.d m n) y)) ∧
      Rep (0 : Sec (I.X n) U) 0 ∧ ∀ (a : ℕ) (z : Sec (I.X n) U) c, Rep z c → Rep (a • z) (a • c) := by
  intro A R _ I U m n k hmn hnk
  have hrep := A.rep R U I m n k hmn hnk
  have hev := (A.evs R (E := sch.obj U) (I := I) (n := n)).1
  have hvan : ∀ (z : Sec (I.X n) U) c, Rep z c →
      Sec.map (I.d n k) z = 0 ∧ (c = 0 ↔ ∃ y : Sec (I.X m) U, Sec.map (I.d m n) y = z) := by
    rintro z c ⟨α, rfl, rfl⟩
    exact hrep.2 α
  have hadd : ∀ (z z' : Sec (I.X n) U) c c', Rep z c → Rep z' c' → Rep (z + z') (c + c') := by
    rintro z z' c c' ⟨α, rfl, rfl⟩ ⟨β, rfl, rfl⟩
    exact ⟨α + β, CohomologyClass.mk_add α β, (hev α.1 β.1 0 n (by simp) U (𝟙 U)).1⟩
  have hsub : ∀ (z z' : Sec (I.X n) U) c c', Rep z c → Rep z' c' → Rep (z - z') (c - c') := by
    rintro z z' c c' ⟨α, rfl, rfl⟩ ⟨β, rfl, rfl⟩
    exact ⟨α - β, CohomologyClass.mk_sub α β, (hev α.1 β.1 0 n (by simp) U (𝟙 U)).2.1⟩
  have hzero : Rep (0 : Sec (I.X n) U) 0 :=
    ⟨0, CohomologyClass.mk_zero _ _ _, (hev 0 0 0 n (by simp) U (𝟙 U)).2.2.1⟩
  refine ⟨?_, ?_, hvan, ?_, hzero, ?_⟩
  · intro z hz
    obtain ⟨α, h0, -⟩ := hrep.1 z hz
    refine ⟨CohomologyClass.mk α, α, rfl, ?_⟩
    rw [h0]
    change ((I.X n).obj.map (𝟙 (op U))).hom z = z
    rw [CategoryTheory.Functor.map_id]
    rfl
  · intro c
    obtain ⟨α, rfl⟩ := c.mk_surjective
    exact ⟨_, α, rfl, rfl⟩
  · intro z z' c c' h h'
    refine ⟨hadd _ _ _ _ h h', hsub _ _ _ _ h h', ?_⟩
    rw [← sub_eq_zero, (hvan _ _ (hsub _ _ _ _ h h')).2]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [hy]; abel⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [hy]; abel⟩
  · intro a z c h
    induction a with
    | zero => simpa using hzero
    | succ a ih => simpa [succ_nsmul] using hadd _ _ _ _ ih h

end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Et

theorem UpperTheory.representatives_additive :
    SlopeTestRemainingChoices → (∀ (R : Type) [CommRing R] (F : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) (n : ℤ) (z : Sec ((res R F).X n) U) (c : H R (sch.obj U) F n), Rep z c → Rep (Sec.res g z) (pull R (sch.map g) F n c)) ∧
      (∀ (R : Type) [CommRing R] (I : Cx R) (U : Scheme.{0}) (n : ℤ) {ι : Type} (t : Finset ι) (z : ι → Sec (I.X n) U) (c : ι → _), (∀ b, Rep (z b) (c b)) → Rep (∑ b ∈ t, z b) (∑ b ∈ t, c b)) ∧
      ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (i : ℤ) (ζ : Prim q Γ(U, ⊤)), Rep (resGen i ζ) (rootClass i ζ) := by
  intro A
  refine ⟨?_, ?_, ?_⟩
  · rintro R _ F V U g n z c ⟨α, rfl, rfl⟩
    refine ⟨zcomp (Cocycle.ofHom ((chains R).map (sch.map g))) α (zero_add n), rfl, ?_⟩
    have h4 := (A.evs R).2.2.2.1 (sch.map g) α.1 0 n (by simp) V (𝟙 V : V ⟶ V)
    have h2 := (A.evs R).2.1 α.1 0 n (by simp) V U g (𝟙 U : U ⟶ U)
    have e1 : Sx.map (sch.map g) (p := 0) (𝟙 V : V ⟶ V) = g := Category.id_comp g
    have e2 : Sx.res g (E := sch.obj U) (p := 0) (𝟙 U : U ⟶ U) = Sx.map (sch.map g) (p := 0) (𝟙 V : V ⟶ V) := e1.symm ▸ Category.comp_id g
    exact (h4.trans (congrArg (ev α.1 0 n (by simp) V) e2.symm)).trans h2.symm
  · intro R _ I U n ι t z c h
    classical
    have hr := UpperTheory.cohomology_representatives A R I U (n - 1) n (n + 1) (by omega) rfl
    induction t using Finset.induction_on with
    | empty => simpa using hr.2.2.2.2.1
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (hr.2.2.2.1 _ _ _ _ (h a) ih).1
  · intro q _ U i ζ
    obtain ⟨α, hα⟩ := (rootClass i ζ).mk_surjective
    refine ⟨α, hα, ?_⟩
    rw [(A.unit q).2.2.2 i U ζ] at hα
    exact ((A.sec _ (tw q i) U).1 (twGen i ζ) α).2 hα

end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Et

theorem UpperTheory.leafProd_holds :
    LeafProd := by
  intro _ R _ F Y ι V j _ hd hc n
  have A : SlopeTestRemainingChoices := ⟨GlobalTheory.T.etaleSheafSections_ext_and_glue, GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness, GlobalTheory.T.free_sections_ext_res_map, GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties, GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff,
    GlobalTheory.T.degreeZeroSectionClass_properties, GlobalTheory.T.cup_eq_class_of_isAW, GlobalTheory.T.tateTwist_sections_locally_generated, GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique, GlobalTheory.T.tateTwistUnitClass_rootClass_spec⟩
  have hsec := fun G : Shv R => UpperTheory.sections_bijective_disjoint_cover R G V j hd hc
  have hr := fun U : Scheme.{0} => UpperTheory.cohomology_representatives A R (res R F) U (n - 1) n (n + 1) (by omega) rfl
  have hp := fun {A' B' : Scheme.{0}} (g : A' ⟶ B') => (UpperTheory.representatives_additive A).1 R F g n
  have hnat : ∀ {G G' : Shv R} (φ : G ⟶ G') {A' B' : Scheme.{0}} (k : A' ⟶ B') (x : Sec G B'),
      Sec.map φ (Sec.res k x) = Sec.res k (Sec.map φ x) := by
    intro G G' φ A' B' k x
    exact ConcreteCategory.congr_hom (φ.hom.naturality k.op) x
  have hadd : ∀ {G : Shv R} {A' B' : Scheme.{0}} (k : A' ⟶ B') (x y : Sec G B'),
      Sec.res k (x + y) = Sec.res k x + Sec.res k y := by
    intro G A' B' k x y
    exact map_add _ x y
  have hzero : ∀ {G G' : Shv R} (φ : G ⟶ G') {A' : Scheme.{0}}, Sec.map φ (0 : Sec G A') = 0 := by
    intro G G' φ A'
    exact map_zero _
  have hzero' : ∀ {G : Shv R} {A' B' : Scheme.{0}} (k : A' ⟶ B'), Sec.res k (0 : Sec G B') = 0 := by
    intro G A' B' k
    exact map_zero _
  constructor
  · intro x x' h
    obtain ⟨z, hz⟩ := (hr Y).2.1 x
    obtain ⟨z', hz'⟩ := (hr Y).2.1 x'
    have hy : ∀ a, ∃ y : Sec ((res R F).X (n - 1)) (V a),
        Sec.res (j a) z = Sec.res (j a) z' + Sec.map ((res R F).d (n - 1) n) y := by
      intro a
      have h1 := hp (j a) z x hz
      have h2 := hp (j a) z' x' hz'
      exact ((hr (V a)).2.2.2.1 _ _ _ _ h1 h2).2.2.1 (congrFun h a)
    choose y hy using hy
    obtain ⟨Y', hY⟩ := (hsec ((res R F).X (n - 1))).2 y
    have hzz : z = z' + Sec.map ((res R F).d (n - 1) n) Y' := by
      apply (hsec ((res R F).X n)).1
      funext a
      have hYa : Sec.res (j a) Y' = y a := congrFun hY a
      change Sec.res (j a) z = Sec.res (j a) (z' + Sec.map ((res R F).d (n - 1) n) Y')
      rw [hadd, ← hnat, hYa]
      exact hy a
    exact ((hr Y).2.2.2.1 _ _ _ _ hz hz').2.2.2 ⟨Y', hzz⟩
  · intro c
    have hz := fun a => (hr (V a)).2.1 (c a)
    choose z hz using hz
    obtain ⟨Z, hZ⟩ := (hsec ((res R F).X n)).2 z
    have hZa : ∀ a, Sec.res (j a) Z = z a := fun a => congrFun hZ a
    have hcl : Sec.map ((res R F).d n (n + 1)) Z = 0 := by
      apply (hsec ((res R F).X (n + 1))).1
      funext a
      change Sec.res (j a) (Sec.map ((res R F).d n (n + 1)) Z) = Sec.res (j a) 0
      rw [← hnat, hZa, hzero']
      exact ((hr (V a)).2.2.1 _ _ (hz a)).1
    obtain ⟨C, hC⟩ := (hr Y).1 Z hcl
    refine ⟨C, ?_⟩
    funext a
    have h1 := hp (j a) Z C hC
    rw [hZa] at h1
    refine ((hr (V a)).2.2.2.1 _ _ _ _ h1 (hz a)).2.2.2 ⟨0, ?_⟩
    rw [hzero, add_zero]

end
end
