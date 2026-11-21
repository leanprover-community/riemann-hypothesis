import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObject
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPrincipalDim
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.Xgn.TateIsomorphismDescent

theorem exists_weilIs (S : Scheme.{0}) (P : Out.PolAV S) (k : ℕ) (T : Over S) (x y : T ⟶ P.A) (hx : x ^ k = 1)
    (hy : y ^ k = 1) : ∃ c : Γ(T.left, ⊤)ˣ, Out.WeilIs P.A P.L k x y c :=
  (GlobalTheory.CommutatorPairing.existsUnique_weilIs GlobalTheory.abelianSchemeLaws_all.1.globalFns
    (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube GlobalTheory.AbLaw.CubeAssembly.cube_and_sections.1).1).2.2
    S P k T x y hx hy).exists

theorem exists_root {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed K] (i : K →+* Ω) {n : ℕ} (hn : 0 < n) (z : Ωˣ)
    (hz : z ^ n = 1) : ∃ w : Kˣ, Units.map i.toMonoidHom w = z := by
  have hz' : (z : Ω) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, hz, Units.val_one]
  have hs : (Polynomial.X ^ n - Polynomial.C 1 : Polynomial K).Splits := IsAlgClosed.splits _
  have hne : (Polynomial.X ^ n - Polynomial.C 1 : Polynomial K) ≠ 0 := Polynomial.X_pow_sub_C_ne_zero hn 1
  have hm : (z : Ω) ∈ ((Polynomial.X ^ n - Polynomial.C 1 : Polynomial K).map i).roots := by
    rw [Polynomial.mem_roots (Polynomial.map_ne_zero hne)]
    simp [hz']
  rw [hs.roots_map_of_injective i.injective] at hm
  obtain ⟨w, -, hw⟩ := Multiset.mem_map.1 hm
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact z.ne_zero (hw.symm.trans (map_zero i))
  exact ⟨Units.mk0 w hw0, Units.ext hw⟩

end PositivityTheory.Xgn.TateIsomorphismDescent

theorem PositivityTheory.Xgn.tate_isomorphism_descends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) (P : Out.PolAV S) (act : 𝓞 E → (P.A ⟶ P.A)), (∀ c, IsMonHom (act c)) → ∀ (K Ω : Type) [Field K] [Field Ω] [IsAlgClosed K] [IsAlgClosed Ω] [CharZero K] (i : K →+* Ω) (x : Sp K ⟶ S) (x' : Sp Ω ⟶ S) (u : Over.mk x' ⟶ Over.mk x), u.left = spMap i → ∀ I' : TateIso D Ω (Over.mk x' ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∃ I : TateIso D K (Over.mk x ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∀ n v, 0 < n → I'.ev n v = u ≫ I.ev n v := by
  intro E _ _ _ H D S P act hact K Ω _ _ _ _ _ i x x' u hu I'
  have laws := GlobalTheory.abelianSchemeLaws_all.1
  have : CharZero Ω := (RingHom.charZero_iff i.injective).1 ‹_›
  let f : (Over.mk x ⟶ P.A) →* (Over.mk x' ⟶ P.A) := MonoidHom.mk' (u ≫ ·) (MonObj.comp_mul u)
  have hinj : Function.Injective f := GlobalTheory.TorsionFieldExt.comp_injective u P.A
  have ginj : Function.Injective (Units.map i.toMonoidHom : Kˣ →* Ωˣ) := Units.map_injective i.injective
  have hu' : ∀ c : Kˣ, unitOn (Units.map i.toMonoidHom c) = Units.map u.left.appTop.hom.toMonoidHom (unitOn c) :=
    fun c => by
      rw [hu]
      exact Units.ext (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i)))
  have hev : ∀ (n : ℕ) (v : D.La), ∃ y : Over.mk x ⟶ P.A, (n = 0 → y = 1) ∧ (0 < n → f y = I'.ev n v) := by
    intro n v
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨1, fun _ => rfl, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨y, -, hy⟩ := GlobalTheory.TorsionFieldExt.exists_of_isAlgClosed laws P u (Nat.cast_ne_zero.2 hn.ne')
        (Nat.cast_ne_zero.2 hn.ne') (I'.ev n v) ((I'.onto n hn _).2 ⟨v, rfl⟩)
      exact ⟨y, fun h => absurd h hn.ne', fun _ => hy⟩
  choose ev ev0 evp using hev
  have hζ : ∀ n : ℕ, ∃ w : Kˣ, 0 < n → Units.map i.toMonoidHom w = I'.ζ n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨1, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨w, hw⟩ := PositivityTheory.Xgn.TateIsomorphismDescent.exists_root i hn (I'.ζ n) (I'.ζ_prim n hn).pow_eq_one
      exact ⟨w, fun _ => hw⟩
  choose ζ hζ using hζ
  have tors : ∀ n, 0 < n → ∀ a, ev n a ^ n = 1 := fun n hn a => hinj (by
    rw [map_pow, evp n a hn, map_one]; exact (I'.onto n hn _).2 ⟨a, rfl⟩)
  refine ⟨{ ζ := ζ
            ζ_prim := fun n hn => IsPrimitiveRoot.of_map_of_injective (f := (Units.map i.toMonoidHom : Kˣ →* Ωˣ))
              (by rw [hζ n hn]; exact I'.ζ_prim n hn) ginj
            ζ_pow := fun n m hn hm => ginj (by
              rw [map_pow, hζ _ (Nat.mul_pos hn hm), hζ n hn, I'.ζ_pow n m hn hm])
            ev := ev
            add := fun n a b => ?_
            lin := fun n c a => ?_
            ker := fun n hn a => by rw [← I'.ker n hn a, ← evp n a hn, map_eq_one_iff f hinj]
            onto := fun n hn z => ⟨fun hz => ?_, ?_⟩
            tower := fun n m hn hm a => hinj (by
              rw [map_pow, evp _ a (Nat.mul_pos hn hm), evp n a hn, I'.tower n m hn hm])
            isom := fun n hn a b => ?_ }, fun n v hn => (evp n v hn).symm⟩
  · rcases Nat.eq_zero_or_pos n with h | hn
    · rw [ev0 n _ h, ev0 n _ h, ev0 n _ h, _root_.mul_one]
    · exact hinj (by rw [map_mul, evp n _ hn, evp n _ hn, evp n _ hn, I'.add])
  · rcases Nat.eq_zero_or_pos n with h | hn
    · have := hact c
      rw [ev0 n _ h, ev0 n _ h]
      exact (MonObj.one_comp (act c)).symm
    · refine hinj ?_
      rw [evp n _ hn, I'.lin, ← evp n a hn]
      exact Category.assoc u (ev n a) (act c)
  · obtain ⟨a, ha⟩ := (I'.onto n hn (f z)).1 (by rw [← map_pow, hz, map_one])
    exact ⟨a, hinj ((evp n a hn).trans ha)⟩
  · rintro ⟨a, rfl⟩
    exact tors n hn a
  · obtain ⟨c, hc⟩ := PositivityTheory.Xgn.TateIsomorphismDescent.exists_weilIs S P n _ _ _ (tors n hn a) (tors n hn b)
    obtain ⟨w, rfl⟩ : ∃ w : Kˣ, unitOn w = c :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.toMonoidHom c,
        Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of K)) c.val)⟩
    have h₁ := GlobalTheory.CommPairing.weilIs_pull laws.globalFns P.isAb P.isLB u hc
    rw [← hu'] at h₁
    have h₂ := I'.isom n hn a b
    rw [← evp n a hn, ← evp n b hn, ← hζ n hn, ← map_zpow] at h₂
    have e := ginj (GlobalTheory.weilIs_unique_fieldPoint S P.A P.L P.isLB Ω x' n _ _ _ _ h₁ h₂)
    rw [← e]
    exact hc
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.Xgn.ModelSectionsTransport

theorem exists_common {F K L : Type} [Field F] [Field K] [Field L] (g : F →+* K) (h : F →+* L) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (i : K →+* Ω) (j : L →+* Ω), i.comp g = j.comp h := by
  letI := g.toAlgebra
  letI := h.toAlgebra
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[F] L)
  letI : Field ((K ⊗[F] L) ⧸ m) := Ideal.Quotient.field m
  let q : K ⊗[F] L →+* AlgebraicClosure ((K ⊗[F] L) ⧸ m) :=
    (algebraMap ((K ⊗[F] L) ⧸ m) (AlgebraicClosure ((K ⊗[F] L) ⧸ m))).comp (Ideal.Quotient.mk m)
  refine ⟨AlgebraicClosure ((K ⊗[F] L) ⧸ m), inferInstance, inferInstance,
    q.comp Algebra.TensorProduct.includeLeftRingHom,
    q.comp (Algebra.TensorProduct.includeRight : L →ₐ[F] K ⊗[F] L).toRingHom, ?_⟩
  have e := Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := F) (A := K) (B := L)
  rw [RingHom.comp_assoc, RingHom.comp_assoc]
  exact congrArg (q.comp ·) e

theorem exists_transport {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {F K L : Type} [Field F] [Field K] [Field L] [IsAlgClosed K] [IsAlgClosed L] [CharZero F]
    (t : SAB H (Sp F)) (ht : IsPrincipal t) (g : F →+* K) (h : F →+* L)
    (I : TateIso D L (Over.mk (spMap h) ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))) :
    ∃ J : TateIso D K (Over.mk (spMap g) ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)),
      ∀ n, 0 < n → ∀ v (s : 𝟙_ (Over (Sp F)) ⟶ t.G), toUnit _ ≫ s = I.ev n v → toUnit _ ≫ s = J.ev n v := by
  obtain ⟨Ω, _, _, i, j, hij⟩ := exists_common g h
  haveI : CharZero K := charZero_of_injective_ringHom g.injective
  haveI : CharZero L := charZero_of_injective_ringHom h.injective
  let uK : Over.mk (spMap (i.comp g)) ⟶ Over.mk (spMap g) :=
    Over.homMk (spMap i) (spMap_comp g i).symm
  let uL : Over.mk (spMap (i.comp g)) ⟶ Over.mk (spMap h) :=
    Over.homMk (spMap j) (by rw [hij, spMap_comp]; rfl)
  obtain ⟨I', -, hI'⟩ := GlobalTheory.FullPoint.exists_tateIso_up (D := D)
    GlobalTheory.abelianSchemeLaws_all.1 (SabModel.pol t ht) t.act.act j uL rfl I
  obtain ⟨J, hJ⟩ := PositivityTheory.Xgn.tate_isomorphism_descends E H D (Sp F) (SabModel.pol t ht)
    t.act.act t.act.hom K Ω i _ _ uK rfl I'
  refine ⟨J, fun n hn v s hs => ?_⟩
  apply GlobalTheory.TorsionFieldExt.comp_injective uK t.G
  show uK ≫ (toUnit _ ≫ s) = uK ≫ J.ev n v
  rw [← hJ n v hn, hI' n v, ← hs, ← Category.assoc,
    toUnit_unique (uK ≫ toUnit _) (uL ≫ toUnit _), Category.assoc]
  rfl

end PositivityTheory.Xgn.ModelSectionsTransport

theorem PositivityTheory.Xgn.model_object_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (F : IntermediateField ℚ ℂ) (hK : KA l ≤ F) (t : SAB H (Sp F)), IsPrincipal t → l.A = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k] (g : F →+* k) (τ : 𝓞 E →+* k), (τ H.rt = g (IntermediateField.inclusion hK (baseKA l).ρ) → LieMult t.act (spMap g) τ D.p) ∧ (τ H.rt ≠ g (IntermediateField.inclusion hK (baseKA l).ρ) → LieMult t.act (spMap g) τ D.q)) → ∀ I : TateIso D ℂ (Over.mk (spMap (algebraMap F ℂ)) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), (∀ a : D.La, ∃ s : 𝟙_ (Over (Sp F)) ⟶ t.G, toUnit _ ≫ s = I.ev l.M a) → ∃ o : Obj D l (baseKA l) (spMap (IntermediateField.inclusion hK).toRingHom), o.t = t := by
  intro E _ _ _ H D l F hK t ht hA hLie I hsec
  obtain ⟨hpr, ham, hkt⟩ := id ht
  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨e, he, e', he', hee⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp l.coprime)
  choose eta heta using fun a => hsec (e' • a)
  have inj := GlobalTheory.TorsionFieldExt.comp_injective (x := 𝟙 (Sp F))
    (toUnit (Over.mk (spMap (algebraMap F ℂ)))) t.G
  refine ⟨⟨t, hpr, ham, hkt, eta, fun a c => inj ?_, fun a ha => inj ?_, fun _ => 1,
    fun _ _ => (mul_one 1).symm, fun _ => rfl, ?_⟩, rfl⟩
  · show toUnit _ ≫ eta (a + c) = toUnit _ ≫ (eta a * eta c)
    rw [comp_mul, heta, heta, heta, smul_add, I.add]
  · show toUnit _ ≫ eta a = toUnit _ ≫ 1
    rw [MonObj.comp_one, heta]
    obtain ⟨c, hc⟩ := GlobalTheory.FullPoint.exists_eq_nsmul (D := D) l ((mul_comm _ _).trans l.prod) he' ha
    exact (I.ker _ hM _).mpr ⟨c, hc⟩
  intro k _ _ x β hx
  obtain ⟨g, rfl⟩ : ∃ g : F →+* k, x = spMap g :=
    ⟨(Spec.preimage x).hom, by simp [spMap, Spec.map_preimage]⟩
  have hβ : β = g.comp (IntermediateField.inclusion hK).toRingHom :=
    GlobalTheory.FullPoint.spMap_inj (by rw [spMap_comp]; exact hx.symm)
  subst hβ
  obtain ⟨J, hJ⟩ := PositivityTheory.Xgn.ModelSectionsTransport.exists_transport D t ht g (algebraMap F ℂ) I
  refine ⟨fun τ => hLie k g τ, J, ?_, fun a => ?_, fun a ha => ?_⟩
  · have a1 : J.ζ l.A = 1 := by
      have h := J.ζ_prim l.A l.A_pos
      rw [hA] at h ⊢
      exact IsPrimitiveRoot.one_right_iff.mp h
    have b1 : (baseKA l).ζ = 1 := by
      have h := (baseKA l).ζ_prim
      rw [hA] at h
      exact IsPrimitiveRoot.one_right_iff.mp h
    rw [a1, b1, map_one, Units.val_one]
  · simp only [MonObj.comp_one]
    symm
    rw [hA]
    exact (J.ker 1 one_pos a).mpr ⟨a, (one_smul ℕ a).symm⟩
  · rw [hJ l.M hM (e' • a) (eta a) (heta a)]
    obtain ⟨c, hc⟩ := GlobalTheory.FullPoint.exists_eq_nsmul (D := D) l l.prod he ha
    have h0 : J.ev l.M (e • a) = 1 := (J.ker _ hM _).mpr ⟨c, hc⟩
    calc J.ev l.M (e' • a) = J.ev l.M (e • a) * J.ev l.M (e' • a) := by rw [h0, _root_.one_mul]
      _ = J.ev l.M a := by rw [← J.add, ← add_smul, hee, one_smul]
end
