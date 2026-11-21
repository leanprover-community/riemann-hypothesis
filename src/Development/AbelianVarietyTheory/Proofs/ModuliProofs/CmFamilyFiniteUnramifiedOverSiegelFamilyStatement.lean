import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenOfIsLocallyNoetherian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelDataPullbackOfLevelMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperOfCompleteDVRLiftGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEquivStdSymp
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverIffLocallyOfFiniteTypeAndExistsIsAmpl
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCyclotomicBaseRingInvertingPrime
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InjectiveOfApplyEqGenericPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelObjectPullbackExistsAndFull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullObjectOfGenericFibreDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfSurjectiveAppTopOfSection
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SubsingletonSpDualNumber
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarizedCMExtensionDvrStatement

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.FullSiegel

open CechPic

section Bundle

theorem pull_eq_zero_of_chart {X Y : Scheme.{0}} {D : LB X} (hD : D.IsLB) (f : Y ⟶ X) (i : D.ι)
    (hf : ∀ y, f y ∈ D.U i) : pull f (cls D hD) = 0 := by
  rw [← cls_pull hD f (pull_isLB hD f), cls_eq_zero_iff]
  have le : ∀ J : PUnit → D.ι, (D.pull f).U J ≤ f ⁻¹ᵁ (D.U (J PUnit.unit) ⊓ D.U i) :=
    fun J y hy => ⟨mem_pull.1 hy, hf y⟩
  refine ⟨⟨fun J => res (le J) (pullU f _ (D.g (J PUnit.unit) i))⟩, fun J J' => unit_ext fun y hy => ?_⟩
  have val : ∀ J, y ∈ (D.pull f).U J → gm (𝟙 Y) y _ (res (le J) (pullU f _ (D.g (J PUnit.unit) i))) =
      gm (𝟙 Y ≫ f) y _ (D.g (J PUnit.unit) i) := fun J hJ =>
    (gm_res (𝟙 Y) y (le J) hJ _).trans (gm_pull (𝟙 Y) f y _ (le J hJ) _)
  refine ((gm_res (𝟙 Y) y _ hy _).trans (val J hy.1)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull_g D f (𝟙 Y) y J J' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (val J' hy.2)))).trans ?_
  exact gm_cocycle hD (𝟙 Y ≫ f) y (mem_pull.1 hy.1) (mem_pull.1 hy.2) (hf y)

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left}

theorem isLB_lam (hL : L.IsLB) : (abelian₂ G L).IsLB := LB.isLB_linComb hL _ _

theorem cls_lam_pull (hL : L.IsLB) {T : Over S} (x y : T ⟶ G) :
    cls _ (pull_isLB (isLB_lam hL) (lift x y).left) = lam (cls L hL) x y := by
  rw [cls_pull (isLB_lam hL), show cls (abelian₂ G L) (isLB_lam hL) = lam (cls L hL) (fst G G) (snd G G) from
    cls_cube_two hL _ _ _, pull_lam, lift_fst, lift_snd]

theorem lam_symm [IsCommMonObj G] (hL : L.IsLB) :
    LBIso (abelian₂ G L) ((abelian₂ G L).pull (lift (snd G G) (fst G G)).left) := by
  rw [← cls_eq_iff (isLB_lam hL) (pull_isLB (isLB_lam hL) _), cls_lam_pull hL, lam_comm]
  exact cls_cube_two hL _ _ _

theorem pull_one (hL : L.IsLB) (hr : Out.Rigidified G L) (T : Over S) :
    pull (1 : T ⟶ G).left (cls L hL) = 0 := by
  have e := (cls_eq_zero_iff (pull_isLB hL _)).2 hr
  rw [cls_pull hL] at e
  have e' := congrArg (pull (toUnit T).left) e
  rwa [map_zero, ← pull_comp] at e'

theorem eq_one_of_lam_triv (hL : L.IsLB) (hr : Out.Rigidified G L) (hK : Out.KTriv G L) (T : Over S) (x : T ⟶ G)
    (h : ∃ t : ((abelian₂ G L).pull (lift (snd G T ≫ x) (fst G T)).left).Gen, t.IsGen) : x = 1 := by
  have e := (cls_eq_zero_iff (pull_isLB (isLB_lam hL) _)).2 h
  rw [cls_lam_pull hL] at e
  have e' := congrArg (pull (lift (snd T G) (fst T G)).left) e
  rw [map_zero, pull_lam, lift_fst, lift_snd_assoc, lam, pull_one hL hr, add_zero] at e'
  refine KerPow.eq_one_of_locGen hK x fun p => ?_
  obtain ⟨i, hi⟩ := exists_chart hL (x.left p)
  refine ⟨x.left ⁻¹ᵁ L.U i, hi, (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_⟩
  have z := pull_eq_zero_of_chart hL (((fst T G).left ⁻¹ᵁ (x.left ⁻¹ᵁ L.U i)).ι ≫ (fst T G ≫ x).left) i
    fun y => y.2
  have e'' := congrArg (pull ((fst T G).left ⁻¹ᵁ (x.left ⁻¹ᵁ L.U i)).ι) e'
  rw [map_zero, map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, z, sub_zero] at e''
  rw [cls_linComb hL, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, ← sub_eq_add_neg]
  exact e''

theorem cls_diag (hM : Out.MulPullSt) [IsLocallyNoetherian S] (P : Out.PolAV S) :
    cls _ (pull_isLB (isLB_lam P.isLB) (lift (𝟙 P.A) (𝟙 P.A)).left) = 2 • cls P.L P.isLB := by
  have e := (cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2 (hM S P 2)
  rw [cls_linComb P.isLB, Fin.sum_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_id, neg_smul, one_smul, Out.mulA, pow_two] at e
  rw [cls_lam_pull P.isLB, lam, pull_one P.isLB P.rigid, Over.id_left, pull_id, ← add_neg_eq_zero.1 e]
  norm_num
  abel

theorem weilIs_sq (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme G) (hL : L.IsLB) {M : LB G.left} (hM : M.IsLB)
    (e : cls M hM = 2 • cls L hL) {n : ℤ} {T : Over S} {x y : T ⟶ G} {c : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs G L n x y c) : Out.WeilIs G M n x y (c ^ 2) := by
  have up : ∀ (T' : Over S) (θ : Out.ThetaGrp G L n T'), ∃ θ' : Out.ThetaGrp G M n T', θ'.pt = θ.pt := by
    intro T' θ
    have z := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨θ.φ, θ.isGen⟩
    obtain ⟨φ, hφ⟩ : ∃ t : LB.Gen (Out.thetaLB G M n θ.pt), t.IsGen := by
      refine (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).1 ?_
      rw [cls_linComb hL] at z
      rw [cls_linComb hM, e]
      simp only [map_nsmul, smul_comm _ (2 : ℕ), ← Finset.smul_sum, z, smul_zero]
    exact ⟨⟨θ.pt, φ, hφ⟩, rfl⟩
  obtain ⟨c', hc'⟩ := CommutatorPairing.exists_weilIs (k := n) (x := x) (y := y) hG hA hM
    (fun p => by
      obtain ⟨V, hV, ⟨θ, -, hθ, -⟩, -⟩ := h p
      obtain ⟨θ', h'⟩ := up _ θ
      exact ⟨V, hV, θ', h'.trans hθ⟩)
    (fun p => by
      obtain ⟨V, hV, ⟨-, θ, -, hθ⟩, -⟩ := h p
      obtain ⟨θ', h'⟩ := up _ θ
      exact ⟨V, hV, θ', h'.trans hθ⟩)
  have w : LBIso (lbPow L 2) (M.pull (𝟙 G : G ⟶ G).left) := by
    rw [← cls_eq_iff (isLB_lbPow hL 2) (pull_isLB hM _), cls_lbPow hL, cls_pull hM, Over.id_left, pull_id, e]
  rw [← (weilIs_along_hom hG S G G (𝟙 G) L M 2 n T x y c c' hA hA hL hM inferInstance w (by simpa using hc')).2 h]
  exact hc'

end Bundle

section Points

theorem exists_geomPt {X : Scheme.{0}} (y : X) (hy : CharZero (X.residueField y)) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharZero k) (z : Sp k ⟶ X), ∀ u, z u = y :=
  ⟨AlgebraicClosure (X.residueField y), inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField y) _)) ≫ X.fromSpecResidueField y,
    fun _ => Scheme.fromSpecResidueField_apply y _⟩

theorem smoothOfRelativeDimension_of_charZero {X S : Scheme.{0}} (f : X ⟶ S) [Smooth f] [GeometricallyConnected f]
    (d : ℕ) (hS : ∀ x : S, ∃ ξ : S, ξ ⤳ x ∧ CharZero (S.residueField ξ))
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (m : ℕ),
      SmoothOfRelativeDimension m (pullback.snd f x) → m = d) : SmoothOfRelativeDimension d f := by
  choose n W hW hd using H1.exists_dim f
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  obtain ⟨ξ, hξ, h0⟩ := hS (f y)
  obtain ⟨y', hy', rfl⟩ := hξ.mem_open (f.isOpenMap _ (W y).isOpen) ⟨y, hW y, rfl⟩
  obtain ⟨k, _, _, _, z, hz⟩ := exists_geomPt y'
    (charZero_of_injective_ringHom (f.residueFieldMap y').hom.injective)
  let x : Sp k ⟶ S := z ≫ f
  have : ConnectedSpace ↥(pullback f x) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) x _ _ (IsPullback.of_hasPullback _ _)
  let z' : Sp k ⟶ pullback f x := pullback.lift z (𝟙 _) (Category.id_comp _).symm
  obtain ⟨m, hm⟩ := exists_dim_of_preconnected (pullback.snd f x) (z' (default : PrimeSpectrum k))
  have e₁ : n y = m := H1.dim_base (IsPullback.of_hasPullback _ _) (hd y) hm (z' (default : PrimeSpectrum k)) (by
    have e : z' ≫ pullback.fst f x = z := pullback.lift_fst _ _ _
    have e' := (congrArg (fun q : Sp k ⟶ X => q (default : PrimeSpectrum k)) e).trans (hz _)
    exact (congrArg (fun u => u ∈ W y) e').mpr hy')
  rw [← h k x m hm, ← e₁]
  exact hd y

theorem unitOn_pull {O k : Type} [CommRing O] [CommRing k] {T : Scheme.{0}} (s : T ⟶ Sp O) (x : Sp k ⟶ T)
    (w : O →+* k) (h : x ≫ s = spMap w) (u : Oˣ) :
    Units.map x.appTop.hom.toMonoidHom (Units.map s.appTop.hom.toMonoidHom (unitOn u)) =
      unitOn (Units.map w.toMonoidHom u) := by
  ext
  change (s.appTop ≫ x.appTop).hom _ = _
  rw [← Scheme.Hom.comp_appTop, h]
  exact congrArg (fun q => q.hom (u : O)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom w)).symm

theorem unitOn_injective {k : Type} [CommRing k] : Function.Injective (unitOn (R := k)) :=
  Units.map_injective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).1

end Points

section Algebra

theorem onto_of_card {La Q Q' : Type} [AddCommGroup La] [Group Q] [Group Q'] {N m : ℕ} (hm : m ≠ 0) {l : La → Q}
    {l' : La → Q'} (hl : ∀ a c, l (a + c) = l a * l c) (hl' : ∀ a c, l' (a + c) = l' a * l' c)
    (hk : ∀ a, l a = 1 ↔ l' a = 1) (ht : ∀ a, l' a ^ N = 1) (onto : ∀ x, x ^ N = 1 ↔ ∃ a, l a = x)
    (c : Nat.card {x : Q // x ^ N = 1} = m) (c' : Nat.card {x : Q' // x ^ N = 1} = m) (y : Q') (hy : y ^ N = 1) :
    ∃ a, l' a = y := by
  let φ : Multiplicative La →* Q := MonoidHom.mk' (fun x => l x.toAdd) fun x y => hl _ _
  let φ' : Multiplicative La →* Q' := MonoidHom.mk' (fun x => l' x.toAdd) fun x y => hl' _ _
  have e : φ.ker = φ'.ker := Subgroup.ext fun a => hk _
  have r : (φ.range : Set Q) = {x | x ^ N = 1} := Set.ext fun x => (onto x).symm
  have e₁ : Nat.card φ'.range = m := by
    rw [← Subgroup.index_ker, ← e, Subgroup.index_ker, ← c]
    exact congrArg (fun s : Set Q => Nat.card s) r
  have fin : ({x | x ^ N = 1} : Set Q').Finite := Nat.finite_of_card_ne_zero (c'.trans_ne hm)
  have r' : (φ'.range : Set Q') = {x | x ^ N = 1} :=
    Set.eq_of_subset_of_ncard_le (by rintro _ ⟨a, rfl⟩; exact ht _) (c'.trans e₁.symm).le fin
  exact r'.ge hy

theorem exists_eq_smul_of_dvd {g N : ℕ} {a : Fin g ⊕ Fin g → ℤ} (h : ∀ b, (N : ℤ) ∣ omegaStd a b) :
    ∃ b, a = N • b := by
  have d : ∀ i, (N : ℤ) ∣ a i := by
    rintro (i | i)
    · simpa [omegaStd, Pi.single_apply] using h (Pi.single (.inr i) 1)
    · simpa [omegaStd, Pi.single_apply] using h (Pi.single (.inl i) 1)
  choose b hb using d
  exact ⟨b, funext fun i => by simpa using hb i⟩

theorem isPrimitiveRoot_zeta {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (zeta N) N := Complex.isPrimitiveRoot_exp N hN

theorem isPrimitiveRoot_map {p N : ℕ} {k : Type} [Field k] (hk : (N : k) ≠ 0) (β : ZP p N →+* k) :
    IsPrimitiveRoot (β (zetaZP p N)) N := by
  have hN : N ≠ 0 := by rintro rfl; exact hk Nat.cast_zero
  have : NeZero (N : k) := ⟨hk⟩
  have e : (Polynomial.cyclotomic N (ZP p N)).eval (zetaZP p N) = 0 := by
    apply (ZP p N).subtype_injective
    rw [← Polynomial.eval_map_apply, Polynomial.map_cyclotomic, map_zero]
    exact (isPrimitiveRoot_zeta hN).isRoot_cyclotomic (Nat.pos_of_ne_zero hN)
  rw [← Polynomial.isRoot_cyclotomic_iff, Polynomial.IsRoot.def, ← Polynomial.map_cyclotomic N β,
    Polynomial.eval_map_apply, e, map_zero]

theorem rt_sq {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (n N : ℕ) :
    RZ.rt H n N ^ 2 = -(H.d : RZ H n N) := by
  apply Subtype.ext
  have e : ((RZ.rt H n N : RZ H n N) : ℂ) = H.rt0 := by
    change 2 * ((1 + H.rt0) / 2) - 1 = H.rt0
    ring
  simp [e, H.sqrt_neg_disc_sq]

end Algebra

theorem isGrpPullback_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let j : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have e₁ : x₀ = j ≫ x := Over.OverMorphism.ext (by simp [hx, j])
  have e₂ : y₀ = j ≫ y := Over.OverMorphism.ext (by simp [hy, j])
  rw [e₁, e₂, ← MonObj.comp_mul]
  simp [j]

end GlobalTheory.FullSiegel

namespace GlobalTheory

open CechPic FullSiegel

theorem exists_siegPre_of_fullObj : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N p : ℕ) (O : Type) [CommRing O] (b : RZ H n N →+* O) (z : ZP p N →+* O) (T : Scheme.{0}) (sT : T ⟶ Sp O) (t : SAB H T) (lev : D.La → (𝟙_ (Over T) ⟶ t.G)) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La), Odd N → IsUnit (N : O) → z (zetaZP p N) = b (RZ.ze H n N) → IsLocallyNoetherian T → (∀ x : T, ∃ ξ : T, ξ ⤳ x ∧ CharZero (T.residueField ξ)) → (∀ x y, D.EF (bas x) (bas y) = omegaStd x y) → FullObj D (sT ≫ spMap b) t lev → ∃ (o : SiegPre g N (zetaZP p N) (sT ≫ spMap z)) (φ : o.A.left ⟶ t.G.left) (φ₂ : (G2 o.A).left ⟶ (G2 t.G).left), o.Principal ∧ IsGrpPullback o.A t.G (𝟙 T) φ ∧ IsSquare φ φ₂ ∧ LBIso o.P ((abelian₂ t.G t.PP.L).pull φ₂) ∧ ∀ u, (o.lev u).left ≫ φ = (lev (bas u)).left := by
  intro hL _ E _ _ _ H D n N p O _ b z T sT t lev g bas hodd hNO hz _ hgen hbas F
  have hN : N ≠ 0 := hodd.pos.ne'
  have hA : IsAbelianScheme t.G := ⟨t.semi.comm, t.semi.smooth, F.proper, t.semi.geomConnected⟩
  have hLB := t.PP.isLB
  have pt : ∀ {k : Type} [Field k] (x : Sp k ⟶ T), ∃ w : O →+* k, x ≫ sT = spMap w := fun x =>
    ⟨(Spec.preimage (x ≫ sT)).hom, (Spec.map_preimage (x ≫ sT)).symm⟩
  have geo := fun (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ T) (w : O →+* k)
    (hw : x ≫ sT = spMap w) => F.geom k x (w.comp b) (by rw [spMap_comp, reassoc_of% hw])
  have hd : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) t.G.hom := by
    have := hA.smooth
    have := hA.geomConnected
    refine smoothOfRelativeDimension_of_charZero _ _ hgen fun k _ _ _ x m hm => ?_
    obtain ⟨w, hw⟩ := pt x
    exact ObjDim.dim_eq_of_detCond D t.act x (by rw [← map_pow, rt_sq, map_neg, map_natCast]) (geo k x w hw).1 hm
  let P : Out.PolAV T :=
    { A := t.G, isAb := hA, g := _, smoothDim := hd, L := t.PP.L, isLB := hLB, rigid := ObjDim.rigidified,
      sym := ObjDim.sym, ample := F.ample, ktriv := F.ktriv }
  let Φ : Multiplicative D.La →* (𝟙_ (Over T) ⟶ t.G) := MonoidHom.mk' (fun a => lev a.toAdd) fun a c => F.add _ _
  have tors : ∀ a, lev a ^ N = 1 := fun a => (map_pow Φ (Multiplicative.ofAdd a) N).symm.trans (F.ker a)

  have ζN : zetaZP p N ^ N = 1 := Subtype.ext (isPrimitiveRoot_zeta hN).pow_eq_one
  let u : Oˣ := Units.ofPowEqOne (z (zetaZP p N)) N (by rw [← map_pow, ζN, map_one]) hN
  have uN : u ^ N = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val]
    change z (zetaZP p N) ^ N = 1
    rw [← map_pow, ζN, map_one])
  have hNT : IsUnit (N : Γ(T, ⊤)) := by
    have := (hNO.map (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom).map sT.appTop.hom
    rwa [map_natCast, map_natCast] at this

  have weil : ∀ (k : Type) [Field k] (x : Sp k ⟶ T) (w : O →+* k), x ≫ sT = spMap w → ∀ a c,
      Out.WeilIs t.G t.PP.L N (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev c)
        (unitOn (Units.map w.toMonoidHom u ^ D.EF a c)) := by
    intro k _ x w hw a c
    obtain ⟨U, hU, H'⟩ := PairingLocus.exists_clopen_of_isLocallyNoetherian hL T P N (𝟙_ _) (lev a) (lev c)
      (Units.map sT.appTop.hom.toMonoidHom (unitOn (u ^ D.EF a c))) hNT (tors a) (tors c) (by
        rw [← map_pow, unitOn, ← map_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, uN,
          one_zpow, map_one, map_one])
    have all : ∀ y, y ∈ U := fun y => by
      obtain ⟨ξ, hξ, h0⟩ := hgen y
      obtain ⟨k', _, _, _, x', hx'⟩ := exists_geomPt ξ h0
      obtain ⟨w', hw'⟩ := pt x'
      obtain ⟨-, I, hζ, hev⟩ := geo k' x' w' hw'
      have e : I.ζ N = Units.map w'.toMonoidHom u := Units.ext (hζ.trans (congrArg w' hz.symm))
      have i := I.isom N (Nat.pos_of_ne_zero hN) a c
      rw [← hev, ← hev, e, ← map_zpow, ← unitOn_pull sT x' w' hw'] at i
      exact hξ.mem_closed hU ((H' _ (toUnit (Over.mk x'))).1 i ⟨(default : PrimeSpectrum k'), hx' _⟩)
    rw [← map_zpow, ← unitOn_pull sT x w hw]
    exact (H' _ (toUnit (Over.mk x))).2 fun y _ => all y
  have hΔ := cls_diag hL.mulPull P
  have hΔ' := pull_isLB (isLB_lam hLB) (lift (𝟙 t.G) (𝟙 t.G)).left

  have ker : ∀ (k : Type) [Field k] (x : Sp k ⟶ T) (a : Fin g ⊕ Fin g → ℤ),
      toUnit (Over.mk x) ≫ lev (bas a) = 1 ↔ ∃ c, a = N • c := by
    intro k _ x a
    refine ⟨fun h => exists_eq_smul_of_dvd fun c => ?_, ?_⟩
    · obtain ⟨w, hw⟩ := pt x
      have i := weil k x w hw (bas a) (bas c)
      rw [h, hbas] at i
      have i₂ := (hL.weil T P N (Over.mk x)).2.1 _ _ _ _ _ i i
      rw [_root_.mul_one] at i₂
      have e := unitOn_injective ((mul_eq_left.1
        (CommutatorPairing.weilIs_unique hL.globalFns hA hLB i₂ i)).trans (map_one _).symm)
      have hk : (N : k) ≠ 0 := by simpa using (hNO.map w).ne_zero
      have pr : IsPrimitiveRoot (Units.map w.toMonoidHom u) N :=
        IsPrimitiveRoot.coe_units_iff.1 (isPrimitiveRoot_map hk (w.comp z))
      exact (pr.zpow_eq_one_iff_dvd _).1 e
    · rintro ⟨c, rfl⟩
      rw [map_nsmul, F.ker, MonObj.comp_one]
  refine ⟨{ A := t.G, ab := hA, P := abelian₂ t.G t.PP.L, isLB := isLB_lam hLB
            rig₁ := (cls_eq_zero_iff (pull_isLB (isLB_lam hLB) _)).1 ((cls_lam_pull hLB _ _).trans (lam_one_left _ _))
            rig₂ := (cls_eq_zero_iff (pull_isLB (isLB_lam hLB) _)).1 ((cls_lam_pull hLB _ _).trans (lam_one_right _ _))
            symm := lam_symm hLB
            lev := fun a => lev (bas a)
            lev_add := fun a c => by rw [map_add, F.add]
            lev_tors := fun a => tors _
            geom := ?_ }, 𝟙 _, 𝟙 _, ⟨?_, eq_one_of_lam_triv hLB P.rigid F.ktriv⟩, isGrpPullback_id _,
    ⟨by simp, by simp⟩, ?_, fun a => Category.comp_id _⟩
  · intro k _ _ x β v hx hv
    obtain ⟨w, hw⟩ := pt x
    obtain rfl : β = w.comp z := by
      rw [reassoc_of% hw, ← spMap_comp] at hx
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective hx.symm)
    obtain rfl : v = Units.map w.toMonoidHom u := Units.ext hv
    refine ⟨ker k x, ?_, fun a c => ?_⟩
    · obtain ⟨ξ, -, h0⟩ := hgen (x (default : PrimeSpectrum k))
      obtain ⟨k', _, _, _, x', -⟩ := exists_geomPt ξ h0
      obtain ⟨w', hw'⟩ := pt x'
      obtain ⟨-, I, -, hev⟩ := geo k' x' w' hw'
      have card := (hL.mulN T P N hodd.pos).2.2.2.2
      refine onto_of_card (pow_ne_zero _ hN) (l := fun a => toUnit (Over.mk x') ≫ lev (bas a))
        (fun a c => by rw [map_add, F.add, MonObj.comp_mul]) (fun a c => by rw [map_add, F.add, MonObj.comp_mul])
        (fun a => (ker k' x' a).trans (ker k x a).symm)
        (fun a => by rw [← MonObj.comp_pow, tors, MonObj.comp_one]) (fun y => ?_)
        (card k' x' (Nat.cast_ne_zero.2 hN)) (card k x (by simpa using (hNO.map w).ne_zero))
      rw [I.onto N hodd.pos, bas.surjective.exists]
      simp only [hev]
    · have i := weilIs_sq hL.globalFns hA hLB hΔ' hΔ (weil k x w hw (bas a) (bas c))
      rwa [unitOn, ← map_pow, ← zpow_natCast, ← zpow_mul, mul_comm, hbas] at i
  · have R := relAmple_finite_pow_iso T t.G t.G (𝟙 _) t.PP.L 2 two_pos hA hA hLB (inferInstanceAs (IsFinite (𝟙 _)))
    have R' := relAmple_finite_pow_iso T t.G t.G (𝟙 _) (lbPow t.PP.L 2) 2 two_pos hA hA (isLB_lbPow hLB 2)
      (inferInstanceAs (IsFinite (𝟙 _)))
    exact R'.2.2.2 _ hΔ' ((cls_eq_iff (isLB_lbPow hLB 2) hΔ').1 ((cls_lbPow hLB 2 _).trans hΔ.symm))
      (R.2.1.2 F.ample)
  · exact (cls_eq_iff (isLB_lam hLB) (pull_isLB (isLB_lam hLB) _)).1 (pull_id _).symm

end GlobalTheory
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelData_pullback_of_levelMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (O : Type) [CommRing O] (T T' : Scheme.{0}) (sT : T ⟶ Sp O) (f : T' ⟶ T) (t : SAB H T) (t' : SAB H T') (ν : SABMap t' t f) (lev : D.La → (𝟙_ (Over T) ⟶ t.G)) (lev' : D.La → (𝟙_ (Over T') ⟶ t'.G)) (g p N : ℕ) (Ag : SiegelFamily g p N) (z : ZP p N →+* O) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (w : T ⟶ pullback Ag.s (spMap z)), (∀ x, (lev' x).left ≫ ν.φ = f ≫ (lev x).left) → SiegData sT t lev Ag z bas w → SiegData (f ≫ sT) t' lev' Ag z bas (f ≫ w) := by
  first | exact @GlobalTheory.SiegelDataPull.siegData_pull | exact GlobalTheory.SiegelDataPull.siegData_pull | (intros; apply GlobalTheory.SiegelDataPull.siegData_pull <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

private theorem omegaStd_single_single_eq_stdSymp {g : ℕ} (a b : Fin g ⊕ Fin g) :
    omegaStd (Pi.single a (1 : ℤ)) (Pi.single b 1) =
      Out.stdSymp g (finCongr (two_mul g).symm (finSumFinEquiv a))
        (finCongr (two_mul g).symm (finSumFinEquiv b)) := by
  unfold Out.stdSymp omegaStd
  rcases a with i | i <;> rcases b with j | j <;>
    simp only [Pi.single_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, mul_zero, zero_mul,
      sub_zero, zero_sub, mul_ite, ite_mul, mul_one, one_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.sum_const_zero, Finset.sum_neg_distrib] <;>
    simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finCongr_apply, Fin.coe_cast,
      Fin.coe_castAdd, Fin.coe_natAdd, Fin.ext_iff] <;>
    split_ifs <;> omega

theorem exists_equiv_omegaStd {M : Type} [AddCommGroup M] (B : LinearMap.BilinForm ℤ M) {g : ℕ}
    (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] M)
    (h : ∀ i j, B (bas (Pi.single i 1)) (bas (Pi.single j 1)) = Out.stdSymp g i j) :
    ∃ bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] M, ∀ x y, B (bas' x) (bas' y) = omegaStd x y := by
  set e : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm) with he
  refine ⟨(LinearEquiv.funCongrLeft ℤ ℤ e.symm).trans bas, ?_⟩
  have hs : ∀ a, (LinearEquiv.funCongrLeft ℤ ℤ e.symm) (Pi.single a (1 : ℤ)) = Pi.single (e a) 1 := by
    intro a
    funext k
    simp [LinearEquiv.funCongrLeft_apply, Pi.single_apply, Equiv.symm_apply_eq]
  let Ω : LinearMap.BilinForm ℤ (Fin g ⊕ Fin g → ℤ) :=
    LinearMap.mk₂ ℤ omegaStd
      (fun a a' b => by simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; ext; ring)
      (fun c a b => by simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; ext; ring)
      (fun a b b' => by simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; ext; ring)
      (fun c a b => by simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; ext; ring)
  have hB : B.compl₁₂ ((LinearEquiv.funCongrLeft ℤ ℤ e.symm).trans bas).toLinearMap
      ((LinearEquiv.funCongrLeft ℤ ℤ e.symm).trans bas).toLinearMap = Ω := by
    refine LinearMap.ext_basis (Pi.basisFun ℤ _) (Pi.basisFun ℤ _) fun a b => ?_
    simp only [Pi.basisFun_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, hs, h,
      Ω, LinearMap.mk₂_apply]
    exact (omegaStd_single_single_eq_stdSymp a b).symm
  intro x y
  exact LinearMap.congr_fun₂ hB x y

theorem sympBasis_std : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), IsSympBasis D bas → g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La, ∀ x y, D.EF (bas' x) (bas' y) = omegaStd x y := by
  intro E _ _ _ H D g bas hb
  refine ⟨?_, exists_equiv_omegaStd D.EF bas hb⟩
  have h1 := (LinearEquiv.finrank_eq bas).symm
  rw [finrank_int_lattice D, Module.finrank_fin_fun] at h1
  omega

end GlobalTheory.ZM
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.JoinRing

def coprimeNat (p : ℕ) (A : Type) [CommRing A] : Submonoid A where
  carrier := {x | ∃ m : ℕ, m.Coprime p ∧ x = m}
  one_mem' := ⟨1, by simp, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, Nat.Coprime.mul_left ha hb, by simp⟩

theorem ne_zero_of_coprime {p m : ℕ} (hp : p.Prime) (hm : m.Coprime p) : m ≠ 0 := by
  rintro rfl
  exact hp.ne_one (by simpa using hm)

theorem coprimeNat_le {p : ℕ} (hp : p.Prime) (A : Type) [CommRing A] [IsDomain A] [CharZero A] :
    coprimeNat p A ≤ nonZeroDivisors A := by
  rintro _ ⟨m, hm, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr (ne_zero_of_coprime hp hm))

theorem isLocalization_of_le_closure {p : ℕ} (hp : p.Prime) (A : Type) [CommRing A] (T : Subring ℂ) [Algebra A T]
    (hinj : Function.Injective (algebraMap A T)) (hinv : ∀ m : ℕ, m.Coprime p → (m : ℂ)⁻¹ ∈ T)
    (hT : T ≤ Subring.closure ({x | ∃ a, x = (algebraMap A T a : ℂ)} ∪ {x | ∃ n : ℕ, n.Coprime p ∧ x = (n : ℂ)⁻¹})) :
    IsLocalization (coprimeNat p A) T := by
  have h0 : ∀ m : ℕ, m.Coprime p → (m : ℂ) ≠ 0 := fun m hm => Nat.cast_ne_zero.mpr (ne_zero_of_coprime hp hm)
  have key : ∀ z ∈ Subring.closure ({x | ∃ a, x = (algebraMap A T a : ℂ)} ∪ {x | ∃ n : ℕ, n.Coprime p ∧ x = (n : ℂ)⁻¹}),
      ∃ m : ℕ, m.Coprime p ∧ ∃ a, z * m = (algebraMap A T a : ℂ) := by
    intro z hz
    induction hz using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | ⟨m, hm, rfl⟩
      · exact ⟨1, by simp, a, by simp⟩
      · exact ⟨m, hm, 1, by simp [h0 m hm]⟩
    | zero => exact ⟨1, by simp, 0, by simp⟩
    | one => exact ⟨1, by simp, 1, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨m, hm, a, ha⟩ := hx
      obtain ⟨k, hk, b, hb⟩ := hy
      refine ⟨m * k, Nat.Coprime.mul_left hm hk, a * k + b * m, ?_⟩
      simp only [map_add, map_mul, map_natCast]
      push_cast
      rw [← ha, ← hb]; ring
    | neg x _ hx =>
      obtain ⟨m, hm, a, ha⟩ := hx
      refine ⟨m, hm, -a, ?_⟩
      simp only [map_neg]
      push_cast
      rw [← ha]; ring
    | mul x y _ _ hx hy =>
      obtain ⟨m, hm, a, ha⟩ := hx
      obtain ⟨k, hk, b, hb⟩ := hy
      refine ⟨m * k, Nat.Coprime.mul_left hm hk, a * b, ?_⟩
      simp only [map_mul]
      push_cast
      rw [← ha, ← hb]; ring
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, hm, rfl⟩
    simp only [map_natCast]
    refine IsUnit.of_mul_eq_one ⟨_, hinv m hm⟩ (Subtype.ext ?_)
    simp [h0 m hm]
  · intro z
    obtain ⟨m, hm, a, ha⟩ := key z (hT z.2)
    refine ⟨(a, ⟨m, m, hm, rfl⟩), Subtype.ext ?_⟩
    simp only [map_natCast]
    push_cast
    exact ha
  · intro x y h
    exact ⟨1, by rw [hinj h]⟩

theorem inv_mem_ZP {p m : ℕ} (k : ℕ) (hm : m.Coprime p) : (m : ℂ)⁻¹ ∈ ZP p k :=
  Subring.subset_closure (Or.inr ⟨m, hm, rfl⟩)

open CycBase in

theorem isDedekindDomain_ZP {n p : ℕ} (e : ℕ) (hn : n.Prime) (hp : p.Prime) : IsDedekindDomain (ZP p (n ^ e)) := by
  haveI := Fact.mk hn
  have hk : n ^ e ≠ 0 := NeZero.ne _
  haveI : IsCyclotomicExtension {n ^ e} ℚ (CF (n ^ e)) := cyc
  haveI : NumberField (CF (n ^ e)) := IsCyclotomicExtension.numberField {n ^ e} ℚ _
  let io : 𝓞 (CF (n ^ e)) →+* ℂ := (CF (n ^ e)).val.toRingHom.comp (algebraMap _ (CF (n ^ e)))
  have hio : Function.Injective io := Subtype.val_injective.comp (RingOfIntegers.coe_injective)
  letI : Algebra (𝓞 (CF (n ^ e))) (ZP p (n ^ e)) := (io.codRestrict _ (mem_ZP p n e hn)).toAlgebra
  have : IsLocalization (coprimeNat p (𝓞 (CF (n ^ e)))) (ZP p (n ^ e)) := by
    refine isLocalization_of_le_closure hp _ _ (fun x y h => hio (congrArg (fun z : ZP p (n ^ e) => (z : ℂ)) h))
      (fun m hm => inv_mem_ZP _ hm) (Subring.closure_mono ?_)
    rintro x (rfl | h)
    · exact Or.inl ⟨(zF_prim hk).toInteger, rfl⟩
    · exact Or.inr h
  exact IsLocalization.isDedekindDomain _ (coprimeNat_le hp (𝓞 (CF (n ^ e)))) _

theorem isDedekindDomain_RZ_of_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {S A e : ℕ}
    (hS : 0 < S) (hA : 0 < A) (h : A ∣ S ^ e) : IsDedekindDomain (RZ H S A) := by
  obtain ⟨l, rfl⟩ : ∃ l : Level H, l.A = A := ⟨GlobalTheory.HostModel.level H A hA, rfl⟩
  exact GlobalTheory.BaseRing.isDedekindDomain_RZ l hS h

theorem flat_inclusion {S T : Subring ℂ} (h : S ≤ T) [IsDedekindDomain S] : Flat (spMap (Subring.inclusion h)) := by
  letI : Algebra S T := (Subring.inclusion h).toAlgebra
  have htf : Module.IsTorsionFree S T := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact fun x y h => Subtype.ext (congrArg (fun z : T => (z : ℂ)) h)
  exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat S T))

theorem noetherian_preimmersion {p : ℕ} (hp : p.Prime) {S T : Subring ℂ} (h : S ≤ T) [IsNoetherianRing S]
    (hinv : ∀ m : ℕ, m.Coprime p → (m : ℂ)⁻¹ ∈ T)
    (hT : T ≤ Subring.closure ((S : Set ℂ) ∪ {x | ∃ n : ℕ, n.Coprime p ∧ x = (n : ℂ)⁻¹})) :
    IsNoetherianRing T ∧ IsPreimmersion (spMap (Subring.inclusion h)) := by
  letI : Algebra S T := (Subring.inclusion h).toAlgebra
  have hL : IsLocalization (coprimeNat p S) T := by
    refine isLocalization_of_le_closure hp _ _ (fun x y h => Subtype.ext (congrArg (fun z : T => (z : ℂ)) h))
      hinv (hT.trans (Subring.closure_mono ?_))
    rintro x (hx | hx)
    · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
    · exact Or.inr hx
  exact ⟨IsLocalization.isNoetherianRing (coprimeNat p S) _ inferInstance,
    IsPreimmersion.of_isLocalization (R := S) (S := T) (coprimeNat p S)⟩

theorem join_rings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n N p : ℕ), n.Prime → (∃ j, 1 ≤ j ∧ N = n ^ j) → p.Prime → p ≠ n → IsDedekindDomain (RZ H n N) ∧ IsNoetherianRing ↥(RZ H n N ⊔ ZP p N) ∧ Flat (spMap (Subring.inclusion (le_sup_left : RZ H n N ≤ RZ H n N ⊔ ZP p N))) ∧ IsPreimmersion (spMap (Subring.inclusion (le_sup_left : RZ H n N ≤ RZ H n N ⊔ ZP p N))) ∧ Flat (spMap (Subring.inclusion (le_sup_right : ZP p N ≤ RZ H n N ⊔ ZP p N))) := by
  rintro E _ _ _ H n N p hn ⟨j, -, hN⟩ hp -
  have hD : IsDedekindDomain (RZ H n N) :=
    isDedekindDomain_RZ_of_dvd H (e := j) hn.pos (hN ▸ pow_pos hn.pos j) (hN ▸ dvd_rfl)
  have hZ : IsDedekindDomain (ZP p N) := hN ▸ isDedekindDomain_ZP j hn hp
  have h := noetherian_preimmersion hp (le_sup_left : RZ H n N ≤ RZ H n N ⊔ ZP p N)
    (fun m hm => (le_sup_right : ZP p N ≤ _) (inv_mem_ZP _ hm))
    (sup_le (fun x hx => Subring.subset_closure (Or.inl hx)) (Subring.closure_mono (by
      rintro x (rfl | h)
      · exact Or.inl (RZ.ze H n N).2
      · exact Or.inr h)))
  exact ⟨hD, h.1, flat_inclusion _, h.2, flat_inclusion _⟩

end GlobalTheory.JoinRing
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory

theorem lbIso_lam_pull_id_w0 {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}
    (t : SAB H S) :
    LBIso t.PP.L ((abelian₂ t.G t.PP.L).pull (Y := t.G.left) (lift (𝟙 t.G) (t.act.act H.w0)).left) := by
  have hΛ : (abelian₂ t.G t.PP.L).IsLB := LB.isLB_linComb t.PP.isLB _ _
  refine t.prim.trans t.PP.isLB (LB.isLB_linComb t.PP.isLB _ _) (pull_isLB hΛ _) ?_
  refine LBIso.chartPull (A := abelian₂ t.G t.PP.L) (B := abelian₂ t.G t.PP.L) (h := (lift (𝟙 t.G) (t.act.act H.w0)).left)
    (chartPullSame t.PP.L _ _ _ _ fun I => ?_) (Geo.Tor.chartPullPull _ _ _ rfl) (Pdiv.PullbackComparison.gen_refl _ hΛ)
  have e : psum t.G ![𝟙 t.G, t.act.act H.w0] I.down =
      lift (𝟙 t.G) (t.act.act H.w0) ≫ psum t.G (x2 t.G) I.down := by
    refine Eq.trans (congrArg (fun z => psum t.G z I.down) (funext fun i => ?_))
      (psum_hom (preHom (lift (𝟙 t.G) (t.act.act H.w0))) (x2 t.G) I.down).symm
    fin_cases i
    · exact (lift_fst _ _).symm
    · exact (lift_snd _ _).symm
  exact congrArg (fun z => z.left) e

theorem exists_sabMap_of_isProper_of_lbIso_lam : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (φ : t'.G.left ⟶ t.G.left) (φ₂ : (G2 t'.G).left ⟶ (G2 t.G).left), IsProper t.G.hom → IsGrpPullback t'.G t.G f φ → IsSquare φ φ₂ → LBIso (abelian₂ t'.G t'.PP.L) ((abelian₂ t.G t.PP.L).pull φ₂) → (∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left) → ∃ m : SABMap t' t f, m.φ = φ := by
  intro hL E _ _ _ H S S' t t' f φ φ₂ hp gp sq hΛ hact
  refine exists_sabMap_of_isProper_of_lbIso hL.globalFns E H S S' t t' f φ hp gp ?_ hact
  have l : (abelian₂ t.G t.PP.L).IsLB := LB.isLB_linComb t.PP.isLB _ _
  have l' : (abelian₂ t'.G t'.PP.L).IsLB := LB.isLB_linComb t'.PP.isLB _ _
  let δ : t.G.left ⟶ (G2 t.G).left := (lift (𝟙 t.G) (t.act.act H.w0)).left
  let δ' : t'.G.left ⟶ (G2 t'.G).left := (lift (𝟙 t'.G) (t'.act.act H.w0)).left
  have a₁ : δ ≫ (fst t.G t.G).left = 𝟙 _ := congrArg (fun z => z.left) (lift_fst (𝟙 t.G) (t.act.act H.w0))
  have a₂ : δ ≫ (snd t.G t.G).left = (t.act.act H.w0).left :=
    congrArg (fun z => z.left) (lift_snd (𝟙 t.G) (t.act.act H.w0))
  have b₁ : δ' ≫ (fst t'.G t'.G).left = 𝟙 _ := congrArg (fun z => z.left) (lift_fst (𝟙 t'.G) (t'.act.act H.w0))
  have b₂ : δ' ≫ (snd t'.G t'.G).left = (t'.act.act H.w0).left :=
    congrArg (fun z => z.left) (lift_snd (𝟙 t'.G) (t'.act.act H.w0))
  have e : δ' ≫ φ₂ = φ ≫ δ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst t.G t.G).left = (_ ≫ _) ≫ (fst t.G t.G).left
      rw [Category.assoc, sq.1, ← Category.assoc, b₁, Category.assoc, a₁, Category.id_comp, Category.comp_id]
    · show (_ ≫ _) ≫ (snd t.G t.G).left = (_ ≫ _) ≫ (snd t.G t.G).left
      rw [Category.assoc, sq.2, ← Category.assoc, b₂, Category.assoc, a₂, hact]
  have s₁ : LBIso t'.PP.L (((abelian₂ t.G t.PP.L).pull φ₂).pull δ') :=
    (lbIso_lam_pull_id_w0 t').trans t'.PP.isLB (pull_isLB l' _) (pull_isLB (pull_isLB l _) _)
      (SiegelPullComp.iso_pull δ' hΛ)
  have s₂ : LBIso t'.PP.L ((abelian₂ t.G t.PP.L).pull (δ' ≫ φ₂)) :=
    s₁.trans t'.PP.isLB (pull_isLB (pull_isLB l _) _) (pull_isLB l _) (SiegelPullComp.iso_pull_pull l φ₂ δ')
  rw [e] at s₂
  have s₃ : LBIso t'.PP.L (((abelian₂ t.G t.PP.L).pull δ).pull φ) :=
    s₂.trans t'.PP.isLB (pull_isLB l _) (pull_isLB (pull_isLB l _) _) (SiegelPullComp.iso_pull_pull l δ φ).symm
  exact s₃.trans t'.PP.isLB (pull_isLB (pull_isLB l _) _) (pull_isLB t.PP.isLB _)
    (SiegelPullComp.iso_pull φ (lbIso_lam_pull_id_w0 t)).symm

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SiegelDirect

open GlobalTheory.SiegelPullComp

private theorem tensor_left_hom_ext' {T : Scheme.{0}} {G : Over T} {X : Scheme.{0}} (a b : X ⟶ (G ⊗ G).left)
    (h1 : a ≫ (fst G G).left = b ≫ (fst G G).left) (h2 : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b := by
  have hw : b ≫ (G ⊗ G).hom = a ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), reassoc_of% h1]
  have key := CartesianMonoidalCategory.hom_ext
    (Over.homMk a rfl : Over.mk (a ≫ (G ⊗ G).hom) ⟶ G ⊗ G) (Over.homMk b hw)
    (by ext; simpa using h1) (by ext; simpa using h2)
  simpa using congrArg (fun k => k.left) key

theorem exists_inverse {T : Scheme.{0}} {A G : Over T} [GrpObj A] [GrpObj G] {φ : A.left ⟶ G.left}
    {φ₂ : (G2 A).left ⟶ (G2 G).left} (hφ : IsGrpPullback A G (𝟙 T) φ) (hs : Geo.Tor.IsSquare φ φ₂) :
    ∃ (F : G.left ⟶ A.left) (F₂ : (G2 G).left ⟶ (G2 A).left), IsGrpPullback G A (𝟙 T) F ∧ Geo.Tor.IsSquare F F₂ ∧
      φ ≫ F = 𝟙 _ ∧ F₂ ≫ φ₂ = 𝟙 _ := by
  have hw : φ ≫ G.hom = A.hom := by simpa using hφ.1.w
  have : IsIso φ := hφ.1.isIso_fst_of_isIso
  let e : A ≅ G := Over.isoMk (asIso φ) hw
  have heL : e.inv.left = inv φ := rfl
  have hsF : Geo.Tor.IsSquare (inv φ) (e.inv ⊗ₘ e.inv).left := by
    constructor
    · rw [← Over.comp_left, tensorHom_fst, Over.comp_left, heL]
    · rw [← Over.comp_left, tensorHom_snd, Over.comp_left, heL]
  refine ⟨inv φ, (e.inv ⊗ₘ e.inv).left, ⟨?_, ?_⟩, hsF, by simp, ?_⟩
  · refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [← hw]
    simp
  · intro U x y x₀ y₀ hx hy
    have key := hφ.2 (Over.mk (U.hom ≫ 𝟙 T)) x₀ y₀ (Over.homMk x.left (by simp))
      (Over.homMk y.left (by simp)) (by simp [hx]) (by simp [hy])
    have hxy := mul_left_congr (a := (U.hom ≫ 𝟙 T) ≫ 𝟙 T) (b := U.hom) (by simp)
      (Over.homMk x.left (by simp)) (Over.homMk y.left (by simp)) x y (by simp) (by simp)
    rw [hxy.symm.trans key]
    simp
  · apply tensor_left_hom_ext'
    · rw [Category.assoc, hs.1, ← Category.assoc, hsF.1]
      simp
    · rw [Category.assoc, hs.2, ← Category.assoc, hsF.2]
      simp

theorem direct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (O : Type) [CommRing O] (T : Scheme.{0}) (sT : T ⟶ Sp O) (t : SAB H T) (lev : D.La → (𝟙_ (Over T) ⟶ t.G)) (g p N : ℕ) (Ag : SiegelFamily g p N) (z : ZP p N →+* O) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (w : T ⟶ pullback Ag.s (spMap z)), SiegData sT t lev Ag z bas w → ∃ (θ : t.G.left ⟶ Ag.univ.A.left) (θ₂ : (G2 t.G).left ⟶ (G2 Ag.univ.A).left), IsGrpPullback t.G Ag.univ.A (w ≫ pullback.fst _ _) θ ∧ IsSquare θ θ₂ ∧ LBIso (abelian₂ t.G t.PP.L) (Ag.univ.P.pull θ₂) ∧ ∀ u, (lev (bas u)).left ≫ θ = (w ≫ pullback.fst _ _) ≫ (Ag.univ.lev u).left := by
  intro E _ _ _ H D O _ T sT t lev g p N Ag z bas w hd
  obtain ⟨o, φ, φ₂, hφ, hs, hL, hlev, hcl, ψ, ψ₂, hψ, hs', hP, hlev'⟩ := hd
  obtain ⟨F, F₂, hF, hsF, hφF, hF₂⟩ := exists_inverse hφ hs
  have h0 : t.PP.L.IsLB := t.PP.isLB
  have hΛ : (abelian₂ t.G t.PP.L).IsLB := by
    unfold abelian₂
    exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ h0 _ _
  refine ⟨F ≫ ψ, F₂ ≫ ψ₂, (hF.comp hψ).congr (Category.id_comp _) rfl, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, hs'.1, ← Category.assoc, hsF.1, Category.assoc]
  · rw [Category.assoc, hs'.2, ← Category.assoc, hsF.2, Category.assoc]
  · have hΛ₁ := pull_isLB hΛ (𝟙 (G2 t.G).left)
    have hΛ₂ := pull_isLB (pull_isLB hΛ φ₂) F₂
    have hO := pull_isLB o.isLB F₂
    have hU₁ := pull_isLB (pull_isLB Ag.univ.isLB ψ₂) F₂
    have hU₂ := pull_isLB Ag.univ.isLB (F₂ ≫ ψ₂)
    have s1 : LBIso (abelian₂ t.G t.PP.L) ((abelian₂ t.G t.PP.L).pull (𝟙 _)) := iso_pull_id hΛ
    have s2 : LBIso ((abelian₂ t.G t.PP.L).pull (𝟙 _)) (((abelian₂ t.G t.PP.L).pull φ₂).pull F₂) := by
      have k := iso_pull_pull hΛ φ₂ F₂
      rw [hF₂] at k
      exact k.symm
    have s3 : LBIso (((abelian₂ t.G t.PP.L).pull φ₂).pull F₂) (o.P.pull F₂) := (iso_pull F₂ hL).symm
    have s4 : LBIso (o.P.pull F₂) ((Ag.univ.P.pull ψ₂).pull F₂) := iso_pull F₂ hP
    have s5 : LBIso ((Ag.univ.P.pull ψ₂).pull F₂) (Ag.univ.P.pull (F₂ ≫ ψ₂)) := iso_pull_pull Ag.univ.isLB ψ₂ F₂
    exact LBIso.trans hΛ hΛ₁ hU₂ s1 (LBIso.trans hΛ₁ hΛ₂ hU₂ s2
      (LBIso.trans hΛ₂ hO hU₂ s3 (LBIso.trans hO hU₁ hU₂ s4 s5)))
  · intro u
    rw [← hlev u]
    simp only [Category.assoc, reassoc_of% hφF]
    exact hlev' u

end GlobalTheory.SiegelDirect

end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.EpsAct

theorem subsingleton_sp_dualNumber (k : Type) [Field k] : Subsingleton (Sp (DualNumber k)) := by
  change Subsingleton (PrimeSpectrum (DualNumber k))
  have key : ∀ (p : PrimeSpectrum (DualNumber k)) (x : DualNumber k), x ∈ p.asIdeal ↔ x.fst = 0 := by
    intro p x
    constructor
    · intro hx
      by_contra h
      exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
        (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 h)))
    · intro h
      apply p.isPrime.mem_of_pow_mem 2
      have hx : x = TrivSqZeroExt.inr x.snd := TrivSqZeroExt.ext (by simp [h]) (by simp)
      rw [hx, pow_two]
      simp
  exact ⟨fun p q => PrimeSpectrum.ext (Ideal.ext fun x => (key p x).trans (key q x).symm)⟩

theorem rigidity (hL : Out.Laws) (k : Type) [Field k] {Z : Scheme.{0}} (c₀ : Z ⟶ Sp k)
    (A' G' : Over (Sp (DualNumber k))) [GrpObj A'] [GrpObj G'] (j : Z ⟶ A'.left) (a b : A' ⟶ G')
    (hA : IsAbelianScheme A')
    (hj : IsPullback j c₀ A'.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom))
    (hab : j ≫ a.left = j ≫ b.left) (hη : η[A'] ≫ a = η[A'] ≫ b) : a = b := by
  classical
  have hsurj : Function.Surjective A'.hom.appTop.hom := (hL.globalFns _ A' hA).2
  set d : A' ⟶ G' := a * b⁻¹ with hd
  have hsub : Subsingleton (Sp (DualNumber k)) := subsingleton_sp_dualNumber k
  have hjs : Function.Surjective j.base := by
    have hs0 : Surjective (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) := by
      constructor
      intro y
      obtain ⟨q⟩ : Nonempty (Sp k) := by
        change Nonempty (PrimeSpectrum k)
        infer_instance
      exact ⟨q, Subsingleton.elim _ _⟩
    exact (MorphismProperty.of_isPullback (P := @Surjective) hj.flip hs0).surj
  have key : ∀ {W : Over (Sp (DualNumber k))} (u : W ⟶ A'), u ≫ a = u ≫ b → u ≫ d = 1 := by
    intro W u h
    rw [MonObj.comp_mul, GrpObj.comp_inv, h, mul_inv_cancel]
  have hjd : j ≫ d.left = (toUnit (Over.mk (j ≫ A'.hom))).left ≫ η[G'].left := by
    have h1 := congrArg (fun f => Over.Hom.left f)
      (key (Over.homMk j rfl : Over.mk (j ≫ A'.hom) ⟶ A') (by ext; exact hab))
    simpa [Hom.one_def] using h1
  obtain ⟨pt⟩ : Nonempty ((𝟙_ (Over (Sp (DualNumber k)))).left) := by
    obtain ⟨q⟩ : Nonempty (Sp k) := by
      change Nonempty (PrimeSpectrum k)
      infer_instance
    exact ⟨(spMap (TrivSqZeroExt.fstHom k k k).toRingHom).base q⟩
  have hsub1 : Subsingleton ((𝟙_ (Over (Sp (DualNumber k)))).left) := hsub
  have hy : ∀ x, d.left x = η[G'].left pt := by
    intro x
    obtain ⟨z, rfl⟩ := hjs x
    have h2 := congrArg (fun f : Z ⟶ G'.left => f z) hjd
    simp only [Scheme.Hom.comp_apply] at h2
    rw [h2]
    exact congrArg _ (Subsingleton.elim _ _)
  have hfac := GlobalTheory.DualRigidity.eq_comp_section_of_const A'.hom η[A'].left d.left
    (by simp) hsurj _ hy
  have hη' : η[A'] ≫ d = 1 := key _ hη
  have hd2 : d = toUnit A' ≫ η[A'] ≫ d := by
    ext
    exact hfac
  have hd1 : d = 1 := by
    rw [hd2, hη']
    simp
  exact mul_inv_eq_one.1 hd1

theorem main : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] (T : Scheme.{0}) (t : SAB H T) (x : Sp (DualNumber k) ⟶ T) (t' : SAB H (Sp (DualNumber k))) (ν : SABMap t' t x) (φ : t'.G.left ⟶ t.G.left), IsProper t.G.hom → IsGrpPullback t'.G t.G (constPt x) φ → (∀ (Z : Scheme.{0}) (j : Z ⟶ t'.G.left) (c : Z ⟶ Sp k), j ≫ t'.G.hom = c ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → j ≫ φ = j ≫ ν.φ) → ∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left := by
  intro hL E _ _ _ H k _ T t x t' ν φ hP hpb hag a
  have hsq := hpb.1
  have hprop : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) hsq hP
  have hs := t'.semi
  have hA : IsAbelianScheme t'.G :=
    { comm := hs.comm, smooth := hs.smooth, proper := hprop, geomConnected := hs.geomConnected }
  have hα : ((t'.act.act a).left ≫ φ) ≫ t.G.hom = t'.G.hom ≫ constPt x := by
    rw [Category.assoc, hsq.w, ← Category.assoc, Over.w]
  have hβ : (φ ≫ (t.act.act a).left) ≫ t.G.hom = t'.G.hom ≫ constPt x := by
    rw [Category.assoc, Over.w, hsq.w]
  let A : t'.G ⟶ t'.G := Over.homMk (hsq.lift _ _ hα) (hsq.lift_snd _ _ _)
  let B : t'.G ⟶ t'.G := Over.homMk (hsq.lift _ _ hβ) (hsq.lift_snd _ _ _)
  have e3 : (t'.act.act a).left ≫ ν.φ = ν.φ ≫ (t.act.act a).left := ν.act a
  have hj := IsPullback.of_hasPullback t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)
  have hab : pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ A.left = pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ B.left := by
    apply hsq.hom_ext
    · simp only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_fst]
      have e1 := hag _ (pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (pullback.snd t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) hj.w
      have e2 := hag _ (pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ (t'.act.act a).left) (pullback.snd t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom))
        (by rw [Category.assoc, Over.w]; exact hj.w)
      rw [← Category.assoc, e2, Category.assoc, e3, ← Category.assoc, ← e1, Category.assoc]
    · simp only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_snd]
  let e : Over.mk ((𝟙_ (Over (Sp (DualNumber k)))).hom ≫ constPt x) ⟶ t.G :=
    Over.homMk (η[t'.G].left ≫ φ) (by rw [Category.assoc, hsq.w, ← Category.assoc, Over.w]; rfl)
  have hη1 : (η[t'.G] : 𝟙_ _ ⟶ t'.G) = 1 := by simp [Hom.one_def]
  have he1 : e = 1 := by
    have hm := hpb.2 _ η[t'.G] η[t'.G] e e rfl rfl
    rw [hη1, _root_.mul_one] at hm
    have hee : e * e = e := by
      ext
      rw [hm, ← hη1]
      rfl
    exact _root_.mul_eq_left.1 hee
  have he2 : e ≫ t.act.act a = e := by
    have := t.act.hom a
    rw [he1, Hom.one_def, Category.assoc, IsMonHom.one_hom]
  have he3 := congrArg Over.Hom.left he2
  have hm1 : η[t'.G] ≫ t'.act.act a = η[t'.G] := by
    have := t'.act.hom a
    exact IsMonHom.one_hom _
  have hm2 := congrArg Over.Hom.left hm1
  have hη : η[t'.G] ≫ A = η[t'.G] ≫ B := by
    ext
    simp only [Over.comp_left]
    apply hsq.hom_ext
    · simp only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_fst]
      simp only [e, Over.comp_left, Over.homMk_left, Category.assoc] at he3 hm2
      rw [← Category.assoc, hm2, he3]
    · simp only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_snd]
  have hAB := rigidity hL k (pullback.snd t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) t'.G t'.G (pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) A B hA hj hab hη
  have hL' := congrArg Over.Hom.left hAB
  simp only [A, B, Over.homMk_left] at hL'
  calc (t'.act.act a).left ≫ φ = hsq.lift _ _ hα ≫ φ := (hsq.lift_fst _ _ _).symm
    _ = hsq.lift _ _ hβ ≫ φ := by rw [hL']
    _ = φ ≫ (t.act.act a).left := hsq.lift_fst _ _ _

end GlobalTheory.EpsAct
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.FamSiegel

theorem exists_sabMap_constPt : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] (T Y : Scheme.{0}) (t : SAB H T) (A : Over Y) (_ : GrpObj A) (P : LB (G2 A).left) (y : T ⟶ Y) (θ : t.G.left ⟶ A.left) (θ₂ : (G2 t.G).left ⟶ (G2 A).left) (x : Sp (DualNumber k) ⟶ T) (t' : SAB H (Sp (DualNumber k))) (ν : SABMap t' t x), IsProper t.G.hom → P.IsLB → IsGrpPullback t.G A y θ → IsSquare θ θ₂ → LBIso (abelian₂ t.G t.PP.L) (P.pull θ₂) → x ≫ y = constPt x ≫ y → ∃ ν' : SABMap t' t (constPt x), ν'.φ ≫ θ = ν.φ ≫ θ := by
  intro hL E _ _ _ H k _ T Y t A _ P y θ θ₂ x t' ν hp hP hθ hsq hiso hx
  obtain ⟨φ, hφ₁, hφ₂⟩ : ∃ φ : t'.G.left ⟶ t.G.left, φ ≫ θ = ν.φ ≫ θ ∧ φ ≫ t.G.hom = t'.G.hom ≫ constPt x :=
    ⟨hθ.1.lift (ν.φ ≫ θ) (t'.G.hom ≫ constPt x) (by
      rw [Category.assoc, hθ.1.w, ← Category.assoc, ν.cart.1.w, Category.assoc, hx, Category.assoc]),
      hθ.1.lift_fst _ _ _, hθ.1.lift_snd _ _ _⟩
  have hφ : IsGrpPullback t'.G t.G (constPt x) φ :=
    hθ.cancel (by rw [hφ₁, ← hx]; exact ν.cart.comp hθ) hφ₂
  obtain ⟨φ₂, hφs⟩ := (GlobalTheory.LamPull.lam_pull E H _ _ t t' (constPt x)).1 φ hφ₂
  obtain ⟨ν₂, hνs⟩ := (GlobalTheory.LamPull.lam_pull E H _ _ t t' x).1 ν.φ ν.cart.1.w
  have hν := (GlobalTheory.LamPull.lam_pull E H _ _ t t' x).2 ν ν₂ hνs
  have e : φ₂ ≫ θ₂ = ν₂ ≫ θ₂ := by
    apply pullback.hom_ext
    · change (φ₂ ≫ θ₂) ≫ (fst A A).left = (ν₂ ≫ θ₂) ≫ (fst A A).left
      rw [Category.assoc, Category.assoc, hsq.1, ← Category.assoc, ← Category.assoc, hφs.1, hνs.1, Category.assoc,
        Category.assoc, hφ₁]
    · change (φ₂ ≫ θ₂) ≫ (snd A A).left = (ν₂ ≫ θ₂) ≫ (snd A A).left
      rw [Category.assoc, Category.assoc, hsq.2, ← Category.assoc, ← Category.assoc, hφs.2, hνs.2, Category.assoc,
        Category.assoc, hφ₁]
  have l : (abelian₂ t.G t.PP.L).IsLB := LB.isLB_linComb t.PP.isLB _ _
  have l' : (abelian₂ t'.G t'.PP.L).IsLB := LB.isLB_linComb t'.PP.isLB _ _
  have key : ∀ a : (G2 t'.G).left ⟶ (G2 t.G).left, LBIso ((abelian₂ t.G t.PP.L).pull a) (P.pull (a ≫ θ₂)) := fun a =>
    (SiegelPullComp.iso_pull a hiso).trans (pull_isLB l _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _)
      (SiegelPullComp.iso_pull_pull hP θ₂ a)
  have hlam : LBIso (abelian₂ t'.G t'.PP.L) ((abelian₂ t.G t.PP.L).pull φ₂) :=
    (hν.trans l' (pull_isLB l _) (pull_isLB hP _) (key ν₂)).trans l' (pull_isLB hP _) (pull_isLB l _)
      (e ▸ (key φ₂).symm)
  have hc : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ constPt x =
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x := by
    rw [constPt, ← Category.assoc]
    exact (congrArg (· ≫ _) (TangentCrit.dualPt_dualBase k)).trans (Category.id_comp _)
  obtain ⟨m, hm⟩ := GlobalTheory.exists_sabMap_of_isProper_of_lbIso_lam hL E H _ _ t t' (constPt x) φ φ₂ hp hφ hφs hlam
    (GlobalTheory.EpsAct.main hL E H k T t x t' ν φ hp hφ fun Z j c hj => hθ.1.hom_ext
      (by rw [Category.assoc, Category.assoc, hφ₁])
      (by rw [Category.assoc, Category.assoc, hφ₂, ν.cart.1.w, ← Category.assoc, ← Category.assoc, hj, Category.assoc,
        Category.assoc, hc]))
  exact ⟨m, by rw [hm, hφ₁]⟩

theorem exists_extension : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) (g : ℕ) (B : Type) [CommRing B] (ζ : B) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (c : SiegPre g N ζ sY) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (sV : Sp V ⟶ Sp (RZ H n N)) (y : Sp V ⟶ Y) (x : Sp K ⟶ MM) (tK : SAB H (Sp K)) (ν : SABMap tK tM x) (lvK : D.La → (𝟙_ (Over (Sp K)) ⟶ tK.G)) (θ : tK.G.left ⟶ c.A.left), 0 < N → FamCore D sM tM lev → Flat sV → x ≫ sM = spMap (algebraMap V K) ≫ sV → (∀ a, (lvK a).left ≫ ν.φ = x ≫ (lev a).left) → IsGrpPullback tK.G c.A (spMap (algebraMap V K) ≫ y) θ → (∀ u, (lvK (bas u)).left ≫ θ = (spMap (algebraMap V K) ≫ y) ≫ (c.lev u).left) → ∃ x' : Sp V ⟶ MM, spMap (algebraMap V K) ≫ x' = x ∧ x' ≫ sM = sV := by
  intro hX hL hL₂ E _ _ _ H D n N MM sM tM lev g B _ ζ Y sY c bas V K _ _ _ _ _ _ sV y x tK ν lvK θ hN F hfl hx hlv hθ hl
  have hK := (GlobalTheory.fullObj_pull E H D n N _ _ sM tM lev x).2 tK ν lvK hlv F.obj
  rw [hx] at hK
  have hA := isGrpPullback_pullback c.A y
  have := c.ab.smooth
  have := c.ab.proper
  have := c.ab.geomConnected
  have hab : IsAbelianScheme ((Over.pullback y).obj c.A) :=
    ⟨inferInstance, MorphismProperty.of_isPullback (P := @Smooth) hA.1 ‹_›,
      MorphismProperty.of_isPullback (P := @IsProper) hA.1 ‹_›,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hA.1 ‹_›⟩
  obtain ⟨φ, hφ₁, hφ₂⟩ : ∃ φ : tK.G.left ⟶ ((Over.pullback y).obj c.A).left, φ ≫ pullback.fst _ _ = θ ∧
      φ ≫ ((Over.pullback y).obj c.A).hom = tK.G.hom ≫ spMap (algebraMap V K) :=
    ⟨hA.1.lift θ _ (hθ.1.w.trans (Category.assoc _ _ _).symm), hA.1.lift_fst _ _ _, hA.1.lift_snd _ _ _⟩
  obtain ⟨t, m, e, he, hmon, hamp, hkt⟩ := GlobalTheory.T.exists_principallyPolarizedCM_extension_dvr hX hL hL₂ E H V K _ tK φ hab
    (hA.cancel (by rw [hφ₁]; exact hθ) hφ₂) hK.ample hK.ktriv
  have hψ : IsGrpPullback t.G c.A y (e.hom.left ≫ pullback.fst _ _) :=
    ((isGrpPullback_of_iso e).comp hA).congr (Category.id_comp _) rfl
  have hθ' : m.φ ≫ e.hom.left ≫ pullback.fst _ _ = θ := by rw [← Category.assoc, he, hφ₁]
  generalize e.hom.left ≫ pullback.fst c.A.hom y = ψ at hψ hθ'
  have hex : ∀ a : D.La, ∃ s : 𝟙_ (Over (Sp V)) ⟶ t.G, s.left ≫ ψ = y ≫ (c.lev (bas.symm a)).left := fun a =>
    ⟨Over.homMk (hψ.1.lift (y ≫ (c.lev (bas.symm a)).left) (𝟙 _) (by
      rw [Category.assoc, Over.w]; exact (Category.comp_id _).trans (Category.id_comp _).symm))
      (hψ.1.lift_snd _ _ _), hψ.1.lift_fst _ _ _⟩
  choose lv hlv' using hex
  let U : Over.mk ((𝟙_ (Over (Sp V))).hom ≫ y) ⟶ 𝟙_ (Over Y) := toUnit _
  have hU : U.left = y := (Category.comp_id _).symm.trans ((Over.w U).trans (Category.id_comp _))
  have hpush : ∀ a, pushHom hψ _ (lv a) = U ≫ c.lev (bas.symm a) := fun a =>
    Over.OverMorphism.ext ((hlv' a).trans (by rw [Over.comp_left, hU]))
  have hinj : Function.Injective (pushHom hψ (𝟙_ (Over (Sp V)))) := fun a b h =>
    Over.OverMorphism.ext (hψ.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  have hadd : ∀ a b, lv (a + b) = lv a * lv b := fun a b => hinj (by
    rw [map_mul, hpush, hpush, hpush, map_add, c.lev_add, MonObj.comp_mul])
  have hker : ∀ a, lv (N • a) = 1 := fun a => by
    have h0 : lv 0 = 1 := by simpa using hadd 0 0
    have hk : ∀ k : ℕ, lv (k • a) = lv a ^ k := fun k => by
      induction k with
      | zero => simpa using h0
      | succ k ih => rw [succ_nsmul, hadd, ih, pow_succ]
    apply hinj
    rw [hk, map_pow, map_one, hpush, ← MonObj.comp_pow, c.lev_tors, MonObj.comp_one]
  have hm : ∀ a, (lvK a).left ≫ m.φ = spMap (algebraMap V K) ≫ (lv a).left := fun a =>
    ObjComp.sec_cancel hψ.1 m.cart.1.w (Over.w (lv a)) (Over.w (lvK a)) (hlv' a) (by
      rw [hθ']; simpa using hl (bas.symm a))
  have hV := GlobalTheory.FullSpread.fullObj_of_genericFibre hL hL₂ E H D n N V K sV t lv tK m lvK hN
    (MorphismProperty.of_isPullback (P := @IsProper) hψ.1 ‹_›) hamp hkt hadd hker hm hK
  obtain ⟨x', ⟨hx', m', hm'⟩, -⟩ := F.rep _ sV t lv inferInstance inferInstance hfl hV
  have : Flat (spMap (algebraMap V K)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K (nonZeroDivisors V))
  obtain ⟨m'', hm''⟩ := ObjMaps.exists_sab_comp m' m
  refine ⟨x', (F.rep _ _ tK lvK inferInstance inferInstance inferInstance hK).unique
    ⟨by rw [Category.assoc, hx'], m'', fun a => ?_⟩ ⟨hx, ν, hlv⟩, hx'⟩
  rw [hm'']
  exact ObjComp.sec_comp (hm' a) (hm a)

end GlobalTheory.FamSiegel

namespace GlobalTheory.FamSiegel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {n N : ℕ}

theorem locallyOfFiniteType_of_qproj {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (h : IsQProjOver s) :
    LocallyOfFiniteType s := by
  obtain ⟨N, i, hi, -, hs⟩ := h
  have := isProper_str R N
  rw [← hs]
  infer_instance

theorem isSeparated_of_qproj {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (h : IsQProjOver s) :
    IsSeparated s := by
  obtain ⟨N, i, hi, -, hs⟩ := h
  have := isProper_str R N
  rw [← hs]
  infer_instance

theorem isReduced_of_flat_preimmersion {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] [IsPreimmersion f] [IsReduced Y] :
    IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have hs : Function.Surjective (f.stalkMap x).hom := f.stalkMap_surjective x
    have hi : Function.Injective (f.stalkMap x).hom := by
      have hf := Flat.stalkMap f x
      algebraize [(f.stalkMap x).hom]
      have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
        inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
      have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (f x)) (B := X.presheaf.stalk x)
      exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
    exact isReduced_of_injective (RingEquiv.ofBijective _ ⟨hi, hs⟩).symm (RingEquiv.injective _)
  exact isReduced_of_isReduced_stalk X

variable {MM : Scheme.{0}} {sM : MM ⟶ Sp (RZ H n N)} {tM : SAB H MM} {lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)}
  {g p : ℕ} {Ag : SiegelFamily g p N} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La}
  {O : Type} [CommRing O] {b : RZ H n N →+* O} {z : ZP p N →+* O}

theorem unramified (hL : Out.Laws) (F : FamCore D sM tM lev) {t : SAB H (pullback sM (spMap b))}
    (ν : SABMap t tM (pullback.fst _ _)) {lv : D.La → (𝟙_ (Over (pullback sM (spMap b))) ⟶ t.G)}
    (hlv : ∀ a, (lv a).left ≫ ν.φ = pullback.fst _ _ ≫ (lev a).left)
    {w : pullback sM (spMap b) ⟶ pullback Ag.s (spMap z)} [LocallyOfFiniteType w]
    (hw : SiegData (pullback.snd _ _) t lv Ag z bas w) : FormallyUnramified w := by
  obtain ⟨θ, θ₂, hθ, hsq, hiso, hl⟩ := GlobalTheory.SiegelDirect.direct E H D O _ _ t lv g p N Ag z bas w hw
  have hs : w ≫ pullback.snd _ _ = pullback.snd sM (spMap b) := by
    obtain ⟨_, _, _, -, -, -, -, h, -⟩ := hw
    exact h
  have hp : IsProper t.G.hom := MorphismProperty.of_isPullback (P := @IsProper) ν.cart.1 F.obj.proper
  refine TangentCrit.formallyUnramified_of_tangent w fun k _ _ x hx => ?_
  have hx' : x ≫ w = constPt x ≫ w := hx.trans (by simp only [constPt, Category.assoc])
  have hy : x ≫ w ≫ pullback.fst _ _ = constPt x ≫ w ≫ pullback.fst _ _ := by
    rw [← Category.assoc, hx', Category.assoc]
  have h₂ : x ≫ pullback.snd sM (spMap b) = constPt x ≫ pullback.snd sM (spMap b) := by
    rw [← hs, ← Category.assoc, hx', Category.assoc]
  obtain ⟨t', κ, lv', hlv'⟩ := (GlobalTheory.fullObj_pull E H D n N _ _ (pullback.fst _ _ ≫ sM) t lv x).1
  obtain ⟨κ', hκ'⟩ := exists_sabMap_constPt hL E H k _ _ t Ag.univ.A inferInstance Ag.univ.P _ θ θ₂ x t' κ hp Ag.univ.isLB hθ hsq
    hiso hy
  have hlv'' : ∀ a, (lv' a).left ≫ κ'.φ = constPt x ≫ (lv a).left := fun a => by
    obtain ⟨u, rfl⟩ := bas.surjective a
    refine ObjComp.sec_cancel hθ.1 κ'.cart.1.w (Over.w (lv (bas u))) (Over.w (lv' (bas u))) (hl u) ?_
    rw [hκ', ← hy]
    exact ObjComp.sec_comp (hl u) (hlv' (bas u))
  obtain ⟨m, hm⟩ := ObjMaps.exists_sab_comp ν κ
  have e' : constPt x ≫ pullback.fst sM (spMap b) = constPt (x ≫ pullback.fst _ _) := by
    simp only [constPt, Category.assoc]
  obtain ⟨m', hm'⟩ : ∃ m' : SABMap t' tM (constPt (x ≫ pullback.fst _ _)), m'.φ = κ'.φ ≫ ν.φ := by
    rw [← e']; exact ObjMaps.exists_sab_comp ν κ'
  refine pullback.hom_ext ?_ h₂
  refine (F.unram k _ t' lv' m m' ?_ (fun a => ?_) fun a => ?_).trans e'.symm
  · rw [← e', Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, h₂, Category.assoc]
  · rw [hm]; exact ObjComp.sec_comp (hlv a) (hlv' a)
  · rw [hm', ← e']; exact ObjComp.sec_comp (hlv a) (hlv'' a)

theorem proper (hX : GlobalTheory.LN.HomExtSt) (hL : Out.Laws) (hL₂ : Out.Laws2) (hN : 0 < N) (F : FamCore D sM tM lev)
    [IsDedekindDomain (RZ H n N)] [IsDomain O] [IsNoetherianRing O] (hb : Function.Injective b)
    (hq : IsQProjOver Ag.s) {t : SAB H (pullback sM (spMap b))}
    (ν : SABMap t tM (pullback.fst _ _)) {lv : D.La → (𝟙_ (Over (pullback sM (spMap b))) ⟶ t.G)}
    (hlv : ∀ a, (lv a).left ≫ ν.φ = pullback.fst _ _ ≫ (lev a).left)
    {w : pullback sM (spMap b) ⟶ pullback Ag.s (spMap z)}
    (hw : SiegData (pullback.snd _ _) t lv Ag z bas w) : IsProper w := by
  obtain ⟨θ, θ₂, hθ, -, -, hl⟩ := GlobalTheory.SiegelDirect.direct E H D O _ _ t lv g p N Ag z bas w hw
  have hs : w ≫ pullback.snd _ _ = pullback.snd sM (spMap b) := by
    obtain ⟨_, _, _, -, -, -, -, h, -⟩ := hw
    exact h
  have := isSeparated_of_qproj hq
  have := locallyOfFiniteType_of_qproj hq
  have := F.flat
  have : IsLocallyNoetherian (pullback Ag.s (spMap z)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Ag.s (spMap z))
  refine GlobalTheory.ValuativeGeneric.isProper_of_lift_generic O _ _ w (pullback.snd _ _) inferInstance ?_ ?_
  · rw [hs]
    exact (GlobalTheory.isQProjOver_finite_and_baseChange _ _ sM F.qproj).2 O b
  intro V K _ _ _ _ _ _ _ x y hx hxy
  have h₂ : x ≫ pullback.snd sM (spMap b) = spMap (algebraMap V K) ≫ y ≫ pullback.snd _ _ := by
    rw [← hs, ← Category.assoc, hxy, Category.assoc]
  have hfl : Flat ((y ≫ pullback.snd _ _) ≫ spMap b) :=
    GlobalTheory.GenericFlat.generic_charZero_and_flat.2 _ O b _ (pullback.snd sM (spMap b)) V K x _ hb inferInstance hx h₂
  obtain ⟨t', κ, lv', hlv'⟩ := (GlobalTheory.fullObj_pull E H D n N _ _ (pullback.fst _ _ ≫ sM) t lv x).1
  obtain ⟨m, hm⟩ := ObjMaps.exists_sab_comp ν κ
  have hy : x ≫ w ≫ pullback.fst _ _ = spMap (algebraMap V K) ≫ y ≫ pullback.fst _ _ := by
    rw [← Category.assoc, hxy, Category.assoc]
  obtain ⟨x', hx₁, hx₂⟩ := exists_extension hX hL hL₂ E H D n N MM sM tM lev g _ _ _ _ Ag.univ bas V K _ (y ≫ pullback.fst _ _) _ t' m
    lv' (κ.φ ≫ θ) hN F hfl
    (by rw [Category.assoc, pullback.condition, ← Category.assoc, h₂]; simp only [Category.assoc])
    (fun a => by rw [hm]; exact ObjComp.sec_comp (hlv a) (hlv' a))
    (hy ▸ κ.cart.comp hθ) (fun u => hy ▸ ObjComp.sec_comp (hl u) (hlv' (bas u)))
  refine ⟨pullback.lift x' (y ≫ pullback.snd _ _) hx₂, pullback.hom_ext ?_ ?_⟩
  · rw [Category.assoc, pullback.lift_fst, hx₁]
  · rw [Category.assoc, pullback.lift_snd, h₂]

theorem core (hX : GlobalTheory.LN.HomExtSt) (hL : Out.Laws) (hL₂ : Out.Laws2) (hN : 0 < N) (hodd : Odd N)
    (F : FamCore D sM tM lev) [IsDedekindDomain (RZ H n N)] [IsDomain O] [CharZero O] [IsNoetherianRing O]
    (hb : Function.Injective b) [Flat (spMap b)] [IsPreimmersion (spMap b)] [Flat (spMap z)] (hu : IsUnit (N : O))
    (hz : z (zetaZP p N) = b (RZ.ze H n N)) (hbas : ∀ x y, D.EF (bas x) (bas y) = omegaStd x y) (hA : SiegRep Ag)
    {t : SAB H (pullback sM (spMap b))}
    (ν : SABMap t tM (pullback.fst _ _)) {lv : D.La → (𝟙_ (Over (pullback sM (spMap b))) ⟶ t.G)}
    (hlv : ∀ a, (lv a).left ≫ ν.φ = pullback.fst _ _ ≫ (lev a).left) :
    ∃ w : pullback sM (spMap b) ⟶ pullback Ag.s (spMap z),
      SiegData (pullback.snd _ _) t lv Ag z bas w ∧ IsFinite w ∧ FormallyUnramified w := by
  have := F.flat
  have := F.red
  have := locallyOfFiniteType_of_qproj F.qproj
  have hn : IsLocallyNoetherian (pullback sM (spMap b)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd sM (spMap b))
  have hr : IsReduced (pullback sM (spMap b)) := isReduced_of_flat_preimmersion (pullback.fst _ _)
  have ho := (GlobalTheory.fullObj_pull E H D n N _ _ sM tM lev _).2 t ν lv hlv F.obj
  rw [pullback.condition] at ho
  obtain ⟨o, φ, φ₂, hpr, h₁, h₂, h₃, h₄⟩ := GlobalTheory.exists_siegPre_of_fullObj hL hL₂ E H D n N p O b z _ (pullback.snd _ _) t lv g bas hodd hu hz hn
    (GlobalTheory.GenericFlat.generic_charZero_and_flat.1 O _ (pullback.snd sM (spMap b)) inferInstance) hbas ho
  obtain ⟨f, ⟨hf, hf'⟩, -⟩ := hA.2 _ _ o hr hn inferInstance hpr
  have hw : SiegData (pullback.snd _ _) t lv Ag z bas (pullback.lift f _ hf) :=
    ⟨o, φ, φ₂, h₁, h₂, h₃, h₄, pullback.lift_snd _ _ _, by rw [pullback.lift_fst]; exact hf'⟩
  have := proper hX hL hL₂ hN F hb hA.1 ν hlv hw
  have := unramified hL F ν hlv hw
  have := TangentCrit.locallyQuasiFinite_of_formallyUnramified (pullback.lift f _ hf)
  exact ⟨_, hw, .of_isProper_of_locallyQuasiFinite _, ‹_›⟩

theorem baseChange {O' : Type} [CommRing O'] (c : O →+* O') {b' : RZ H n N →+* O'} {z' : ZP p N →+* O'}
    (hb : c.comp b = b') (hz : c.comp z = z') {t : SAB H (pullback sM (spMap b))}
    (ν : SABMap t tM (pullback.fst _ _)) {lv : D.La → (𝟙_ (Over (pullback sM (spMap b))) ⟶ t.G)}
    (hlv : ∀ a, (lv a).left ≫ ν.φ = pullback.fst _ _ ≫ (lev a).left)
    {w : pullback sM (spMap b) ⟶ pullback Ag.s (spMap z)} (hw : SiegData (pullback.snd _ _) t lv Ag z bas w)
    [IsFinite w] [FormallyUnramified w] {T : Scheme.{0}} {sT : T ⟶ Sp O'} {f : T ⟶ MM} {tT : SAB H T}
    (κ : SABMap tT tM f) {lvT : D.La → (𝟙_ (Over T) ⟶ tT.G)} (hT : IsPullback f sT sM (spMap b'))
    (hlvT : ∀ a, (lvT a).left ≫ κ.φ = f ≫ (lev a).left) :
    ∃ w' : T ⟶ pullback Ag.s (spMap z'), SiegData sT tT lvT Ag z' bas w' ∧ IsFinite w' ∧ FormallyUnramified w' := by
  have eb : spMap c ≫ spMap b = spMap b' := by rw [← hb, ← Spec.map_comp]; rfl
  have ez : spMap c ≫ spMap z = spMap z' := by rw [← hz, ← Spec.map_comp]; rfl
  have hs : w ≫ pullback.snd _ _ = pullback.snd sM (spMap b) := by
    obtain ⟨_, _, _, -, -, -, -, h, -⟩ := hw
    exact h
  obtain ⟨r, hr₁, hr₂⟩ : ∃ r : T ⟶ pullback sM (spMap b), r ≫ pullback.fst _ _ = f ∧ r ≫ pullback.snd _ _ = sT ≫ spMap c :=
    ⟨pullback.lift f (sT ≫ spMap c) (by rw [Category.assoc, eb, hT.w]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hr : IsPullback r sT (pullback.snd sM (spMap b)) (spMap c) :=
    IsPullback.of_right (by rw [hr₁, eb]; exact hT) hr₂ (IsPullback.of_hasPullback _ _)
  subst hr₁
  obtain ⟨κ', hκ'⟩ := ObjMaps.exists_sab_cancel ν κ
  have hl : ∀ a, (lvT a).left ≫ κ'.φ = r ≫ (lv a).left := fun a =>
    ObjComp.sec_cancel ν.cart.1 κ'.cart.1.w (Over.w (lv a)) (Over.w (lvT a)) (hlv a) (by rw [← hκ']; exact hlvT a)
  have e : (r ≫ pullback.snd sM (spMap b)) ≫ spMap z = sT ≫ spMap z' := by rw [hr₂, Category.assoc, ez]
  obtain ⟨w', hw₁, hw₂⟩ : ∃ w' : T ⟶ pullback Ag.s (spMap z'),
      w' ≫ pullback.fst _ _ = (r ≫ w) ≫ pullback.fst _ _ ∧ w' ≫ pullback.snd _ _ = sT :=
    ⟨pullback.lift ((r ≫ w) ≫ pullback.fst _ _) sT (by
      rw [← e, ← hs]; simp only [Category.assoc, pullback.condition]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨q, hq₁, hq₂⟩ : ∃ q : pullback Ag.s (spMap z') ⟶ pullback Ag.s (spMap z),
      q ≫ pullback.fst _ _ = pullback.fst _ _ ∧ q ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap c :=
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap c) (by rw [Category.assoc, ez, pullback.condition]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hq : IsPullback q (pullback.snd _ _) (pullback.snd Ag.s (spMap z)) (spMap c) :=
    IsPullback.of_right (by rw [hq₁, ez]; exact IsPullback.of_hasPullback _ _) hq₂ (IsPullback.of_hasPullback _ _)
  have hsq : IsPullback r w' w q := by
    refine IsPullback.of_bot (by rw [hw₂, hs]; exact hr) (pullback.hom_ext ?_ ?_) hq
    · rw [Category.assoc w', hq₁, hw₁]
    · rw [Category.assoc, hs, hr₂, Category.assoc, hq₂, ← Category.assoc, hw₂]
  refine ⟨w', ?_, MorphismProperty.of_isPullback (P := @IsFinite) hsq ‹_›,
    MorphismProperty.of_isPullback (P := @FormallyUnramified) hsq ‹_›⟩
  obtain ⟨o, φ, φ₂, h₁, h₂, h₃, h₄, -, h₅⟩ := GlobalTheory.T.siegelData_pullback_of_levelMap E H D O _ T _ r t tT κ' lv lvT g p N Ag z bas w hl hw
  rw [← hw₁] at h₅
  unfold SiegData
  generalize (r ≫ pullback.snd sM (spMap b)) ≫ spMap z = s at e o φ φ₂ h₁ h₂ h₃ h₄ h₅
  subst e
  exact ⟨o, φ, φ₂, h₁, h₂, h₃, h₄, hw₂, h₅⟩

theorem exists_lift_subring {O : Type} [CommRing O] {i : O →+* ℂ} (hi : Function.Injective i) {S : Subring ℂ}
    (h : S ≤ i.range) : ∃ c : S →+* O, ∀ x, i (c x) = x := by
  let e : O ≃+* i.range :=
    RingEquiv.ofBijective i.rangeRestrict ⟨fun _ _ h => hi (congrArg Subtype.val h), i.rangeRestrict_surjective⟩
  exact ⟨e.symm.toRingHom.comp (Subring.inclusion h), fun x => congrArg Subtype.val (e.apply_symm_apply ⟨x, h x.2⟩)⟩

theorem isUnit_natCast_of_inv_mem {S : Subring ℂ} {m : ℕ} (hm : m ≠ 0) (h : (m : ℂ)⁻¹ ∈ S) : IsUnit (m : S) := by
  refine IsUnit.of_mul_eq_one ⟨_, h⟩ (Subtype.ext ?_)
  simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hm : (m : ℂ) ≠ 0)

end GlobalTheory.FamSiegel

open GlobalTheory.FamSiegel in

theorem GlobalTheory.siegClause_of_famCore : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)), 1 ≤ D.p + D.q → n.Prime → Odd n → (∃ j, 1 ≤ j ∧ N = n ^ j) → FamCore D sM tM lev → (∀ p : ℕ, p.Prime → p ≠ n → ∃ Ag : SiegelFamily (Module.finrank ℚ E / 2 * (D.p + D.q)) p N, SiegRep Ag) → SiegClause D sM tM lev := by
  intro hX hL hL₂ E _ _ _ H D n N MM sM tM lev _ hn hodd hj F hAg p hp hpn
  obtain ⟨Ag, hA⟩ := hAg p hp hpn
  obtain ⟨bas₀, hbas₀⟩ := GlobalTheory.ZM.exists_isSympBasis E H D
  obtain ⟨-, bas, hbas⟩ := GlobalTheory.ZM.sympBasis_std E H D _ bas₀ hbas₀
  obtain ⟨hD, hO, h₁, h₂, h₃⟩ := GlobalTheory.JoinRing.join_rings E H n N p hn hj hp hpn
  obtain ⟨j, -, hj⟩ := hj
  have hN : 0 < N := by rw [hj]; exact pow_pos hn.pos j
  have hNo : Odd N := by rw [hj]; exact hodd.pow
  refine ⟨Ag, bas, hbas, fun O _ i z b hi hz hb T sT f tT κ lvT hT hlvT => ?_⟩
  have hle : RZ H n N ⊔ ZP p N ≤ i.range :=
    sup_le (fun x hx => ⟨b ⟨x, hx⟩, hb _⟩) fun x hx => ⟨z ⟨x, hx⟩, hz _⟩
  obtain ⟨S, l₁, l₂, hO, h₁, h₂, h₃, hle⟩ : ∃ (S : Subring ℂ) (l₁ : RZ H n N ≤ S) (l₂ : ZP p N ≤ S),
      IsNoetherianRing S ∧ Flat (spMap (Subring.inclusion l₁)) ∧ IsPreimmersion (spMap (Subring.inclusion l₁)) ∧
        Flat (spMap (Subring.inclusion l₂)) ∧ S ≤ i.range := ⟨_, le_sup_left, le_sup_right, hO, h₁, h₂, h₃, hle⟩
  have hu : IsUnit (N : S) := by
    have := (isUnit_natCast_of_inv_mem hn.ne_zero (l₁ (Subring.subset_closure (Or.inr (Or.inl rfl))))).pow j
    rwa [← Nat.cast_pow, ← hj] at this
  obtain ⟨t, ν, lv, hlv⟩ := (GlobalTheory.fullObj_pull E H D n N _ _ sM tM lev (pullback.fst sM (spMap (Subring.inclusion l₁)))).1
  obtain ⟨w, hw, _, _⟩ := core (z := Subring.inclusion l₂) hX hL hL₂ hN hNo F (Subring.inclusion_injective l₁) hu
    (Subtype.ext rfl) hbas hA ν hlv
  obtain ⟨c, hc⟩ := exists_lift_subring hi hle
  exact baseChange c (RingHom.ext fun x => hi ((hc ⟨x, l₁ x.2⟩).trans (hb x).symm))
    (RingHom.ext fun x => hi ((hc ⟨x, l₂ x.2⟩).trans (hz x).symm)) ν hlv hw κ hT hlvT
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmFamily_finite_unramified_over_siegelFamily : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)), 1 ≤ D.p + D.q → n.Prime → Odd n → (∃ j, 1 ≤ j ∧ N = n ^ j) → FamCore D sM tM lev → (∀ p : ℕ, p.Prime → p ≠ n → ∃ Ag : SiegelFamily (Module.finrank ℚ E / 2 * (D.p + D.q)) p N, SiegRep Ag) → SiegClause D sM tM lev := by
  first | exact @GlobalTheory.siegClause_of_famCore | exact GlobalTheory.siegClause_of_famCore | (intros; apply GlobalTheory.siegClause_of_famCore <;> assumption)
end
