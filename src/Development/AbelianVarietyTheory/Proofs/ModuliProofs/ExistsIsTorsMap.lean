import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPullbackPow
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IotaPointsAdditive
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePairIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OverExtOfPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionToG
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAdicColimitOfIsFiniteNoetherian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePartImageGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartImagePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionFiniteFlatIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndFlatMulAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPtsEquiv

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.IotaExists

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorsionFormCompare

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}

theorem val_tauW (ψW : PsiOn D W) (a b : D.X) {Z : Scheme.{0}} (r : Z ⟶ W.toScheme) {z : Z} {J}
    (hJ : Good D.P.L z J) :
    val (ψW.tau a b) r z J = val (ψW.psi (a + b)) r z J * (val (ψW.psi a) r z J)⁻¹ * (val (ψW.psi b) r z J)⁻¹ *
      (val (D.rigW W) r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem tauW_symm (ψW : PsiOn D W) (a b : D.X) {Z : Scheme.{0}} (r : Z ⟶ W.toScheme) {z : Z} {J}
    (hJ : Good D.P.L z J) : val (ψW.tau a b) r z J = val (ψW.tau b a) r z J :=
  (val_tauW ψW a b r hJ).trans ((congrArg₂ (· * ·) ((mul_right_comm _ _ _).trans (congrArg₂ (· * ·)
    (congrArg₂ (· * ·) (congrArg (fun x => val (ψW.psi x) r z J) (add_comm a b)) rfl) rfl)) rfl).trans
      (val_tauW ψW b a r hJ).symm)

theorem existsUnique_iota (hB : D.TauBimult) (ψW : PsiOn D W) (T : Over W.toScheme) (y : D.X) :
    ∃! g : GtPt D (overW W T), GtPt.IsIotaW ψW y g := by
  let ρ : overW W T ⟶ TW W := Over.homMk T.hom rfl
  have vv : ∀ χ z J, Good D.P.L z J →
      val (LB.pullGen D.P.L _ _ (ψW.tau y χ) T.hom) (𝟙 (overW W T).left) z J = val (ψW.tau χ y) ρ.left z J :=
    fun χ z J hJ => ((val_pull hJ _ _ _).trans
      (congrArg (fun r => val (ψW.tau y χ) r z J) (Category.id_comp _))).trans (tauW_symm ψW y χ _ hJ)
  obtain ⟨g, hb, hv⟩ := TorusModel.exists_pt (D := D) (T := overW W T) (cP D _ y)
    (fun χ => LB.pullGen D.P.L _ _ (ψW.tau y χ) T.hom)
    (fun χ => pullGen_isGen _ _ _ _ (IotaAdditive.tau_isGen ψW y χ) _) (fun χ U _ h => by
      have p : ∀ x y w v : (TW W).left ⟶ D.P.A.left, ∏ i : ((PUnit ⊕ PUnit) ⊕ PUnit) ⊕ PUnit.{1},
          h (ρ.left ≫ Sum.elim (Sum.elim (Sum.elim (fun _ => x) (fun _ => y)) (fun _ => w)) (fun _ => v) i) ^
            Sum.elim (Sum.elim (Sum.elim (fun _ => (-1 : ℤ)) (fun _ => - -1)) (fun _ => - -1)) (fun _ => -1) i =
          (h (ρ.left ≫ x))⁻¹ * h (ρ.left ≫ y) * h (ρ.left ≫ w) * (h (ρ.left ≫ v))⁻¹ := fun x y w v => by
        simp [Fintype.prod_sum_type]
      refine (p (cP D _ (y + χ)).left (cP D _ y).left (cP D _ χ).left (1 : TW W ⟶ D.P.A).left).trans ?_
      rw [TorusModel.prod_pt, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left,
        comp_cP, comp_cP, comp_cP, MonObj.comp_one, add_comm y χ, cPoint_add, mul_right_comm _ (h (cP D _ y).left)])
    (fun z J hJ => by
      have C : IsCub (th D (T := overW W T) z J) := isCub_cubV D.cub hJ
      have t := IotaAdditive.tau_mul hB ψW 0 0 y ρ hJ
      rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
      exact (vv 0 z J hJ).trans (mul_eq_left.1 t.symm))
    (fun χ χ' z J hJ => (congrArg₂ (· * ·) (vv _ z J hJ) rfl).trans
      ((IotaAdditive.tau_mul hB ψW χ χ' y ρ hJ).trans (congrArg₂ (· * ·) (vv _ z J hJ) (vv _ z J hJ)).symm))
  refine ⟨g, ⟨hb, fun χ => corr_of_val D.P.isLB fun z J hJ => hv χ _ _ z J hJ⟩, fun g' H => ?_⟩
  exact TorusModel.pt_ext (H.1.trans hb.symm) fun χ z J hJ =>
    (val_corr hJ (H.2 χ) (𝟙 _)).trans (hv χ _ _ z J hJ).symm

theorem iota_existsUnique : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ (T : Over W.toScheme) (y : P.D.toPre.X), ∃! g : GtPt P.D.toPre (overW W T), GtPt.IsIotaW ψW y g :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ P _ _ _ ψW _ _ T y => existsUnique_iota P.D.tau_bimult ψW T y

end GlobalTheory.IotaExists
end
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.PairScheme

open GlobalTheory.TorusModel GlobalTheory.TorsionFormCompare

theorem formallyUnramified_fibre {S S' N W : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (k : ℕ)
    (j : S' ⟶ S) (hk : IsUnit (k : Γ(S', ⊤))) (w : W ⟶ S) [IsOpenImmersion w] {s : W ⟶ G.left} (hs : s ≫ G.hom = w)
    {n : N ⟶ G.left} {q : N ⟶ W} (H : IsPullback n q ((𝟙 G) ^ k : G ⟶ G).left s) :
    FormallyUnramified (pullback.snd (q ≫ w) j) := by
  have hm : ((𝟙 G) ^ k : G ⟶ G).left ≫ G.hom = G.hom := Over.w _
  have hn : n ≫ G.hom = q ≫ w := by rw [← hm, ← Category.assoc, H.w, Category.assoc, hs]
  have e : (Over.pullback j).map ((𝟙 G) ^ k : G ⟶ G) = mulA ((Over.pullback j).obj G) k :=
    (map_pow (Over.pullback j).homMonoidHom (𝟙 G) k).trans
      (congrArg (· ^ k) (CategoryTheory.Functor.map_id (Over.pullback j) G))
  let m' : pullback G.hom j ⟶ pullback G.hom j := ((Over.pullback j).map ((𝟙 G) ^ k : G ⟶ G)).left
  have hu : FormallyUnramified m' := by
    have := formallyUnramified_mulA S' ((Over.pullback j).obj G) k hk
    rw [← e] at this
    exact this
  have m1 : m' ≫ pullback.fst G.hom j = pullback.fst G.hom j ≫ ((𝟙 G) ^ k : G ⟶ G).left := pullback.lift_fst _ _ _
  have m2 : m' ≫ pullback.snd G.hom j = pullback.snd G.hom j := pullback.lift_snd _ _ _
  have PR : IsPullback (pullback.fst G.hom j) m' ((𝟙 G) ^ k : G ⟶ G).left (pullback.fst G.hom j) :=
    IsPullback.of_bot (by rw [m2, hm]; exact IsPullback.of_hasPullback _ _) m1.symm (IsPullback.of_hasPullback _ _)
  let q' : pullback (q ≫ w) j ⟶ pullback w j :=
    pullback.lift (pullback.fst _ _ ≫ q) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])
  have q1 : q' ≫ pullback.fst w j = pullback.fst _ _ ≫ q := pullback.lift_fst _ _ _
  have q2 : q' ≫ pullback.snd w j = pullback.snd _ _ := pullback.lift_snd _ _ _
  have PQ : IsPullback (pullback.fst (q ≫ w) j) q' q (pullback.fst w j) :=
    IsPullback.of_bot (by rw [q2]; exact IsPullback.of_hasPullback _ _) q1.symm (IsPullback.of_hasPullback _ _)
  let n' : pullback (q ≫ w) j ⟶ pullback G.hom j :=
    pullback.lift (pullback.fst _ _ ≫ n) (pullback.snd _ _) (by rw [Category.assoc, hn, pullback.condition])
  have n1 : n' ≫ pullback.fst G.hom j = pullback.fst _ _ ≫ n := pullback.lift_fst _ _ _
  have n2 : n' ≫ pullback.snd G.hom j = pullback.snd _ _ := pullback.lift_snd _ _ _
  let s' : pullback w j ⟶ pullback G.hom j :=
    pullback.lift (pullback.fst _ _ ≫ s) (pullback.snd _ _) (by rw [Category.assoc, hs, pullback.condition])
  have s1 : s' ≫ pullback.fst G.hom j = pullback.fst _ _ ≫ s := pullback.lift_fst _ _ _
  have s2 : s' ≫ pullback.snd G.hom j = pullback.snd _ _ := pullback.lift_snd _ _ _
  have PL : IsPullback n' q' m' s' := by
    refine IsPullback.of_right (by rw [n1, s1]; exact PQ.paste_horiz H) ?_ PR
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, m1, s1, reassoc_of% n1, reassoc_of% q1, H.w]
    · rw [Category.assoc, Category.assoc, m2, s2, n2, q2]
  have : FormallyUnramified q' := MorphismProperty.of_isPullback (P := @FormallyUnramified) PL hu
  rw [← q2]
  exact MorphismProperty.comp_mem (@FormallyUnramified) _ _ this inferInstance

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {Gt : Over (Sp R)} [GrpObj Gt]
  {Φ : ∀ T, (T ⟶ Gt) ≃ GtPt D T}

theorem isNsmul_iff (hΦ : Represents Φ) (k : ℕ) {T : Over (Sp R)} (x z : T ⟶ Gt) :
    GtPt.IsNsmul k (Φ T x) (Φ T z) ↔ x ^ k = z := by
  constructor
  · rintro ⟨u, u0, us, hz⟩
    have : ∀ i : Fin (k + 1), u i = Φ T (x ^ (i : ℕ)) := fun i => by
      induction i using Fin.induction with
      | zero => exact isZero_unique u0 (by simpa using isZero_one hΦ T)
      | succ i ih =>
        have h := us i
        rw [ih] at h
        rw [Fin.val_succ, pow_succ]
        exact isAdd_unique h (hΦ.2 T _ _)
    exact (Φ T).injective ((this (Fin.last k)).symm.trans hz)
  · rintro rfl
    refine ⟨fun i => Φ T (x ^ (i : ℕ)), by simpa using isZero_one hΦ T, fun i => ?_, rfl⟩
    simp only [Fin.val_succ, Fin.val_castSucc, pow_succ]
    exact hΦ.2 T _ _

theorem isIotaW_pull {W : (Sp R).Opens} {ψW : PsiOn D W} {T T' : Over W.toScheme} (h : T' ⟶ T) {y : D.X}
    {g : GtPt D (overW W T)} {g' : GtPt D (overW W T')} (H : GtPt.IsPull h.left g g') (hg : GtPt.IsIotaW ψW y g) :
    GtPt.IsIotaW ψW y g' := by
  refine ⟨Over.OverMorphism.ext (H.1.trans ?_), fun χ => corr_of_val D.P.isLB fun z J hJ => ?_⟩
  · rw [hg.1]
    exact congrArg (·.left) (comp_toUnit_assoc ((Over.map W.ι).map h) (D.c y))
  · refine (val_corr hJ (H.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (hg.2 χ) _).trans
      ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))))
    rw [Category.assoc, Over.w h]

theorem exists_pairRep [CharZero R] [IsCommMonObj Gt] (hΦ : Represents Φ) {W : (Sp R).Opens} (ψW : PsiOn D W) {k : ℕ}
    (hk : 1 ≤ k) [IsFinite ((𝟙 Gt) ^ k : Gt ⟶ Gt).left] [Flat ((𝟙 Gt) ^ k : Gt ⟶ Gt).left]
    [Surjective ((𝟙 Gt) ^ k : Gt ⟶ Gt).left] (y : D.X)
    (hι : ∀ T : Over W.toScheme, ∃! g : GtPt D (overW W T), GtPt.IsIotaW ψW y g) :
    ∃ (N : Over W.toScheme) (p₀ : QkPtW D W ψW k N), PairRep ψW k y N p₀ := by
  obtain ⟨g₀, hg₀, -⟩ := hι (Over.mk (𝟙 _))
  obtain ⟨s, rfl⟩ := (Φ _).surjective g₀
  let s₀ : W.toScheme ⟶ Gt.left := s.left
  have hs : s₀ ≫ Gt.hom = W.ι := (Over.w s).trans (Category.id_comp _)
  let m : Gt.left ⟶ Gt.left := ((𝟙 Gt) ^ k : Gt ⟶ Gt).left
  have hm : m ≫ Gt.hom = Gt.hom := Over.w _
  let τ : ∀ T : Over W.toScheme, T ⟶ Over.mk (𝟙 _) := fun T => Over.homMk T.hom (Category.comp_id _)
  have io : ∀ T, GtPt.IsIotaW ψW y (Φ _ ((Over.map W.ι).map (τ T) ≫ s)) := fun T =>
    isIotaW_pull (τ T) (hΦ.1 _ _ ((Over.map W.ι).map (τ T)) s) hg₀
  have key : ∀ (T : Over W.toScheme) (x : overW W T ⟶ Gt),
      (∃ h, GtPt.IsNsmul k (Φ _ x) h ∧ GtPt.IsIotaW ψW y h) ↔ x.left ≫ m = T.hom ≫ s₀ := fun T x => by
    have e : x.left ≫ m = (x ^ k).left := by
      rw [← Category.comp_id x, ← MonObj.comp_pow, Category.comp_id]; rfl
    rw [e]
    constructor
    · rintro ⟨h, h₁, h₂⟩
      rw [(hι T).unique h₂ (io T), isNsmul_iff hΦ] at h₁
      exact congrArg (·.left) h₁
    · exact fun h => ⟨_, (isNsmul_iff hΦ _ _ _).2 (Over.OverMorphism.ext h), io T⟩
  let N : Over W.toScheme := Over.mk (pullback.snd m s₀)
  let n : overW W N ⟶ Gt := Over.homMk (pullback.fst m s₀) (by
    rw [← hm, ← Category.assoc, pullback.condition, Category.assoc, hs]; rfl)
  have hf : IsFinite N.hom := inferInstanceAs (IsFinite (pullback.snd m s₀))
  have hl : Flat N.hom := inferInstanceAs (Flat (pullback.snd m s₀))
  refine ⟨N, ⟨y, Φ _ n, (key N n).2 pullback.condition⟩, ⟨hf, hl, ?_⟩,
    inferInstanceAs (Surjective (pullback.snd m s₀)), rfl, ?_⟩
  · change Etale (pullback.snd (N.hom ≫ W.ι) (jK R))
    have : FormallyUnramified (pullback.snd (N.hom ≫ W.ι) (jK R)) := by
      refine formallyUnramified_fibre Gt k (jK R) ?_ W.ι hs (IsPullback.of_hasPullback m s₀)
      have : IsUnit (k : FractionRing R) := by
        have : CharZero (FractionRing R) := IsFractionRing.charZero_of_isFractionRing R
        exact (Nat.cast_ne_zero.2 (by omega) : (k : FractionRing R) ≠ 0).isUnit
      simpa using this.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
    exact Etale.of_formallyUnramified_of_flat _
  · rintro T ⟨y', g, hg⟩ rfl
    obtain ⟨x, rfl⟩ := (Φ _).surjective g
    have hx := (key T x).1 hg
    refine ⟨Over.homMk (pullback.lift x.left T.hom hx) (pullback.lift_snd _ _ _), ⟨rfl, ?_⟩, fun h hh => ?_⟩
    · exact (isPull_iff_comp hΦ ((Over.map W.ι).map (Over.homMk (pullback.lift x.left T.hom hx)
        (pullback.lift_snd _ _ _) : T ⟶ N)) n x).2 (Over.OverMorphism.ext (pullback.lift_fst _ _ _))
    · have e := (isPull_iff_comp hΦ ((Over.map W.ι).map h) n x).1 hh.2
      refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
      · exact (congrArg (·.left) e).trans (pullback.lift_fst x.left T.hom hx).symm
      · exact (Over.w h).trans (pullback.lift_snd x.left T.hom hx).symm

theorem pairRep_exists : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ y : P.D.toPre.X,
    ∃ (N : Over W.toScheme) (p₀ : QkPtW P.D.toPre W ψW k N), PairRep ψW k y N p₀ := by
  intro E _ _ _ H R _ _ _ _ hR t P W hW hp ψW k hk y
  have := hR.1
  obtain ⟨Gt, _, _, Φ, hΦ, -, -, h⟩ := GlobalTheory.ExtensionMul.exists_represents_pow R P.D.toPre
  obtain ⟨_, _, _⟩ := h k hk
  exact exists_pairRep hΦ ψW hk y fun T => GlobalTheory.IotaExists.iota_existsUnique E H R hR t P W hW hp ψW k hk T y

end GlobalTheory.PairScheme
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_pair_representative : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ y : P.D.toPre.X, ∃ (N : Over W.toScheme) (p₀ : QkPtW P.D.toPre W ψW k N), PairRep ψW k y N p₀ := by
  atlas_forward_decl GlobalTheory.PairScheme.pairRep_exists
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatTors.TorsExt

theorem mem_of_integral (S K F B : Type) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Field K] [Algebra S K]
    [IsFractionRing S K] [Field F] [Algebra S F] [Algebra K F] [IsScalarTower S K F] [CommRing B] [Algebra S B]
    [Module.Finite S B] [Module.Projective S B] (c : K ⊗[S] B) (w : integralClosure S F ⊗[S] B)
    (h : Algebra.TensorProduct.map (IsScalarTower.toAlgHom S K F) (AlgHom.id S B) c =
      Algebra.TensorProduct.map (integralClosure S F).val (AlgHom.id S B) w) :
    ∃ b : B, c = (1 : K) ⊗ₜ[S] b := by
  obtain ⟨n, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective S B
  let ev : ∀ (X : Type) [CommRing X] [Algebra S X], Fin n → X ⊗[S] B →ₗ[S] X := fun X _ _ i =>
    (TensorProduct.rid S X).toLinearMap ∘ₗ LinearMap.lTensor X (LinearMap.proj i ∘ₗ s)
  have nat : ∀ (X : Type) [CommRing X] [Algebra S X] (f : X →ₐ[S] F) (i : Fin n) (x : X ⊗[S] B),
      ev F i (Algebra.TensorProduct.map f (AlgHom.id S B) x) = f (ev X i x) := by
    intro X _ _ f i x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [ev]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hi : ∀ i, ∃ r : S, algebraMap S K r = ev K i c := by
    intro i
    apply IsIntegrallyClosed.isIntegral_iff.1
    apply (isIntegral_algHom_iff (IsScalarTower.toAlgHom S K F) (algebraMap K F).injective).1
    rw [← nat K, h, nat]
    exact (ev _ i w).2
  choose r hr using hi
  have hc : ∀ x : K ⊗[S] B, x = ∑ i, ev K i x ⊗ₜ[S] p (Pi.single i 1) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have hb : b = ∑ i, s b i • p (Pi.single i 1) := by
        conv_lhs => rw [← LinearMap.id_apply (R := S) b, ← hps, LinearMap.comp_apply, pi_eq_sum_univ' (s b), map_sum]
        simp
      conv_lhs => rw [hb, TensorProduct.tmul_sum]
      simp [ev, TensorProduct.smul_tmul]
    | add a b ha hb =>
      simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib]
      rw [← ha, ← hb]
  refine ⟨∑ i, r i • p (Pi.single i 1), ?_⟩
  rw [hc c, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hr, ← TensorProduct.smul_tmul, Algebra.smul_def, _root_.mul_one]

theorem ext_of_geom {D : Type} [CommRing D] [_root_.IsReduced D] {Y Z : Scheme.{0}} (s : Y ⟶ Z) [IsSeparated s]
    (f g : Sp D ⟶ Y) (hs : f ≫ s = g ≫ s)
    (h : ∀ (F : Type) [Field F] [IsAlgClosed F] (φ : D →+* F), spMap φ ≫ f = spMap φ ≫ g) : f = g := by
  refine ext_of_fromSpecResidueField_eq f g s Set.univ dense_univ (fun x _ => ?_) hs
  let k := (Sp D).residueField x
  let σ : k →+* AlgebraicClosure k := algebraMap _ _
  have : Flat (Spec.map (CommRingCat.ofHom σ)) :=
    Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective (Spec.map (CommRingCat.ofHom σ)) :=
    ⟨fun y => ⟨IsLocalRing.closedPoint _, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  have := Flat.epi_of_flat_of_surjective (Spec.map (CommRingCat.ofHom σ))
  rw [← cancel_epi (Spec.map (CommRingCat.ofHom σ))]
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Spec.map (CommRingCat.ofHom σ) ≫ (Sp D).fromSpecResidueField x)
  have := h (AlgebraicClosure k) φ.hom
  simp only [spMap, CommRingCat.ofHom_hom] at this
  rw [← Category.assoc, ← Category.assoc, ← hφ]
  exact this

theorem exists_chart {N W : Scheme.{0}} (q : N ⟶ W) [IsAffineHom q] (S : Type) [CommRing S] (j : Sp S ⟶ W) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra S B) (g : Sp B ⟶ N), IsPullback g (spMap (algebraMap S B)) q j := by
  have : IsAffine (pullback q j) := isAffine_of_isAffineHom (pullback.snd q j)
  let e := (pullback q j).isoSpec
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (e.inv ≫ pullback.snd q j)
  letI : Algebra S Γ(pullback q j, ⊤) := φ.hom.toAlgebra
  refine ⟨Γ(pullback q j, ⊤), inferInstance, inferInstance, e.inv ≫ pullback.fst q j, ?_⟩
  have h : spMap (algebraMap S Γ(pullback q j, ⊤)) = e.inv ≫ pullback.snd q j := hφ
  rw [h]
  exact IsPullback.of_iso_pullback ⟨by simp [pullback.condition]⟩ e.symm rfl rfl

section Affine

variable {X : Scheme.{0}} {S : Type} [CommRing S] (σ : Sp S ⟶ X)

abbrev spO (A : Type) [CommRing A] [Algebra S A] : Over X := Over.mk (spMap (algebraMap S A) ≫ σ)

def spH {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (φ : A →ₐ[S] A') :
    spO σ A' ⟶ spO σ A :=
  Over.homMk (spMap φ.toRingHom) (by
    change spMap φ.toRingHom ≫ spMap (algebraMap S A) ≫ σ = spMap (algebraMap S A') ≫ σ
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact φ.comp_algebraMap)


theorem spH_comp {A A' A'' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] [CommRing A'']
    [Algebra S A''] (φ : A →ₐ[S] A') (ψ : A' →ₐ[S] A'') : spH σ (ψ.comp φ) = spH σ ψ ≫ spH σ φ := by
  ext1
  change spMap _ = spMap _ ≫ spMap _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem exists_ext_affine (K B C : Type) [IsDomain S] [IsIntegrallyClosed S] [Field K] [Algebra S K]
    [IsFractionRing S K] [CommRing B] [Algebra S B] [Module.Finite S B] [Module.Projective S B]
    [Algebra.Etale K (K ⊗[S] B)] [Nontrivial (K ⊗[S] B)] [CommRing C] [Algebra S C] [Module.Finite S C]
    (G : Over X) [GrpObj G] [IsCommMonObj G] [IsSeparated G.hom] (k : ℕ) (n : spO σ C ⟶ G) (hn : n ^ k = 1)
    (univ : ∀ (A : Type) [CommRing A] [Algebra S A] (x : spO σ A ⟶ G), x ^ k = 1 →
      ∃! φ : C →ₐ[S] A, spH σ φ ≫ n = x)
    (u : spO σ (K ⊗[S] B) ⟶ G) (d : spO σ (B ⊗[S] B) ⟶ G) (hu : u ^ k = 1) (hd : d ^ k = 1)
    (H : ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra S F] [Algebra K F] [IsScalarTower S K F]
      (a b : K ⊗[S] B →ₐ[S] F), spH σ a ≫ u = (spH σ b ≫ u) *
        (spH σ (Algebra.TensorProduct.productMap (a.comp Algebra.TensorProduct.includeRight)
          (b.comp Algebra.TensorProduct.includeRight)) ≫ d)) :
    ∃ v : spO σ B ⟶ G, spH σ Algebra.TensorProduct.includeRight ≫ v = u := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[S] B)
  letI := Ideal.Quotient.field m
  let F := AlgebraicClosure ((K ⊗[S] B) ⧸ m)
  let b₀ : K ⊗[S] B →ₐ[S] F := IsScalarTower.toAlgHom S (K ⊗[S] B) F
  obtain ⟨μ₀, hμ, -⟩ := univ _ u hu
  let O := integralClosure S F
  let β : B →ₐ[S] O := (b₀.comp Algebra.TensorProduct.includeRight).codRestrict O fun x =>
    (Algebra.IsIntegral.isIntegral (R := S) x).map _
  let γ₀ : C →ₐ[S] O := (b₀.comp μ₀).codRestrict O fun x =>
    (Algebra.IsIntegral.isIntegral (R := S) x).map _
  let w : spO σ (O ⊗[S] B) ⟶ G := (spH σ (Algebra.TensorProduct.includeLeft.comp γ₀) ≫ n) *
    (spH σ (Algebra.TensorProduct.productMap Algebra.TensorProduct.includeRight
      (Algebra.TensorProduct.includeLeft.comp β)) ≫ d)
  have hw : w ^ k = 1 := by
    simp only [w]
    rw [mul_pow, ← MonObj.comp_pow, ← MonObj.comp_pow, hn, hd]
    simp
  obtain ⟨ω, hω, -⟩ := univ _ w hw
  let iK : K ⊗[S] B →ₐ[S] F ⊗[S] B := Algebra.TensorProduct.map (IsScalarTower.toAlgHom S K F) (AlgHom.id S B)
  let iO : O ⊗[S] B →ₐ[S] F ⊗[S] B := Algebra.TensorProduct.map O.val (AlgHom.id S B)
  have hred : _root_.IsReduced (F ⊗[S] B) := by
    have := Algebra.FormallyUnramified.isReduced_of_field F (F ⊗[K] (K ⊗[S] B))
    exact isReduced_of_injective _ (Algebra.TensorProduct.cancelBaseChange S K F F B).symm.injective
  have key : spH σ iK ≫ u = spH σ iO ≫ w := by
    ext1
    refine ext_of_geom G.hom _ _ (by rw [Over.w, Over.w]) fun F' _ _ φ => ?_
    letI : Algebra S F' := (φ.comp (algebraMap S (F ⊗[S] B))).toAlgebra
    letI : Algebra K F' := (φ.comp (algebraMap K (F ⊗[S] B))).toAlgebra
    have : IsScalarTower S K F' := IsScalarTower.of_algebraMap_eq fun x =>
      congrArg φ (IsScalarTower.algebraMap_apply S K (F ⊗[S] B) x)
    let φ' : F ⊗[S] B →ₐ[S] F' := ⟨φ, fun _ => rfl⟩
    have h := H F' (φ'.comp iK) (φ'.comp (Algebra.TensorProduct.includeLeft.comp b₀))
    suffices spH σ φ' ≫ spH σ iK ≫ u = spH σ φ' ≫ spH σ iO ≫ w from congrArg CommaMorphism.left this
    rw [← Category.assoc, ← spH_comp, h, ← Category.assoc, ← spH_comp]
    simp only [w]
    rw [MonObj.comp_mul, ← hμ]
    simp only [← Category.assoc, ← spH_comp]
    congr 3
    ext x
    · simp [iK, iO]
    · simp [iO, β, ← Algebra.TensorProduct.one_def]
      rfl
  have hμω : iK.comp μ₀ = iO.comp ω := by
    refine (univ _ (spH σ iK ≫ u) (by rw [← MonObj.comp_pow, hu]; simp)).unique ?_ ?_
    · rw [spH_comp, Category.assoc, hμ]
    · rw [spH_comp, Category.assoc, hω, key]
  have hB : ∀ z : C, μ₀ z ∈ (Algebra.TensorProduct.includeRight : B →ₐ[S] K ⊗[S] B).range := fun z => by
    obtain ⟨b, hb⟩ := mem_of_integral S K F B (μ₀ z) (ω z) (DFunLike.congr_fun hμω z)
    exact ⟨b, hb.symm⟩
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight : B →ₐ[S] K ⊗[S] B) :=
    Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective S K)
  let e := AlgEquiv.ofInjective _ hinj
  refine ⟨spH σ (e.symm.toAlgHom.comp (μ₀.codRestrict _ hB)) ≫ n, ?_⟩
  rw [← Category.assoc, ← spH_comp, ← hμ]
  congr 2
  ext z
  exact congrArg Subtype.val (e.apply_symm_apply ⟨μ₀ z, hB z⟩)

end Affine

section Global

variable {R : Type} [CommRing R] [IsDomain R] {W : (Sp R).Opens} {G : Over (Sp R)} [GrpObj G] {k : ℕ}

theorem tors_univ {Z : Over W.toScheme} {n : overW W Z ⟶ G}
    (univ : ∀ (T : Over W.toScheme) (x : overW W T ⟶ G), x ^ k = 1 → ∃! h : T ⟶ Z, (Over.map W.ι).map h ≫ n = x)
    (T : Over (Sp R)) (t : T.left ⟶ W.toScheme) (ht : t ≫ W.ι = T.hom) (x : T ⟶ G) (hx : x ^ k = 1) :
    ∃! h : T.left ⟶ Z.left, h ≫ Z.hom = t ∧ h ≫ n.left = x.left := by
  let i : overW W (Over.mk t) ⟶ T := Over.homMk (𝟙 T.left) ((Category.id_comp _).trans ht.symm)
  obtain ⟨h, h1, h2⟩ := univ (Over.mk t) (i ≫ x) (by rw [← MonObj.comp_pow, hx]; simp)
  refine ⟨h.left, ⟨Over.w h, (congrArg CommaMorphism.left h1).trans (Category.id_comp _)⟩, fun h' hh => ?_⟩
  exact congrArg CommaMorphism.left (h2 (Over.homMk h' hh.1)
    (Over.OverMorphism.ext (hh.2.trans (Category.id_comp _).symm)))

theorem exists_ext_local [IsCommMonObj G] [IsSeparated G.hom] (hG : TorsFiniteFlat G W k) (N : Over W.toScheme)
    (hN : FinFlatEt N) (hs : Surjective N.hom) (u : genPart (overW W N) ⟶ G) (d : overW W (N ⊗ N) ⟶ G)
    (hu : u ^ k = 1) (hd : d ^ k = 1)
    (H : ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
      (a b : TF (R := R) F ⟶ genPart (overW W N)) (c : TF (R := R) F ⟶ overW W (N ⊗ N)),
      c ≫ (Over.map W.ι).map (fst N N) = a ≫ genι _ → c ≫ (Over.map W.ι).map (snd N N) = b ≫ genι _ →
      a ≫ u = (b ≫ u) * (c ≫ d))
    (S : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra R S]
    [Algebra S (FractionRing R)] [IsScalarTower R S (FractionRing R)] [IsFractionRing S (FractionRing R)]
    (j : Sp S ⟶ W.toScheme) (hj : j ≫ W.ι = spMap (algebraMap R S)) :
    ∃ (T : Scheme.{0}) (g : T ⟶ N.left) (q : T ⟶ Sp S), IsPullback g q N.hom j ∧
      ∃ (e : (genPart (overW W N)).left ⟶ T) (v : T ⟶ G.left), e ≫ g = (genι _).left ∧
        v ≫ G.hom = g ≫ (overW W N).hom ∧ e ≫ v = u.left := by
  obtain ⟨Z, n, hZ, -, hn, univ⟩ := hG
  obtain ⟨hN1, hN2, hN3⟩ := hN
  obtain ⟨B, _, _, g, hg⟩ := exists_chart N.hom S j
  obtain ⟨C, _, _, z, hz⟩ := exists_chart Z.hom S j
  let K := FractionRing R
  let σ : Sp S ⟶ Sp R := j ≫ W.ι
  have : Module.Finite S B := RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1
    (MorphismProperty.of_isPullback (P := @IsFinite) hg hN1))
  have : Module.Finite S C := RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1
    (MorphismProperty.of_isPullback (P := @IsFinite) hz hZ))
  have : Module.Flat S B := RingHom.flat_algebraMap_iff.1 (Flat.SpecMap_iff.1
    (MorphismProperty.of_isPullback (P := @Flat) hg hN2))
  have : Module.FinitePresentation S B := Module.finitePresentation_of_finite S B
  have : Module.Projective S B := Module.Flat.projective_of_finitePresentation
  have hK : spMap (algebraMap S K) ≫ σ = jK R := by
    simp only [σ]
    rw [hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hA0 := (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct S K B)).flip.paste_horiz hg
  have hA1 : IsPullback (spMap (algebraMap S K) ≫ j) (𝟙 _) W.ι (jK R) :=
    IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp, Category.assoc]; exact hK⟩
  have hA : IsPullback (spMap (Algebra.TensorProduct.includeRight : B →ₐ[S] K ⊗[S] B).toRingHom ≫ g)
      (spMap (algebraMap K (K ⊗[S] B))) (overW W N).hom (jK R) := by
    have := hA0.paste_vert hA1
    rw [Category.comp_id] at this
    exact this
  have : Algebra.Etale K (K ⊗[S] B) := by
    rw [← RingHom.etale_algebraMap]
    refine (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom (algebraMap K (K ⊗[S] B)))).1 ?_
    change Etale (spMap (algebraMap K (K ⊗[S] B)))
    rw [← hA.isoPullback_hom_snd]
    infer_instance
  have : Nontrivial (K ⊗[S] B) := by
    obtain ⟨y, -⟩ := (MorphismProperty.of_isPullback (P := @Surjective) hA0 hs).surj (IsLocalRing.closedPoint K)
    exact PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨y⟩
  let gO : spO σ B ⟶ overW W N := Over.homMk g (by
    change g ≫ N.hom ≫ W.ι = _ ≫ j ≫ W.ι
    rw [← Category.assoc, hg.w, Category.assoc])
  let zO : spO σ C ⟶ overW W Z := Over.homMk z (by
    change z ≫ Z.hom ≫ W.ι = _ ≫ j ≫ W.ι
    rw [← Category.assoc, hz.w, Category.assoc])
  let EO : spO σ (K ⊗[S] B) ⟶ genPart (overW W N) := Over.homMk hA.isoPullback.hom (by
    change hA.isoPullback.hom ≫ pullback.fst _ _ ≫ _ = _
    rw [← Category.assoc, hA.isoPullback_hom_fst]
    exact Over.w (spH σ (Algebra.TensorProduct.includeRight : B →ₐ[S] K ⊗[S] B) ≫ gO))
  have hEO : EO ≫ genι _ = spH σ Algebra.TensorProduct.includeRight ≫ gO :=
    Over.OverMorphism.ext hA.isoPullback_hom_fst
  let hB : ∀ φ : B →ₐ[S] B ⊗[S] B, Over.mk (spMap (algebraMap S (B ⊗[S] B)) ≫ j) ⟶ N := fun φ =>
    Over.homMk (spH σ φ ≫ gO).left (by
      rw [← cancel_mono W.ι, Category.assoc]
      exact (Over.w (spH σ φ ≫ gO)).trans (Category.assoc _ _ _).symm)
  let l := lift (hB Algebra.TensorProduct.includeLeft) (hB Algebra.TensorProduct.includeRight)
  let lO : spO σ (B ⊗[S] B) ⟶ overW W (N ⊗ N) := Over.homMk l.left (by
    change l.left ≫ (N ⊗ N).hom ≫ W.ι = _ ≫ j ≫ W.ι
    rw [← Category.assoc, Over.w l]
    exact Category.assoc _ _ _)
  have hl1 : lO ≫ (Over.map W.ι).map (fst N N) = spH σ Algebra.TensorProduct.includeLeft ≫ gO :=
    Over.OverMorphism.ext (congrArg CommaMorphism.left (lift_fst (hB Algebra.TensorProduct.includeLeft)
      (hB Algebra.TensorProduct.includeRight)) :)
  have hl2 : lO ≫ (Over.map W.ι).map (snd N N) = spH σ Algebra.TensorProduct.includeRight ≫ gO :=
    Over.OverMorphism.ext (congrArg CommaMorphism.left (lift_snd (hB Algebra.TensorProduct.includeLeft)
      (hB Algebra.TensorProduct.includeRight)) :)
  obtain ⟨v, hv⟩ := exists_ext_affine σ K B C G k (zO ≫ n) (by rw [← MonObj.comp_pow, hn]; simp)
    (fun A _ _ x hx => by
      obtain ⟨h, ⟨h1, h2⟩, h3⟩ := tors_univ univ _ (spMap (algebraMap S A) ≫ j) (Category.assoc _ _ _) x hx
      obtain ⟨φ, hφ⟩ := Spec.map_surjective (hz.lift h _ h1)
      have e1 : Spec.map φ ≫ z = h := by rw [hφ, hz.lift_fst]
      have e2 : Spec.map φ ≫ spMap (algebraMap S C) = spMap (algebraMap S A) := by rw [hφ, hz.lift_snd]
      rw [← Spec.map_comp] at e2
      have e3 := congrArg CommRingCat.Hom.hom (Spec.map_injective e2)
      let φ' : C →ₐ[S] A := ⟨φ.hom, fun s => DFunLike.congr_fun e3 s⟩
      refine ⟨φ', Over.OverMorphism.ext ?_, fun ψ hψ => ?_⟩
      · change Spec.map φ ≫ z ≫ n.left = x.left
        rw [← Category.assoc, e1, h2]
      · have w1 : spMap ψ.toRingHom ≫ spMap (algebraMap S C) = spMap (algebraMap S A) := by
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 2
          exact ψ.comp_algebraMap
        have e4 : spMap ψ.toRingHom ≫ z = h := h3 _ ⟨by
          rw [Category.assoc, hz.w, ← Category.assoc, w1], by
          rw [Category.assoc]; exact congrArg CommaMorphism.left hψ⟩
        have e5 : spMap ψ.toRingHom = Spec.map φ := hz.hom_ext (by rw [e4, e1]) (by
          rw [w1, ← Spec.map_comp, e2])
        have e6 := congrArg CommRingCat.Hom.hom (Spec.map_injective e5)
        exact AlgHom.ext fun c => DFunLike.congr_fun e6 c)
    (EO ≫ u) (lO ≫ d) (by rw [← MonObj.comp_pow, hu]; simp) (by rw [← MonObj.comp_pow, hd]; simp)
    (fun F _ _ _ _ _ a b => by
      let i : spO σ F ⟶ TF (R := R) F := Over.homMk (𝟙 _) (by
        change 𝟙 _ ≫ spMap (algebraMap K F) ≫ jK R = spMap (algebraMap S F) ≫ σ
        rw [Category.id_comp, ← hK, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          ← IsScalarTower.algebraMap_eq])
      let i' : TF (R := R) F ⟶ spO σ F := Over.homMk (𝟙 _) (by
        have := Over.w i
        exact (Category.id_comp _).trans (this.symm.trans (Category.id_comp _)))
      have hi : i ≫ i' = 𝟙 _ := Over.OverMorphism.ext (Category.id_comp _)
      have h := H F (i' ≫ spH σ a ≫ EO) (i' ≫ spH σ b ≫ EO)
        (i' ≫ spH σ (Algebra.TensorProduct.productMap (a.comp Algebra.TensorProduct.includeRight)
          (b.comp Algebra.TensorProduct.includeRight)) ≫ lO)
        (by simp only [Category.assoc, hl1, hEO]
            simp only [← Category.assoc (spH σ _), ← spH_comp, Algebra.TensorProduct.productMap_left])
        (by simp only [Category.assoc, hl2, hEO]
            simp only [← Category.assoc (spH σ _), ← spH_comp, Algebra.TensorProduct.productMap_right])
      have h' := congrArg (i ≫ ·) h
      simp only [MonObj.comp_mul, Category.assoc, reassoc_of% hi] at h'
      exact h')
  refine ⟨_, g, _, hg, hA.isoPullback.inv ≫ (spH σ Algebra.TensorProduct.includeRight).left, v.left, ?_, ?_, ?_⟩
  · rw [Category.assoc, Iso.inv_comp_eq]
    exact (congrArg CommaMorphism.left hEO).symm
  · exact (Over.w v).trans (Over.w gO).symm
  · rw [Category.assoc, Iso.inv_comp_eq]
    exact congrArg CommaMorphism.left hv

end Global

end GlobalTheory.FlatTors.TorsExt

namespace GlobalTheory.FlatTors

open TorsExt

theorem exists_tors_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (W : (Sp R).Opens) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (k : ℕ), IsSeparated G.hom → TorsFiniteFlat G W k → ∀ N : Over W.toScheme, FinFlatEt N → Surjective N.hom → ∀ (u : genPart (overW W N) ⟶ G) (d : overW W (N ⊗ N) ⟶ G), u ^ k = 1 → d ^ k = 1 → (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (a b : TF (R := R) F ⟶ genPart (overW W N)) (c : TF (R := R) F ⟶ overW W (N ⊗ N)), c ≫ (Over.map W.ι).map (fst N N) = a ≫ genι _ → c ≫ (Over.map W.ι).map (snd N N) = b ≫ genι _ → a ≫ u = (b ≫ u) * (c ≫ d)) → ∃ v : overW W N ⟶ G, v ^ k = 1 ∧ genι _ ≫ v = u := by
  intro R _ _ _ _ W G _ _ k hsep hG N hN hs u d hu hd H
  have loc : ∀ x : N.left, ∃ (T : Scheme.{0}) (g : T ⟶ N.left), IsOpenImmersion g ∧ (∃ y, g y = x) ∧
      ∃ (e : (genPart (overW W N)).left ⟶ T) (v : T ⟶ G.left), e ≫ g = (genι _).left ∧
        v ≫ G.hom = g ≫ (overW W N).hom ∧ e ≫ v = u.left := by
    intro x
    let p : PrimeSpectrum R := W.ι (N.hom x)
    have hp : p ∈ W := (N.hom x).2
    obtain ⟨_, ⟨f, rfl⟩, hpf, hfW⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp W.isOpen
    have hf : f ≠ 0 := by
      rintro rfl
      exact hpf p.asIdeal.zero_mem
    have hle : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf
    let S := Localization.Away f
    have : IsDomain S := IsLocalization.isDomain_localization hle
    have : IsIntegrallyClosed S := isIntegrallyClosed_of_isLocalization S _ hle
    have : IsNoetherianRing S := IsLocalization.isNoetherianRing (Submonoid.powers f) S inferInstance
    letI : Algebra S (FractionRing R) := IsLocalization.localizationAlgebraOfSubmonoidLe S (FractionRing R) _ _ hle
    have : IsScalarTower R S (FractionRing R) :=
      IsLocalization.localization_isScalarTower_of_submonoid_le S (FractionRing R) _ _ hle
    have : IsFractionRing S (FractionRing R) :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) S (FractionRing R)
    have hop : IsOpenImmersion (spMap (algebraMap R S)) := IsOpenImmersion.of_isLocalization f
    have hr : Set.range (spMap (algebraMap R S)) = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
      PrimeSpectrum.localization_away_comap_range S f
    let j : Sp S ⟶ W.toScheme := IsOpenImmersion.lift W.ι (spMap (algebraMap R S)) (by
      rw [hr, Scheme.Opens.range_ι]; exact hfW)
    have hj : j ≫ W.ι = spMap (algebraMap R S) := IsOpenImmersion.lift_fac _ _ _
    have hjo : IsOpenImmersion j := by
      have : IsOpenImmersion (j ≫ W.ι) := by rw [hj]; exact hop
      exact IsOpenImmersion.of_comp j W.ι
    obtain ⟨T, g, q, hg, h⟩ := exists_ext_local hG N hN hs u d hu hd H S j hj
    refine ⟨T, g, MorphismProperty.of_isPullback (P := @IsOpenImmersion) hg.flip hjo, ?_, h⟩
    obtain ⟨s, hs⟩ : p ∈ Set.range (spMap (algebraMap R S)) := by rw [hr]; exact hpf
    have hs' : N.hom x = j s := W.ι.injective (by rw [← Scheme.Hom.comp_apply j, hj]; exact hs.symm)
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback hg x s hs'
    exact ⟨y, hy⟩
  choose T g hg hy e v he hv hu' using loc
  have hfl : Flat (overW W N).hom := by
    have := hN.2.1
    change Flat (N.hom ≫ W.ι)
    infer_instance
  have hj : IsSchemeTheoreticallyDominant (jK R) := schDom_spec_map _ (IsFractionRing.injective R _)
  have hdom : IsSchemeTheoreticallyDominant (genι (overW W N)).left :=
    inferInstanceAs (IsSchemeTheoreticallyDominant (pullback.fst (overW W N).hom (jK R)))
  have hqc : QuasiCompact (genι (overW W N)).left :=
    inferInstanceAs (QuasiCompact (pullback.fst (overW W N).hom (jK R)))
  let 𝒰 : N.left.OpenCover := Scheme.Cover.mkOfCovers N.left T g (fun x => ⟨x, hy x⟩) hg
  have hc : ∀ x y, pullback.fst (g x) (g y) ≫ v x = pullback.snd (g x) (g y) ≫ v y := by
    intro x y
    let r : pullback (g x) (g y) ⟶ (overW W N).left := pullback.fst (g x) (g y) ≫ g x
    have : IsOpenImmersion r := inferInstanceAs (IsOpenImmersion (pullback.fst (g x) (g y) ≫ g x))
    refine ext_of_schDom G.hom ?_ (pullback.fst r (genι (overW W N)).left) ?_
    · rw [Category.assoc, Category.assoc, hv, hv, ← Category.assoc, pullback.condition, Category.assoc]
    · have h1 : pullback.fst r (genι (overW W N)).left ≫ pullback.fst (g x) (g y) =
          pullback.snd r (genι (overW W N)).left ≫ e x := by
        rw [← cancel_mono (g x), Category.assoc, Category.assoc, he]
        exact pullback.condition
      have h2 : pullback.fst r (genι (overW W N)).left ≫ pullback.snd (g x) (g y) =
          pullback.snd r (genι (overW W N)).left ≫ e y := by
        rw [← cancel_mono (g y), Category.assoc, Category.assoc, he, ← pullback.condition]
        exact pullback.condition
      rw [← Category.assoc, h1, ← Category.assoc, h2, Category.assoc, Category.assoc, hu', hu']
  let v₀ : N.left ⟶ G.left := 𝒰.glueMorphisms v hc
  have hv₀ : ∀ x, g x ≫ v₀ = v x := fun x => 𝒰.ι_glueMorphisms v hc x
  have hov : v₀ ≫ G.hom = (overW W N).hom := 𝒰.hom_ext _ _ fun x => by
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G.hom) (hv₀ x)).trans (hv x))
  let V : overW W N ⟶ G := Over.homMk v₀ hov
  have hV : genι _ ≫ V = u := by
    ext1
    change (genι (overW W N)).left ≫ v₀ = u.left
    by_cases hne : Nonempty N.left
    · obtain ⟨x⟩ := hne
      rw [← he x, Category.assoc, hv₀, hu']
    · have : IsEmpty (genPart (overW W N)).left := ⟨fun y => hne ⟨(genι (overW W N)).left y⟩⟩
      exact (isInitialOfIsEmpty).hom_ext _ _
  refine ⟨V, ?_, hV⟩
  ext1
  refine ext_of_schDom G.hom (by rw [Over.w, Over.w]) (genι (overW W N)).left ?_
  have : genι _ ≫ V ^ k = genι _ ≫ 1 := by
    rw [MonObj.comp_pow, hV, hu]
    simp
  exact congrArg CommaMorphism.left this

end GlobalTheory.FlatTors
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_descent_finite_etale_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (W : (Sp R).Opens) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (k : ℕ), IsSeparated G.hom → TorsFiniteFlat G W k → ∀ N : Over W.toScheme, FinFlatEt N → Surjective N.hom → ∀ (u : genPart (overW W N) ⟶ G) (d : overW W (N ⊗ N) ⟶ G), u ^ k = 1 → d ^ k = 1 → (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (a b : TF (R := R) F ⟶ genPart (overW W N)) (c : TF (R := R) F ⟶ overW W (N ⊗ N)), c ≫ (Over.map W.ι).map (fst N N) = a ≫ genι _ → c ≫ (Over.map W.ι).map (snd N N) = b ≫ genι _ → a ≫ u = (b ≫ u) * (c ≫ d)) → ∃ v : overW W N ⟶ G, v ^ k = 1 ∧ genι _ ≫ v = u := by
  atlas_forward_decl GlobalTheory.FlatTors.exists_tors_ext
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsMono

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct
open GlobalTheory.TorusModel GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.TorsionFormCompare

theorem hom_ext_of_isFinite {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (T : Over (Sp R))
    [IsFinite T.hom] {X : Scheme.{0}} [IsAffine X] {f g : T.left ⟶ X}
    (h : ∀ e, thickι (maximalIdeal R) e T ≫ f = thickι (maximalIdeal R) e T ≫ g) : f = g := by
  have : IsAffine T.left := isAffine_of_isAffineHom T.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (T.left.isoSpec.inv ≫ T.hom)
  have hf : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at hf
  letI : Algebra R Γ(T.left, ⊤) := φ.hom.toAlgebra
  have : Module.Finite R Γ(T.left, ⊤) := hf
  obtain ⟨a, ha⟩ := Spec.map_surjective (T.left.isoSpec.inv ≫ f ≫ X.isoSpec.hom)
  obtain ⟨b, hb⟩ := Spec.map_surjective (T.left.isoSpec.inv ≫ g ≫ X.isoSpec.hom)
  suffices a = b by
    rw [this, hb, cancel_epi, cancel_mono] at ha
    exact ha.symm
  ext s
  rw [← sub_eq_zero, ← Submodule.mem_bot R, ← Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := Γ(T.left, ⊤))
    (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top, Submodule.mem_iInf]
  intro e
  let J : Ideal Γ(T.left, ⊤) := (maximalIdeal R ^ (e + 1)).map φ.hom
  let q : Γ(T.left, ⊤) ⟶ CommRingCat.of (Γ(T.left, ⊤) ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  let σ : CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)) ⟶ CommRingCat.of (Γ(T.left, ⊤) ⧸ J) :=
    CommRingCat.ofHom (Ideal.quotientMap J φ.hom Ideal.le_comap_map)
  have w : (Spec.map q ≫ T.left.isoSpec.inv) ≫ T.hom = Spec.map σ ≫ thick R (maximalIdeal R) e := by
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    exact (congrArg Spec.map (by ext x; rfl)).trans (Spec.map_comp _ _)
  have hl : pullback.lift _ _ w ≫ thickι (maximalIdeal R) e T = Spec.map q ≫ T.left.isoSpec.inv :=
    pullback.lift_fst _ _ _
  have e₁ : a ≫ q = b ≫ q := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, ha, hb, ← reassoc_of% hl, ← reassoc_of% hl, reassoc_of% h e]
  have e₂ : a.hom s - b.hom s ∈ J := Ideal.Quotient.eq.1 (congrArg (fun u => u.hom s) e₁)
  refine Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ e)) ?_
  rw [Ideal.smul_top_eq_map]
  exact e₂

theorem mono_torsion : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N) (x₀ : N ⟶ t.G), IsFinite N.hom → GtTors k g₀ → (∀ (T : Over (Sp R)) (g : GtPt P.D.toPre T), GtTors k g → ∃! h : T ⟶ N, GtPt.IsPull h.left g₀ g) → FormalEq P.U.toUnifPre x₀ g₀ → Mono x₀ := by
  intro E _ _ _ H R _ _ _ _ hR t P W _ _ ψW k _ N g₀ x₀ hN hg hu hF
  have := hR.1
  obtain ⟨Gt, _, _, Φ, hΦ, -⟩ := exists_represents P.D.toPre
  obtain ⟨c₀, rfl⟩ := (Φ N).surjective g₀
  have hc₀ := (tors_iff hΦ k c₀).1 hg
  have hp := (formalEq_iff _ _ _).1 hF
  have univ : ∀ {T} (x : T ⟶ Gt), x ^ k = 1 → ∃! h : T ⟶ N, h ≫ c₀ = x := fun {T} x hx =>
    (existsUnique_congr fun h => isPull_iff_comp hΦ h c₀ x).1 (hu T _ ((tors_iff hΦ k x).2 hx))
  have tz : ∀ {T} (h : T ⟶ N), (h ≫ c₀) ^ k = 1 := fun h => by rw [← MonObj.comp_pow, hc₀, MonObj.comp_one]
  have canc : ∀ {T} {h h' : T ⟶ N}, h ≫ c₀ = h' ≫ c₀ → h = h' := fun {T h h'} e => (univ _ (tz h')).unique e rfl
  have pt : ∀ {T} (h : T ⟶ N), IsPointOf P.U.toUnifPre (Φ T (h ≫ c₀)) (h ≫ x₀) := fun h => hp.pull h (hΦ.1 _ _ h c₀)
  have : IsAffine N.left := isAffine_of_isAffineHom N.hom
  have : IsSeparated t.G.hom := t.semi.separated
  have : IsFinite x₀.left := by
    have : IsFinite (x₀.left ≫ t.G.hom) := by rw [Over.w]; exact hN
    exact IsFinite.of_comp _ t.G.hom
  let Q : Over (Sp R) := Over.mk (pullback.fst x₀.left x₀.left ≫ N.hom)
  have : IsFinite Q.hom := inferInstanceAs (IsFinite (pullback.fst x₀.left x₀.left ≫ N.hom))
  let p₁ : Q ⟶ N := Over.homMk (pullback.fst x₀.left x₀.left) rfl
  let p₂ : Q ⟶ N := Over.homMk (pullback.snd x₀.left x₀.left) (by
    show _ = pullback.fst x₀.left x₀.left ≫ N.hom
    rw [← Over.w x₀, pullback.condition_assoc])
  have hx : p₁ ≫ x₀ = p₂ ≫ x₀ := Over.OverMorphism.ext pullback.condition
  have key : p₁.left = p₂.left := hom_ext_of_isFinite Q fun e => by
    have pl : ∀ w : Q ⟶ N, HasCoords P.U.toUnifPre e (Φ _ (fstG (maximalIdeal R) e Q ≫ w ≫ c₀)) (𝟙 _)
        (thickHom (maximalIdeal R) e (w ≫ x₀)) := fun w => by
      rw [← hasCoords_pull (hΦ.1 _ _ (fstG (maximalIdeal R) e Q) (w ≫ c₀)), Category.id_comp]
      exact (isPointOf_iff_thick _ _ _).1 (pt w) e
    have e₁ := (Φ _).injective (eq_of_hasCoords (pl p₁) (hx ▸ pl p₂))
    rw [← Category.assoc, ← Category.assoc] at e₁
    exact congrArg (·.left) (canc e₁)
  have key' : pullback.fst x₀.left x₀.left = pullback.snd x₀.left x₀.left := key
  refine ⟨fun h h' e => Over.OverMorphism.ext ?_⟩
  have e' : h.left ≫ x₀.left = h'.left ≫ x₀.left := congrArg (·.left) e
  rw [← pullback.lift_fst _ _ e', key', pullback.lift_snd]

end GlobalTheory.TorsMono
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_part_image_generic : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N) (x₀ : N ⟶ t.G), IsFinitePart P.U.toUnifPre k N g₀ x₀ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : Sp F ⟶ N.left), OverGen F N x → ∀ q : QkPt P.D.toPre F k, q.y = 0 → GtPt.IsPullF F x g₀ q.g → IsImage P F k q (x ≫ x₀.left) := by
  first | exact @GlobalTheory.FinitePartGeneric.main | exact GlobalTheory.FinitePartGeneric.main | (intros; apply GlobalTheory.FinitePartGeneric.main <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_part_image_pullback : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ y N p₀, PairRep ψW k y N p₀ → ∃ u : genPart (overW W N) ⟶ t.G, u ^ k = 1 ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : Sp F ⟶ (genPart (overW W N)).left), OverGen F (genPart (overW W N)) x → ∀ q : QkPt P.D.toPre F k, QkPtW.IsPullF F (x ≫ (genι (overW W N)).left) p₀ q → IsImage P F k q (x ≫ u.left) := by
  first | exact @GlobalTheory.GenTorsMap.exists_genericMap | exact GlobalTheory.GenTorsMap.exists_genericMap | (intros; apply GlobalTheory.GenTorsMap.exists_genericMap <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.TorsOverOpen

open GlobalTheory.TorsionRepresent GlobalTheory.IndefiniteRowSideFullHecke.FlatTorsionIsomorphism

section

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] (k : ℕ)

theorem isPullback_incl :
    IsPullback (incl G k).left (torsScheme G k).hom ((𝟙 G : G ⟶ G) ^ k).left η[G].left := by
  have h := (IsPullback.of_hasPullback ((𝟙 G : G ⟶ G) ^ k) (η : 𝟙_ (Over S) ⟶ G)).map (Over.forget S)
  have e : (pullback.snd ((𝟙 G : G ⟶ G) ^ k) (η : 𝟙_ (Over S) ⟶ G)).left = (torsScheme G k).hom :=
    (Category.comp_id _).symm.trans (Over.w (pullback.snd ((𝟙 G : G ⟶ G) ^ k) (η : 𝟙_ (Over S) ⟶ G)))
  exact e ▸ h

theorem pullback_map_pow :
    (Over.pullback f).map ((𝟙 G : G ⟶ G) ^ k) = (𝟙 ((Over.pullback f).obj G)) ^ k := by
  rw [← (Over.pullback f).map_id]
  exact map_pow (Over.pullback f).homMonoidHom _ _

theorem prop_snd (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange]
    (h : P ((𝟙 ((Over.pullback f).obj G)) ^ k : (Over.pullback f).obj G ⟶ _).left) :
    P (pullback.snd (torsScheme G k).hom f) := by
  rw [← pullback_map_pow] at h
  have hη : η[G].left ≫ G.hom = 𝟙 S := Over.w η[G]
  have hι : (incl G k).left ≫ G.hom = (torsScheme G k).hom := Over.w _
  have hm : ((𝟙 G : G ⟶ G) ^ k).left ≫ G.hom = G.hom := Over.w _
  let s : S' ⟶ pullback G.hom f := pullback.lift (f ≫ η[G].left) (𝟙 _) (by
    rw [Category.assoc, hη]; simp)
  let a : pullback (torsScheme G k).hom f ⟶ pullback G.hom f :=
    pullback.lift (pullback.fst _ _ ≫ (incl G k).left) (pullback.snd _ _) (by
      rw [Category.assoc, hι, pullback.condition])
  let m : pullback G.hom f ⟶ pullback G.hom f := ((Over.pullback f).map ((𝟙 G : G ⟶ G) ^ k)).left
  have m1 : m ≫ pullback.fst G.hom f = pullback.fst G.hom f ≫ ((𝟙 G : G ⟶ G) ^ k).left := pullback.lift_fst _ _ _
  have m2 : m ≫ pullback.snd G.hom f = pullback.snd G.hom f := pullback.lift_snd _ _ _
  have a1 : a ≫ pullback.fst G.hom f = pullback.fst _ _ ≫ (incl G k).left := pullback.lift_fst _ _ _
  have a2 : a ≫ pullback.snd G.hom f = pullback.snd _ _ := pullback.lift_snd _ _ _
  have s1 : s ≫ pullback.fst G.hom f = f ≫ η[G].left := pullback.lift_fst _ _ _
  have s2 : s ≫ pullback.snd G.hom f = 𝟙 _ := pullback.lift_snd _ _ _
  have hr : IsPullback (pullback.fst G.hom f) m ((𝟙 G : G ⟶ G) ^ k).left (pullback.fst G.hom f) := by
    refine IsPullback.of_bot ?_ m1.symm (IsPullback.of_hasPullback G.hom f)
    rw [hm, m2]
    exact IsPullback.of_hasPullback G.hom f
  have ho := (IsPullback.of_hasPullback (torsScheme G k).hom f).paste_horiz (isPullback_incl G k)
  have hl : IsPullback a (pullback.snd (torsScheme G k).hom f) m s := by
    refine IsPullback.of_right ?_ ?_ hr
    · rw [a1, s1]
      exact ho
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, m1, s1, ← Category.assoc, a1]
        exact ho.w
      · rw [Category.assoc, Category.assoc, m2, s2, a2, Category.comp_id]
  exact MorphismProperty.of_isPullback hl h

noncomputable def toTors : (Over.map f).obj ((Over.pullback f).obj (torsScheme G k)) ⟶ torsScheme G k :=
  Over.homMk (pullback.fst (torsScheme G k).hom f) pullback.condition

theorem univ (T : Over S') (x : (Over.map f).obj T ⟶ G) (hx : x ^ k = 1) :
    ∃! h : T ⟶ (Over.pullback f).obj (torsScheme G k), (Over.map f).map h ≫ toTors f G k ≫ incl G k = x := by
  obtain ⟨l, hl⟩ := exists_lift G k x hx
  have hw : l.left ≫ (torsScheme G k).hom = T.hom ≫ f := Over.w l
  refine ⟨Over.homMk (pullback.lift l.left T.hom hw) (pullback.lift_snd _ _ _), ?_, ?_⟩
  · beta_reduce
    rw [← hl, ← Category.assoc]
    congr 1
    ext1
    exact pullback.lift_fst _ _ _
  · intro h hh
    rw [← hl, ← Category.assoc, cancel_mono] at hh
    ext1
    apply pullback.hom_ext
    · exact (congrArg CommaMorphism.left hh).trans (pullback.lift_fst _ _ _).symm
    · exact (Over.w h).trans (pullback.lift_snd _ _ _).symm

end

theorem isAbelianScheme_restrict {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (W : S.Opens)
    (hp : IsProper (G.hom ∣_ W)) : IsAbelianScheme ((Over.pullback W.ι).obj G) := by
  have := hG.comm
  have := hG.smooth
  have := hG.geomConnected
  have hr := isPullback_morphismRestrict G.hom W
  refine ⟨inferInstance, inferInstanceAs (Smooth (pullback.snd G.hom W.ι)), ?_,
    inferInstanceAs (GeometricallyConnected (pullback.snd G.hom W.ι))⟩
  change IsProper (pullback.snd G.hom W.ι)
  rw [← hr.flip.isoPullback_inv_snd]
  infer_instance

theorem torsion_finFlatEt : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => IsAbelianScheme ((Over.pullback W.ι).obj t.G) ∧ TorsFiniteFlat t.G W k ∧ ∃ (Z : Over W.toScheme) (n : overW W Z ⟶ t.G), FinFlatEt Z ∧ n ^ k = 1 ∧ ∀ (T : Over W.toScheme) (x : overW W T ⟶ t.G), x ^ k = 1 → ∃! h : T ⟶ Z, (Over.map W.ι).map h ≫ n = x := by
  intro E _ _ _ H R _ _ _ _ hR t P W _ hp ψW k hk
  have hA := isAbelianScheme_restrict t.G t.semi W hp
  have : IsNoetherianRing R := hR.1
  have : IsNoetherianRing (CommRingCat.of R) := hR.1
  have : IsLocallyNoetherian W.toScheme := isLocallyNoetherian_of_isOpenImmersion W.ι
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.isFinite_and_flat_mul_abelianScheme _ _ hA k hk
  have hfin := prop_snd W.ι t.G k @IsFinite h₁
  have hflat := prop_snd W.ι t.G k @Flat h₂
  have hs := t.semi.smooth
  have hsK : Smooth ((Over.pullback (jK R)).obj t.G).hom := inferInstanceAs (Smooth (pullback.snd t.G.hom (jK R)))
  have hu : IsUnit (k : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)) := by
    have : IsUnit (k : FractionRing R) := (Nat.cast_ne_zero.2 (by omega) : (k : FractionRing R) ≠ 0).isUnit
    simpa using this.map (Scheme.ΓSpecIso (.of (FractionRing R))).inv.hom
  have het : Etale (pullback.snd (torsScheme t.G k).hom (jK R)) :=
    prop_snd (jK R) t.G k @Etale (GlobalTheory.GrpTangent.etale_id_pow _ hu)
  have hn : (toTors W.ι t.G k ≫ incl t.G k) ^ k = 1 := comp_incl_pow t.G k _
  refine ⟨hA, ⟨_, _, hfin, hflat, hn, univ W.ι t.G k⟩, _, _, ⟨hfin, hflat, ?_⟩, hn, univ W.ι t.G k⟩
  have ho : IsOpenImmersion ((Over.pullback (jK R)).map (toTors W.ι t.G k)).left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) _ _
      (inferInstanceAs (IsOpenImmersion (pullback.fst (torsScheme t.G k).hom W.ι)))
  have e : ((Over.pullback (jK R)).map (toTors W.ι t.G k)).left ≫ pullback.snd (torsScheme t.G k).hom (jK R) =
      pullback.snd (overW W ((Over.pullback W.ι).obj (torsScheme t.G k))).hom (jK R) :=
    Over.w ((Over.pullback (jK R)).map (toTors W.ι t.G k))
  rw [← e]
  infer_instance

end GlobalTheory.TorsOverOpen
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_representable_finite_etale : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => IsAbelianScheme ((Over.pullback W.ι).obj t.G) ∧ TorsFiniteFlat t.G W k ∧ ∃ (Z : Over W.toScheme) (n : overW W Z ⟶ t.G), FinFlatEt Z ∧ n ^ k = 1 ∧ ∀ (T : Over W.toScheme) (x : overW W T ⟶ t.G), x ^ k = 1 → ∃! h : T ⟶ Z, (Over.map W.ι).map h ≫ n = x := by
  atlas_forward_decl GlobalTheory.TorsOverOpen.torsion_finFlatEt
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsRepMap

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorsionFormCompare GlobalTheory.TorusModel GlobalTheory.FieldRestrictionTest

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem isIota_zero {F : Type} [Field F] [Algebra (FractionRing R) F] (hB : D.TauBimult) {h : GtPtF D F}
    (hh : h.IsZero) : GtPtF.IsIota 0 h := by
  obtain ⟨hb, hv⟩ := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isZero_iff h).1 hh
  refine (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isIota_iff 0 h).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  have t := tau_mul (𝟙 (TF (R := R) F)) hJ hB 0 0 χ
  rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
  exact (hv χ y J hJ).trans (mul_eq_left.1 t.symm).symm

variable {Gt : Over (Sp R)} [GrpObj Gt] {Φ : ∀ T, (T ⟶ Gt) ≃ GtPt D T}

theorem nsmul_eq (hΦ : Represents Φ) (k : ℕ) {T : Over (Sp R)} (x : T ⟶ Gt) {h : GtPt D T}
    (H : GtPt.IsNsmul k (Φ T x) h) : h = Φ T (x ^ k) := by
  obtain ⟨u, u0, us, rfl⟩ := H
  have : ∀ i : Fin (k + 1), u i = Φ T (x ^ (i : ℕ)) := fun i => by
    induction i using Fin.induction with
    | zero => exact isZero_unique u0 (by simpa using isZero_one hΦ T)
    | succ i ih =>
      have h := us i
      rw [ih] at h
      rw [Fin.val_succ, pow_succ]
      exact isAdd_unique h (hΦ.2 T _ _)
  exact this (Fin.last k)

theorem iota_pull_eq {W : (Sp R).Opens} {ψW : PsiOn D W} {T T' : Over W.toScheme} (h₁ h₂ : T' ⟶ T) {y : D.X}
    {g : GtPt D (overW W T)} (hg : GtPt.IsIotaW ψW y g) {g₁ g₂ : GtPt D (overW W T')}
    (H₁ : GtPt.IsPull ((Over.map W.ι).map h₁).left g g₁) (H₂ : GtPt.IsPull ((Over.map W.ι).map h₂).left g g₂) :
    g₁ = g₂ := by
  have key : ∀ (h : T' ⟶ T) (g' : GtPt D (overW W T')), GtPt.IsPull ((Over.map W.ι).map h).left g g' →
      g'.b = DegPre.cT D _ y ∧ ∀ χ z J, Good D.P.L z J →
        val (g'.s χ) (𝟙 _) z J = val (ψW.tau y χ) T'.hom z J := fun h g' H => by
    refine ⟨?_, fun χ z J hJ => ?_⟩
    · have : g'.b = (Over.map W.ι).map h ≫ g.b := Over.OverMorphism.ext H.1
      rw [this, hg.1, DegPre.cT, comp_toUnit_assoc]
    · refine (val_corr hJ (H.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (hg.2 χ) _).trans
        ((val_pull hJ _ _ _).trans ?_)))
      rw [Category.id_comp]
      exact congrArg (fun m => val (ψW.tau y χ) m z J) (Over.w h)
  obtain ⟨a₁, b₁⟩ := key h₁ g₁ H₁
  obtain ⟨a₂, b₂⟩ := key h₂ g₂ H₂
  exact pt_ext (a₁.trans a₂.symm) fun χ z J hJ => (b₁ χ z J hJ).trans (b₂ χ z J hJ).symm

theorem isPullF_iff_eq (hΦ : Represents Φ) {F : Type} [Field F] [Algebra (FractionRing R) F] {T : Over (Sp R)}
    (σ : TF (R := R) F ⟶ T) (x : T ⟶ Gt) (g : GtPtF D F) :
    GtPt.IsPullF F σ.left (Φ T x) g ↔ toT g = Φ _ (σ ≫ x) :=
  ⟨fun H => isPull_unique (k := σ) H (hΦ.1 _ _ σ x), fun H => (isPullF_iff_isPull _ _ _).2 (H ▸ hΦ.1 _ _ σ x)⟩

end Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)}

theorem isImage_mul {P : PELUnif I t} (hP : P.TorsionIso) {F : Type} [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] {k : ℕ} (hk : 1 ≤ k) {q q' q'' : QkPt P.D.toPre F k} (hq : QkAdd q q' q'')
    {v v' v'' : TF (R := R) F ⟶ t.G} (h : IsImage P F k q v.left) (h' : IsImage P F k q' v'.left)
    (h'' : IsImage P F k q'' v''.left) : v'' = v * v' := by
  obtain ⟨f, f1, -, -, f4, -⟩ := hP F k hk
  obtain ⟨Ψ, hΨ⟩ := GlobalTheory.LevelRatio.exists_ptsEquiv P.U.toUnifPre F
  have key : ∀ {q : QkPt P.D.toPre F k} {v : TF (R := R) F ⟶ t.G}, IsImage P F k q v.left → v = Ψ (f q) := by
    rintro q v ⟨a, e, ha⟩
    obtain rfl := (f1 _ _).1 ha
    exact Over.OverMorphism.ext (e.symm.trans (hΨ _).symm)
  rw [key h, key h', key h'', f4 _ _ _ hq, map_mul]

theorem exists_repMap : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ y N p₀, PairRep ψW k y N p₀ → ∃ v : overW W N ⟶ t.G, v ^ k = 1 ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : Sp F ⟶ N.left), OverGen F (overW W N) x → ∀ q : QkPt P.D.toPre F k, QkPtW.IsPullF F x p₀ q → IsImage P F k q (x ≫ v.left) := by
  intro E _ _ _ H R _ _ _ _ hR t P W hW hp ψW k hk y N p₀ hN
  have := hR.1
  have := hR.2.2.1
  have hP := GlobalTheory.FlatTors.torsionIso_holds E H R _ hR t P
  obtain ⟨u, hu, hu'⟩ := GlobalTheory.T.generic_part_image_pullback E H R hR t P W hW hp ψW k hk y N p₀ hN
  obtain ⟨Z, g₀, x₀, z1, z2, -, z3, z4, z5, z6⟩ := GlobalTheory.FlatTors.exists_torsion_toG E H R hR t P W hW hp ψW k hk
  have hZ : IsFinitePart P.U.toUnifPre k Z g₀ x₀ :=
    ⟨z1, z2, z3, z4, z5, GlobalTheory.TorsMono.mono_torsion E H R hR t P W hW hp ψW k hk Z g₀ x₀ z1 z3 z4 z6,
      GlobalTheory.FiniteTorsLift.main E H R hR t P W hW hp ψW k hk Z g₀ x₀ z1 z3 z4 z6, z6⟩
  have hgen := GlobalTheory.T.finite_part_image_generic E H R hR t P W hW hp ψW k hk Z g₀ x₀ hZ
  obtain ⟨Gt, _, _, Φ, hΦ, -⟩ := exists_represents P.D.toPre
  obtain ⟨c₀, rfl⟩ := (Φ Z).surjective g₀
  have hc₀ := (tors_iff hΦ k c₀).1 z3
  obtain ⟨c, hc⟩ := (Φ (overW W N)).surjective p₀.g
  let n₁ : overW W (N ⊗ N) ⟶ overW W N := (Over.map W.ι).map (fst N N)
  let n₂ : overW W (N ⊗ N) ⟶ overW W N := (Over.map W.ι).map (snd N N)
  have hk₀ : GtPt.IsIotaW ψW p₀.y (Φ _ (c ^ k)) := by
    obtain ⟨h, h1, h2⟩ := p₀.eq
    rw [← hc] at h1
    rwa [nsmul_eq hΦ k c h1] at h2
  have hpow : n₁ ≫ c ^ k = n₂ ≫ c ^ k :=
    (Φ _).injective (iota_pull_eq (fst N N) (snd N N) hk₀ (hΦ.1 _ _ _ _) (hΦ.1 _ _ _ _))
  have hδ : ((n₂ ≫ c)⁻¹ * (n₁ ≫ c)) ^ k = 1 := by
    rw [mul_pow, inv_pow, ← MonObj.comp_pow, ← MonObj.comp_pow, hpow, inv_mul_cancel]
  obtain ⟨e, he, -⟩ := z4 _ _ ((tors_iff hΦ k _).2 hδ)
  have he' : e ≫ c₀ = (n₂ ≫ c)⁻¹ * (n₁ ≫ c) := (isPull_iff_comp hΦ _ _ _).1 he
  obtain ⟨v, hv, hv'⟩ := GlobalTheory.T.torsion_descent_finite_etale_cover R W t.G k t.semi.separated
    (GlobalTheory.T.torsion_representable_finite_etale E H R hR t P W hW hp ψW k hk).2.1 N hN.1 hN.2.1 u (e ≫ x₀) hu
    (by rw [← MonObj.comp_pow, z5, MonObj.comp_one]) (fun F _ _ _ a b s ha hb => by
      obtain ⟨qa, hqa, -⟩ := (existsUnique_pair_iff (F := F) (a ≫ genι (overW W N)).left p₀).2
        (Over.w (a ≫ genι (overW W N)))
      obtain ⟨qb, hqb, -⟩ := (existsUnique_pair_iff (F := F) (b ≫ genι (overW W N)).left p₀).2
        (Over.w (b ≫ genι (overW W N)))
      obtain ⟨g, hg⟩ := exists_isPullF (s ≫ e) (Φ Z c₀)
      obtain ⟨h, h1, h2⟩ := z3
      obtain ⟨h', hh⟩ := exists_isPullF (s ≫ e) h
      let qd : QkPt P.D.toPre F k := ⟨0, g, h', isNsmul_restrict hg hh h1,
        isIota_zero P.D.tau_bimult (isZero_restrict hh h2)⟩
      have ia : IsImage P F k qa (a ≫ u).left := hu' F a.left (Over.w a) qa hqa
      have ib : IsImage P F k qb (b ≫ u).left := hu' F b.left (Over.w b) qb hqb
      have id : IsImage P F k qd (s ≫ e ≫ x₀).left := by
        rw [← Category.assoc]
        exact hgen F (s ≫ e).left (Over.w _) qd rfl hg
      refine isImage_mul hP hk ⟨qa, ?_, ?_, qk_equiv_refl P.D.tau_bimult qa⟩ ib id ia
      · exact hqa.1.trans (hqb.1.symm.trans (add_zero _).symm)
      · have ea := hqa.2
        have eb := hqb.2
        rw [← hc] at ea eb
        rw [isPullF_iff_eq hΦ] at ea eb hg
        have add := hΦ.2 _ ((b ≫ genι (overW W N)) ≫ c) ((s ≫ e) ≫ c₀)
        have em : ((b ≫ genι (overW W N)) ≫ c) * ((s ≫ e) ≫ c₀) = (a ≫ genι (overW W N)) ≫ c := by
          rw [← ha, ← hb, Category.assoc, Category.assoc, Category.assoc, he', ← MonObj.comp_mul,
            mul_inv_cancel_left]
        rw [em, ← ea, ← eb, ← hg] at add
        exact add)
  refine ⟨v, hv, fun F _ _ _ x hx q hq => ?_⟩
  let x' : Sp F ⟶ (genPart (overW W N)).left := pullback.lift x (jFK (R := R) F) hx
  have e₁ : x' ≫ (genι (overW W N)).left = x := pullback.lift_fst _ _ _
  have := hu' F x' (by
    show x' ≫ (genι (overW W N)).left ≫ _ = _
    rw [← Category.assoc, e₁]
    exact hx) q (e₁.symm ▸ hq)
  rwa [← hv', Over.comp_left, ← Category.assoc, e₁] at this

end GlobalTheory.TorsRepMap
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_hom_image : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ y N p₀, PairRep ψW k y N p₀ → ∃ v : overW W N ⟶ t.G, v ^ k = 1 ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : Sp F ⟶ N.left), OverGen F (overW W N) x → ∀ q : QkPt P.D.toPre F k, QkPtW.IsPullF F x p₀ q → IsImage P F k q (x ≫ v.left) := by
  atlas_forward_decl GlobalTheory.TorsRepMap.exists_repMap
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.FlatTors.TorsMapExists

open ReciprocityTheory.ChartRestriction.G.DVR

theorem isPull_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' T'' : Over (Sp R)}
    {a : T'.left ⟶ T.left} {b : T''.left ⟶ T'.left} {g : GtPt D T} {g' : GtPt D T'} {g'' : GtPt D T''}
    (h : GtPt.IsPull a g g') (h' : GtPt.IsPull b g' g'') : GtPt.IsPull (b ≫ a) g g'' := by
  refine ⟨by rw [h'.1, h.1, Category.assoc], fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  rw [val_corr hJ (h'.2 χ), val_pull hJ, val_corr hJ (h.2 χ), val_pull hJ, val_pull hJ, Category.assoc]

theorem isPullF_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Sp R)}
    {F : Type} [Field F] [Algebra (FractionRing R) F]
    {a : T'.left ⟶ T.left} {b : Sp F ⟶ T'.left} {g : GtPt D T} {g' : GtPt D T'} {g'' : GtPtF D F}
    (h : GtPt.IsPull a g g') (h' : GtPt.IsPullF F b g' g'') : GtPt.IsPullF F (b ≫ a) g g'' :=
  isPull_trans (T'' := TF (R := R) F) (g'' := ⟨g''.b, g''.s, g''.isGen, g''.s_zero, g''.mult⟩) h h'




end GlobalTheory.FlatTors.TorsMapExists
end
