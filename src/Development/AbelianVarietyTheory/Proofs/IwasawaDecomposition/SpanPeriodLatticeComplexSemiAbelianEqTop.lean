import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPerHolOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactSpacePts

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.PeriodSpan.TorusExp

section Torus

variable {Λ : Type} [AddCommGroup Λ]

def expRing (m : Λ →+ ℂ) : torusRing ZU Λ →+* ℂ :=
  AddMonoidAlgebra.liftNCRingHom ((Int.castRingHom ℂ).comp (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ).toRingHom)
    { toFun := fun x => Complex.exp (m (Multiplicative.toAdd x))
      map_one' := by simp
      map_mul' := fun x y => by simp [Complex.exp_add] }
    (fun _ _ => Commute.all _ _)

theorem expRing_single (m : Λ →+ ℂ) (x : Λ) (r : ULift.{0} ℤ) :
    expRing m (AddMonoidAlgebra.single x r) = (r.down : ℂ) * Complex.exp (m x) := by
  simp [expRing, AddMonoidAlgebra.liftNCRingHom_single]
  rfl

def expPt (m : Λ →+ ℂ) : Over.mk (𝟙 (Sp ℂ)) ⟶ splitTorus (Spec (.of ℂ)) Λ :=
  SplitTorus.ofCoord (CommRingCat.ofHom (expRing m) ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv)

theorem val_expPt (m : Λ →+ ℂ) (x : Λ) :
    SplitTorus.val (expPt m) x = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom (Complex.exp (m x)) := by
  unfold SplitTorus.val expPt
  rw [SplitTorus.coord_ofCoord]
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
  erw [expRing_single]
  simp

theorem expPt_add (m m' : Λ →+ ℂ) : expPt (m + m') = expPt m * expPt m' := by
  apply SplitTorus.hom_ext
  intro a
  simp only [SplitTorus.val_mul, val_expPt, AddMonoidHom.add_apply, Complex.exp_add, map_mul]

theorem expPt_zero : expPt (0 : Λ →+ ℂ) = 1 := by
  apply SplitTorus.hom_ext
  intro a
  simp only [val_expPt, SplitTorus.val_one, AddMonoidHom.zero_apply, Complex.exp_zero, map_one]

theorem expPt_sum_mem {κ : Type} (s : Finset κ) (m : κ → Λ →+ ℂ)
    (H : Subgroup (Over.mk (𝟙 (Sp ℂ)) ⟶ splitTorus (Spec (.of ℂ)) Λ)) (h : ∀ i, expPt (m i) ∈ H) :
    expPt (∑ i ∈ s, m i) ∈ H := by
  classical
  refine Finset.induction_on s (by rw [Finset.sum_empty, expPt_zero]; exact H.one_mem) ?_
  intro j s hj ih
  rw [Finset.sum_insert hj, expPt_add]
  exact H.mul_mem (h j) ih

theorem exists_eq_expPt [Module.Free ℤ Λ] (t : Over.mk (𝟙 (Sp ℂ)) ⟶ splitTorus (Spec (.of ℂ)) Λ) :
    ∃ l : Λ →+ ℂ, t = expPt ((2 * Real.pi * Complex.I : ℂ) • l) := by
  let φ : Λ → ℂˣ := fun x =>
    ((SplitTorus.isUnit_val t x).map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom).unit
  have hφ : ∀ x, (φ x : ℂ) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (SplitTorus.val t x) :=
    fun x => rfl
  obtain ⟨l, hl⟩ := GlobalTheory.Ex.Arch.exists_log_of_character φ (fun x y => by
    ext
    simp only [Units.val_mul, hφ, SplitTorus.val_add, map_mul])
  refine ⟨l, SplitTorus.hom_ext fun a => ?_⟩
  rw [val_expPt]
  have h1 := hl a
  rw [hφ] at h1
  unfold eTwoPi at h1
  rw [AddMonoidHom.smul_apply, smul_eq_mul, ← h1]
  simp

private theorem isHolTo_comp_continuousLinearMap {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X Y : Scheme.{0}}
    {B : Set V} {f : V → (Sp ℂ ⟶ X)} (hf : IsHolTo B f) (g : X ⟶ Y) : IsHolTo B fun b => f b ≫ g := by
  intro U s
  obtain ⟨h1, h2⟩ := hf (g ⁻¹ᵁ U) ((g.app U).hom s)
  have key : ∀ b, valAt' (f b ≫ g) U s = valAt' (f b) (g ⁻¹ᵁ U) ((g.app U).hom s) := by
    intro b
    unfold valAt'
    by_cases hb : ⊤ ≤ (f b ≫ g) ⁻¹ᵁ U
    · have hb' : ⊤ ≤ f b ⁻¹ᵁ g ⁻¹ᵁ U := hb
      rw [dif_pos hb, dif_pos hb']
      unfold valAt
      rw [Scheme.Hom.comp_appLE]
      rfl
    · have hb' : ¬ ⊤ ≤ f b ⁻¹ᵁ g ⁻¹ᵁ U := hb
      rw [dif_neg hb, dif_neg hb']
  exact ⟨h1, h2.congr fun b _ => key b⟩

theorem isHolTo_expPt {m : ℂ → Λ →+ ℂ} (hm : ∀ x, Differentiable ℂ fun s => m s x) :
    IsHolTo Set.univ fun s => (show Sp ℂ ⟶ _ from (expPt (m s)).left) := by
  let ψ : ℂ → (AddMonoidAlgebra ℂ Λ →+* ℂ) := fun s =>
    AddMonoidAlgebra.liftNCRingHom (RingHom.id ℂ)
      { toFun := fun x => Complex.exp (m s (Multiplicative.toAdd x))
        map_one' := by simp
        map_mul' := fun x y => by simp [Complex.exp_add] }
      (fun _ _ => Commute.all _ _)
  have hψs : ∀ s a c, ψ s (AddMonoidAlgebra.single a c) = c * Complex.exp (m s a) := by
    intro s a c
    simp [ψ, AddMonoidAlgebra.liftNCRingHom_single]
  have hψ0 : ∀ s, (ψ s).comp (algebraMap ℂ (AddMonoidAlgebra ℂ Λ)) = RingHom.id ℂ := by
    intro s
    ext c
    simp [AddMonoidAlgebra.coe_algebraMap, hψs]
  have hs : ∀ s, Spec.map (CommRingCat.ofHom ((ψ s).comp (algebraMap (CommRingCat.of ℂ)
      (AddMonoidAlgebra (CommRingCat.of ℂ) Λ)))) ≫ 𝟙 (Spec (CommRingCat.of ℂ)) = 𝟙 (Sp ℂ) := by
    intro s
    rw [hψ0 s, Category.comp_id]
    exact Spec.map_id _
  have key : ∀ s, expPt (m s) = SplitTorus.ptOf (S := Spec (CommRingCat.of ℂ)) (X := Λ) (A := CommRingCat.of ℂ)
      (B := CommRingCat.of ℂ) (s := 𝟙 (Sp ℂ)) (𝟙 _) (ψ s) (hs s) := by
    intro s
    apply SplitTorus.pull_ext
    intro a
    rw [SplitTorus.pull_ptOf, SplitTorus.ev_chi, SplitTorus.pull_chi, val_expPt]
    erw [hψs]
    simp
  have hd : ∀ u : AddMonoidAlgebra ℂ Λ, DifferentiableOn ℂ (fun s => ψ s u) Set.univ := by
    intro u
    refine AddMonoidAlgebra.induction_linear u ?_ ?_ ?_
    · simp
    · intro f g hf hg
      simp only [map_add]
      exact hf.add hg
    · intro a c
      simp only [hψs]
      exact ((hm a).cexp.const_mul c).differentiableOn
  have hhol := isHolTo_comp_continuousLinearMap (GlobalTheory.ThetaValueCont.isHolTo_spMap isOpen_univ ψ hd)
    (SplitTorus.univPt Λ (𝟙 (Spec (CommRingCat.of ℂ)))).left
  convert hhol using 1
  funext s
  rw [key s]
  rfl

def oneParam (n : Λ →+ ℤ) (s : ℂ) : Over.mk (𝟙 (Sp ℂ)) ⟶ splitTorus (Spec (.of ℂ)) Λ :=
  expPt (s • (Int.castAddHom ℂ).comp n)

theorem oneParam_add (n : Λ →+ ℤ) (s s' : ℂ) : oneParam n (s + s') = oneParam n s * oneParam n s' := by
  simp only [oneParam, add_smul, expPt_add]

theorem oneParam_period (n : Λ →+ ℤ) : oneParam n (2 * Real.pi * Complex.I) = 1 := by
  apply SplitTorus.hom_ext
  intro a
  simp only [oneParam, val_expPt, SplitTorus.val_one, AddMonoidHom.smul_apply, AddMonoidHom.comp_apply,
    Int.coe_castAddHom, smul_eq_mul]
  rw [mul_comm (2 * (Real.pi : ℂ) * Complex.I), Complex.exp_int_mul_two_pi_mul_I, map_one]

theorem isHolTo_oneParam (n : Λ →+ ℤ) : IsHolTo Set.univ fun s => (show Sp ℂ ⟶ _ from (oneParam n s).left) := by
  refine isHolTo_expPt fun x => ?_
  simp only [AddMonoidHom.smul_apply, AddMonoidHom.comp_apply, smul_eq_mul]
  fun_prop

theorem mem_closure_oneParam [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (t : Over.mk (𝟙 (Sp ℂ)) ⟶ splitTorus (Spec (.of ℂ)) Λ) :
    t ∈ Subgroup.closure (⋃ n : Λ →+ ℤ, Set.range (oneParam n)) := by
  obtain ⟨l, rfl⟩ := exists_eq_expPt t
  set M : Λ →+ ℂ := (2 * Real.pi * Complex.I : ℂ) • l
  let b := Module.Free.chooseBasis ℤ Λ
  have hM : M = ∑ j, M (b j) • (Int.castAddHom ℂ).comp (b.coord j).toAddMonoidHom := by
    ext x
    simp
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, zsmul_eq_mul]
    ring
  rw [hM]
  refine expPt_sum_mem _ _ _ fun j => Subgroup.subset_closure ?_
  exact Set.mem_iUnion.2 ⟨(b.coord j).toAddMonoidHom, M (b j), rfl⟩

end Torus

section Push

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {y : Sp ℂ ⟶ X} {Λ : Type} [AddCommGroup Λ]
  (i : splitTorus (Spec (.of ℂ)) Λ ⟶ (Over.pullback y).obj G)

theorem left_mul_congr {y' : Sp ℂ ⟶ X} (hy : y' = y) {a b : Over.mk y' ⟶ G} {a' b' : Over.mk y ⟶ G}
    (ha : (show Sp ℂ ⟶ G.left from a.left) = a'.left) (hb : (show Sp ℂ ⟶ G.left from b.left) = b'.left) :
    (show Sp ℂ ⟶ G.left from (a * b).left) = (a' * b').left := by
  subst hy
  have h1 : a = a' := Over.OverMorphism.ext ha
  have h2 : b = b' := Over.OverMorphism.ext hb
  subst h1 h2
  rfl

omit [GrpObj G] in
theorem push_w (t : Over.mk (𝟙 (Sp ℂ)) ⟶ splitTorus (Spec (.of ℂ)) Λ) :
    ((t ≫ i).left ≫ pullback.fst G.hom y) ≫ G.hom = (Over.mk (𝟙 (Sp ℂ))).hom ≫ y := by
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  congr 1
  exact Over.w (t ≫ i)

def push (t : Over.mk (𝟙 (Sp ℂ)) ⟶ splitTorus (Spec (.of ℂ)) Λ) : Over.mk y ⟶ G :=
  Over.homMk ((t ≫ i).left ≫ pullback.fst G.hom y) ((push_w i t).trans (Category.id_comp y))

theorem push_mul [IsMonHom i] (t t' : Over.mk (𝟙 (Sp ℂ)) ⟶ splitTorus (Spec (.of ℂ)) Λ) :
    push i (t * t') = push i t * push i t' := by
  apply Over.OverMorphism.ext
  have hx := SplitTorus.mul_left_comp_fst G y (t ≫ i) (t' ≫ i)
    (Over.homMk ((t ≫ i).left ≫ pullback.fst G.hom y) (push_w i t))
    (Over.homMk ((t' ≫ i).left ≫ pullback.fst G.hom y) (push_w i t')) rfl rfl
  have hc := left_mul_congr (G := G) (Category.id_comp y)
    (a := Over.homMk ((t ≫ i).left ≫ pullback.fst G.hom y) (push_w i t))
    (b := Over.homMk ((t' ≫ i).left ≫ pullback.fst G.hom y) (push_w i t'))
    (a' := push i t) (b' := push i t') rfl rfl
  calc (push i (t * t')).left = ((t * t') ≫ i).left ≫ pullback.fst G.hom y := rfl
    _ = ((t ≫ i) * (t' ≫ i)).left ≫ pullback.fst G.hom y := by rw [MonObj.mul_comp]
    _ = _ := hx.symm
    _ = _ := hc

def pushHom [IsMonHom i] : (Over.mk (𝟙 (Sp ℂ)) ⟶ splitTorus (Spec (.of ℂ)) Λ) →* (Over.mk y ⟶ G) :=
  MonoidHom.mk' (push i) (push_mul i)

theorem isPerHol_push [IsMonHom i] (n : Λ →+ ℤ) : IsPerHol G y fun s => pushHom i (oneParam n s) := by
  unfold IsPerHol
  refine ⟨fun s t => by simp only [oneParam_add, map_mul], ?_, by simp only [oneParam_period, map_one]⟩
  exact isHolTo_comp_continuousLinearMap (isHolTo_comp_continuousLinearMap (isHolTo_oneParam n) i.left) (pullback.fst G.hom y)

end Push

end GlobalTheory.PeriodSpan.TorusExp

namespace GlobalTheory.PeriodSpan

open TorusExp in

theorem torusPts_subset_perHolSub (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X)
    (E : TorusExtension ((Over.pullback y).obj G)) :
    torusPts G y E ⊆ (perHolSub G y : Set (Over.mk y ⟶ G)) := by
  let _ := E.addCommGroup
  have : Module.Free ℤ E.X := E.free
  have : Module.Finite ℤ E.X := E.finite
  have : IsMonHom E.i := E.i_hom
  rintro x ⟨t, ht⟩
  have hx : x = pushHom E.i t := Over.OverMorphism.ext ht.symm
  rw [hx, SetLike.mem_coe]
  unfold perHolSub
  have hmap := Subgroup.mem_map_of_mem (pushHom E.i) (mem_closure_oneParam t)
  rw [MonoidHom.map_closure] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨n, s, rfl⟩ := Set.mem_iUnion.1 hz
  exact Set.mem_iUnion₂.2 ⟨_, isPerHol_push E.i n, s, rfl⟩

end GlobalTheory.PeriodSpan
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.PeriodSpan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusPoints_subset_holPeriodicOneParamSpan : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X) (E : TorusExtension ((Over.pullback y).obj G)), torusPts G y E ⊆ (perHolSub G y : Set (Over.mk y ⟶ G)) := by
  first | exact @GlobalTheory.PeriodSpan.torusPts_subset_perHolSub | exact GlobalTheory.PeriodSpan.torusPts_subset_perHolSub | (intros; apply GlobalTheory.PeriodSpan.torusPts_subset_perHolSub <;> assumption)
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam GlobalTheory.ShFam.BdArc
  Filter Topology
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.PeriodSpan GlobalTheory.Points GlobalTheory.IntegralPower

namespace GlobalTheory.TorusCocompact

theorem exists_isCompact_surjOn {V H : Type} [NormedAddCommGroup V] [ProperSpace V] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CompactSpace H] [T2Space H] (φ : V → H) (hφ : ∀ z w, φ (z + w) = φ z * φ w)
    (hs : Function.Surjective φ) (hc : Continuous φ) : ∃ C : Set V, IsCompact C ∧ ∀ z, ∃ c ∈ C, φ (z - c) = 1 := by
  let ψ : V →+ Additive H := AddMonoidHom.mk' (fun z => Additive.ofMul (φ z)) hφ
  have : BaireSpace (Additive H) := inferInstanceAs (BaireSpace H)
  have : T2Space (Additive H) := inferInstanceAs (T2Space H)
  have ho : IsOpenMap φ := AddMonoidHom.isOpenMap_of_sigmaCompact ψ hs hc
  obtain ⟨n, hn⟩ := isCompact_univ.elim_directed_cover (fun n : ℕ => φ '' Metric.ball 0 n)
    (fun n => ho _ Metric.isOpen_ball) (fun h _ => by
      obtain ⟨z, rfl⟩ := hs h
      obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
      exact Set.mem_iUnion.2 ⟨n, z, by simpa using hn, rfl⟩)
    (Monotone.directed_le fun m n h => Set.image_mono (Metric.ball_subset_ball (Nat.cast_le.2 h)))
  refine ⟨Metric.closedBall 0 n, isCompact_closedBall _ _, fun z => ?_⟩
  obtain ⟨c, hc, hcz⟩ := hn (Set.mem_univ (φ z))
  refine ⟨c, Metric.ball_subset_closedBall hc, ?_⟩
  have h := hφ (z - c) c
  rw [sub_add_cancel, hcz] at h
  exact (mul_eq_right.1 h.symm)

theorem exists_lift_point {A B : Over (Sp ℂ)} (q : A ⟶ B) [Surjective q.left] [LocallyOfFiniteType q.left]
    (w : Over.mk (𝟙 (Sp ℂ)) ⟶ B) : ∃ u : Over.mk (𝟙 (Sp ℂ)) ⟶ A, u ≫ q = w := by
  let w' : Sp ℂ ⟶ B.left := w.left
  obtain ⟨z, -⟩ := (pullback.snd q.left w').surjective (IsLocalRing.closedPoint ℂ)
  obtain ⟨x, hx, -⟩ := GlobalTheory.ComplexPoints.exists_point_mem (pullback.snd q.left w') isClosed_univ.isLocallyClosed
    ⟨z, trivial⟩
  have h : (x ≫ pullback.fst q.left w') ≫ q.left = w' := by
    rw [Category.assoc, pullback.condition, reassoc_of% hx]
  refine ⟨Over.homMk (x ≫ pullback.fst q.left w') ?_, Over.OverMorphism.ext h⟩
  rw [← Over.w q, ← Category.assoc]
  exact (congrArg (· ≫ B.hom) h).trans (Over.w w)

section Fibre

variable {X : Scheme.{0}} {G : Over X} {y : Sp ℂ ⟶ X}

def fibrePt (x : Over.mk y ⟶ G) : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback y).obj G :=
  Over.homMk (pullback.lift x.left (𝟙 (Sp ℂ)) ((Over.w x).trans (Category.id_comp y).symm))
    (pullback.lift_snd _ _ _)

theorem fibrePt_fst (x : Over.mk y ⟶ G) : (fibrePt x).left ≫ pullback.fst G.hom y = x.left :=
  pullback.lift_fst _ _ _

theorem fibre_ext {u v : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback y).obj G}
    (h : u.left ≫ pullback.fst G.hom y = v.left ≫ pullback.fst G.hom y) : u = v :=
  Over.OverMorphism.ext (pullback.hom_ext h ((Over.w u).trans (Over.w v).symm))

theorem fibrePt_surjective : Function.Surjective (fibrePt (G := G) (y := y)) := fun u =>
  ⟨Over.homMk (u.left ≫ pullback.fst G.hom y) (by
    have h : u.left ≫ pullback.snd G.hom y = 𝟙 _ := Over.w u
    rw [Category.assoc, pullback.condition, reassoc_of% h]
    rfl), fibre_ext (fibrePt_fst _)⟩

theorem fibrePt_mul [GrpObj G] (a b : Over.mk y ⟶ G) : fibrePt (a * b) = fibrePt a * fibrePt b := by
  let U : Over.mk ((Over.mk (𝟙 (Sp ℂ))).hom ≫ y) ⟶ Over.mk y := Over.homMk (𝟙 (Sp ℂ)) rfl
  have hU : ∀ x : Over.mk y ⟶ G, (U ≫ x).left = x.left := fun x => Category.id_comp _
  refine fibre_ext ?_
  rw [fibrePt_fst, ← (isGrpPullback_pullback G y).2 _ (fibrePt a) (fibrePt b) (U ≫ a) (U ≫ b)
    ((hU a).trans (fibrePt_fst a).symm) ((hU b).trans (fibrePt_fst b).symm), ← comp_mul, hU]

theorem continuous_fibrePt {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (e : V → (Over.mk y ⟶ G))
    (he : IsHolTo Set.univ (fun z => (e z).left)) :
    Continuous fun z => leftPt (𝟙 (Sp ℂ)) (fibrePt (e z)) := by
  have h1 : Continuous fun z => leftPt y (e z) := by
    refine GlobalTheory.Points.continuous_iff.2 fun U => ⟨?_, fun f => ?_⟩
    · simpa using (he U 0).1
    · exact (he U f).2.continuousOn.mono fun _ hb => ⟨trivial, hb⟩
  refine (isEmbedding_of_isPullback (C := ℂ) (IsPullback.of_hasPullback G.hom y)).continuous_iff.2 ?_
  refine (h1.prodMk (continuous_const (y := 𝟙 (Sp ℂ)))).congr fun z => ?_
  exact Prod.ext (fibrePt_fst (e z)).symm (Over.w (fibrePt (e z))).symm

end Fibre

attribute [local instance] ptTopology in

theorem exists_isCompact_mod_torusPts : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X) (g : ℕ)
    (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (E : TorusExtension ((Over.pullback y).obj G)), IsSemiAbelian G →
    (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → IsHolTo Set.univ (fun z => (e z).left) →
    (∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) →
    ∃ C : Set (Fin g → ℂ), IsCompact C ∧ ∀ z, ∃ c ∈ C, e (z - c) ∈ torusPts G y E := by
  intro X G _ y g e E hG hadd hsurj hhol _
  let := E.addCommGroup
  let := E.grpB
  have := E.q_hom
  have := E.q_surjective
  have := E.isAbelian.proper
  have := hG.smooth
  have : LocallyOfFiniteType (E.q.left ≫ E.B.hom) := by
    rw [Over.w E.q]
    exact inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom y))
  have : LocallyOfFiniteType E.q.left := locallyOfFiniteType_of_comp _ E.B.hom
  have : CompactSpace (PtsOver E.B.hom (𝟙 (Sp ℂ))) := GlobalTheory.ProperPoints.compactSpace_pts E.B.hom
  have := compactSpace_of_ptsOver (𝟙 (Sp ℂ)) E.B
  have := isTopologicalGroup (𝟙 (Sp ℂ)) E.B
  have : T2Space (Over.mk (𝟙 (Sp ℂ)) ⟶ E.B) :=
    have := PtsOver.t2Space E.B.hom (𝟙 (Sp ℂ))
    T2Space.of_injective_continuous (f := fun x => (⟨x.left, Over.w x⟩ : PtsOver E.B.hom (𝟙 (Sp ℂ))))
      (fun _ _ h => Over.OverMorphism.ext (congrArg Subtype.val h))
      ((isEmbedding_leftPt (𝟙 (Sp ℂ)) E.B).continuous.subtype_mk _)
  obtain ⟨C, hC, H⟩ := exists_isCompact_surjOn (fun z => fibrePt (e z) ≫ E.q)
    (fun z w => by rw [hadd, fibrePt_mul, mul_comp])
    (fun w => by
      obtain ⟨u, rfl⟩ := exists_lift_point E.q w
      obtain ⟨x, rfl⟩ := fibrePt_surjective u
      obtain ⟨z, rfl⟩ := hsurj x
      exact ⟨z, rfl⟩)
    ((continuous_comp_over _ E.q).comp ((isEmbedding_leftPt _ _).continuous_iff.2 (continuous_fibrePt e hhol)))
  refine ⟨C, hC, fun z => ?_⟩
  obtain ⟨c, hc, hz⟩ := H z
  refine ⟨c, hc, E.isKernel.lift (fibrePt (e (z - c))) (toUnit _) hz, ?_⟩
  rw [IsPullback.lift_fst]
  exact fibrePt_fst _

end GlobalTheory.TorusCocompact
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.PeriodSpan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_representatives_mod_torusPoints : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (E : TorusExtension ((Over.pullback y).obj G)), IsSemiAbelian G → (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → IsHolTo Set.univ (fun z => (e z).left) → (∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) → ∃ C : Set (Fin g → ℂ), IsCompact C ∧ ∀ z, ∃ c ∈ C, e (z - c) ∈ torusPts G y E := by
  atlas_forward_decl GlobalTheory.TorusCocompact.exists_isCompact_mod_torusPts
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.PeriodSpan

namespace GlobalTheory.PeriodSpan

theorem span_ker_eq_top : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsSemiAbelian G → ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective (e) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) ∧ (∀ w, ∃! v : epsPt (y) ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ (∀ v : epsPt (y) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) → Submodule.span ℂ {z | e z = 1} = ⊤ := by
  intro X G _ y g e hG ⟨hadd, hsurj, hhol, _, hd2⟩
  have hhol' : IsHolTo Set.univ (fun z => (e z).left) := hhol
  have h0 : e 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hsub : ∀ z w, e (z - w) = e z * (e w)⁻¹ := fun z w =>
    eq_mul_inv_of_mul_eq (by rw [← hadd, sub_add_cancel])
  by_contra hne
  obtain ⟨ℓ, hℓ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  have hℓK : ∀ z, e z = 1 → ℓ z = 0 := fun z hz => hle (Submodule.subset_span hz)
  have hℓeq : ∀ z w, e z = e w → ℓ z = ℓ w := fun z w h => by
    have := hℓK (z - w) (by rw [hsub, h, mul_inv_cancel])
    rwa [map_sub, sub_eq_zero] at this
  let lam : (Over.mk y ⟶ G) → ℂ := fun x => ℓ (hsurj x).choose
  have hlam : ∀ z, lam (e z) = ℓ z := fun z => hℓeq _ _ (hsurj (e z)).choose_spec
  let S : Subgroup (Over.mk y ⟶ G) :=
    { carrier := {x | lam x = 0}
      one_mem' := by
        show lam 1 = 0
        rw [← h0, hlam, map_zero]
      mul_mem' := by
        intro x x' hx hx'
        obtain ⟨a, rfl⟩ := hsurj x
        obtain ⟨b, rfl⟩ := hsurj x'
        show lam (e a * e b) = 0
        have hx : lam (e a) = 0 := hx
        have hx' : lam (e b) = 0 := hx'
        rw [← hadd, hlam, map_add, ← hlam, ← hlam, hx, hx', add_zero]
      inv_mem' := by
        intro x hx
        obtain ⟨a, rfl⟩ := hsurj x
        have hx : lam (e a) = 0 := hx
        show lam (e a)⁻¹ = 0
        have hinv : (e a)⁻¹ = e (-a) :=
          inv_eq_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, h0])
        rw [hinv, hlam, map_neg, ← hlam, hx, neg_zero] }
  have hper : perHolSub G y ≤ S := by
    refine Subgroup.closure_le _ |>.2 (Set.iUnion₂_subset fun ψ hψ => Set.range_subset_iff.2 fun s => ?_)
    obtain ⟨hψadd, hψhol, hψper⟩ := hψ
    obtain ⟨h, hh, -⟩ := (GlobalTheory.holomorphic_hom_determined X G).2.2.1 y ℂ g ψ e hψadd hadd hψhol hhol' hd2
    have hlin : ∀ s : ℂ, h s = s • h 1 := fun s => by rw [← h.map_smul, smul_eq_mul, _root_.mul_one]
    have h1 : ℓ (h 1) = 0 := by
      have h2 : ℓ (h (2 * Real.pi * Complex.I)) = 0 := hℓK _ (by rw [← hh, hψper])
      rw [hlin, map_smul, smul_eq_mul] at h2
      refine (mul_eq_zero.1 h2).resolve_left ?_
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    show lam (ψ s) = 0
    rw [hh, hlam, hlin, map_smul, h1, smul_zero]
  obtain ⟨E⟩ := hG.fibres ℂ y
  have htor : ∀ x ∈ torusPts G y E, lam x = 0 := fun x hx => hper (GlobalTheory.T.torusPoints_subset_holPeriodicOneParamSpan X G y E hx)
  obtain ⟨C, hC, hCz⟩ := GlobalTheory.T.exists_compact_representatives_mod_torusPoints X G y g e E hG hadd hsurj hhol' hd2
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (LinearMap.continuous_of_finiteDimensional ℓ).continuousOn
  have hbd : ∀ z, ‖ℓ z‖ ≤ M := fun z => by
    obtain ⟨c, hc, hzc⟩ := hCz z
    have := htor _ hzc
    rw [hlam, map_sub, sub_eq_zero] at this
    rw [this]
    exact hM c hc
  apply hℓ0
  refine LinearMap.ext fun z => ?_
  by_contra hz0
  have hz : ℓ z ≠ 0 := by simpa using hz0
  have hpos : 0 < ‖ℓ z‖ := norm_pos_iff.2 hz
  have := hbd ((((|M| + 1) / ‖ℓ z‖ : ℝ) : ℂ) • z)
  rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
    div_mul_cancel₀ _ hpos.ne'] at this
  linarith [le_abs_self M]

end GlobalTheory.PeriodSpan
end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_periodLattice_complexSemiAbelian_eq_top : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsSemiAbelian G → ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective (e) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) ∧ (∀ w, ∃! v : epsPt (y) ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ (∀ v : epsPt (y) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) → Submodule.span ℂ {z | e z = 1} = ⊤ := by
  atlas_forward_decl GlobalTheory.PeriodSpan.span_ker_eq_top
end
