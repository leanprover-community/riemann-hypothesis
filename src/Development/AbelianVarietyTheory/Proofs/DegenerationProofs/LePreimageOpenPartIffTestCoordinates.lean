import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeZeroOfLe
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMaximalComapMaximalIdealOO
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisTestLattice
import BuildAid.ForwardExisting

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.WeightZero

theorem eq_zero_of_q_nonpos {X : Type} [AddCommGroup X] [Module.Free ℤ X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) {α : X} (h : q α ≤ 0) : α = 0 := by
  by_contra h0
  have h1 : {x | ¬ 0 < q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_gt_atTop 0)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => n • α) (smul_left_injective ℤ h0)
    (fun n => ?_) h1
  rw [Set.mem_setOf_eq, q.map_smul, not_lt]
  exact smul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg n) h

theorem proj_congr {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    {T T' : AddSubgroup S.Gam} (h : T = T') (c : T →+ ZMod S.N) (c' : T' →+ ZMod S.N)
    (hc : ∀ t ht ht', c ⟨t, ht⟩ = c' ⟨t, ht'⟩) : S.proj T c = S.proj T' c' := by
  subst h
  rw [show c = c' from AddMonoidHom.ext fun t => hc t.1 t.2 t.2]

theorem nsmul_char {T : Type} [AddCommGroup T] (N : ℕ) (c : T →+ ZMod N) : N • c = 0 := by
  ext x
  rw [AddMonoidHom.nsmul_apply]
  simp

theorem map_add_nsmul {X T : Type} [AddCommGroup X] [AddCommGroup T] (N : ℕ) (w : X →+ (T →+ ZMod N)) (β m : X) :
    w (β + N • m) = w β := by
  rw [map_add, map_nsmul, nsmul_char, add_zero]

theorem span_eq_of_test {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [hA : ArithBase o Ω] {S : ThetaSys o Ω}
    {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (τ : S.Test p y₀) (b : S.J → S.J → PadicAlgCl p)
    (a : S.J → τ.X) (ha : ∀ i v, τ.q (a i) ≤ τ.q (a i + S.N • v))
    (hE : τ.E = Submodule.span (OO p) (Set.range b))
    (hb : ∀ i, ((S.proj _ (τ.wt (a i))).map fun x => y₀ (algebraMap o S.R x)).mulVec (b i) = b i) :
    Submodule.span (OO p) (b '' {i | a i = 0}) =
      Submodule.span (OO p) (Set.range fun i j => y₀ (algebraMap o S.R (S.proj (S.perp τ.yy.ker) 0 j i))) := by
  have : IsDomain o := hA.inj.isDomain
  have := FreeNear.finite_char S (S.perp τ.yy.ker)
  have := Fintype.ofFinite (S.perp τ.yy.ker →+ ZMod S.N)
  obtain ⟨hmul, -⟩ := FreeNear.proj_orthogonal S _ τ.isoFree
  have hz : ∀ α, (∀ v, τ.q α ≤ τ.q (α + S.N • v)) → 0 = τ.wt α → α = 0 := fun α hα h => by
    have h3 := TestBasis.q_le_of_wt_eq τ hα (β := 0) (by rw [map_zero, h])
    rw [map_zero] at h3
    exact eq_zero_of_q_nonpos _ τ.pos h3
  let φ : o →+* PadicAlgCl p := y₀.comp (algebraMap o S.R)
  obtain ⟨Q, hQd⟩ : ∃ Q : (S.perp τ.yy.ker →+ ZMod S.N) → Matrix S.J S.J (PadicAlgCl p),
    ∀ c j i, y₀ (algebraMap o S.R (S.proj _ c j i)) = Q c j i := ⟨fun c => (S.proj _ c).map φ, fun _ _ _ => rfl⟩
  have hQe : ∀ c, Q c = φ.mapMatrix (S.proj _ c) := fun c => Matrix.ext fun j i => (hQd c j i).symm
  have hQ : ∀ c, Q 0 * Q c = if 0 = c then Q 0 else 0 := fun c => by
    rw [hQe, hQe, ← map_mul, hmul]
    split_ifs
    · rfl
    · exact map_zero _
  obtain ⟨L, hL⟩ : ∃ L : (S.J → PadicAlgCl p) →ₗ[OO p] (S.J → PadicAlgCl p), ∀ v, L v = (Q 0).mulVec v :=
    ⟨(Q 0).mulVecLin.restrictScalars (OO p), fun _ => rfl⟩
  have hcol : ∀ c i, L (fun j => Q c j i) = fun j => (Q 0 * Q c) j i := fun c i => hL _
  have hb' : ∀ i, (Q (τ.wt (a i))).mulVec (b i) = b i := fun i => by
    rw [hQe]
    exact hb i
  simp only [hQd]
  have h1 : τ.E.map L ≤ Submodule.span (OO p) (Set.range fun i j => Q 0 j i) := by
    rw [ThetaSys.Test.E, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨α, l, i, hα, hl, rfl⟩, rfl⟩
    simp only [hQd]
    have h2 : L (fun j => l * Q (τ.wt α) j i) = l • fun j => (Q 0 * Q (τ.wt α)) j i := by
      rw [← hcol, hL, hL, ← Matrix.mulVec_smul]
      rfl
    rw [h2, hQ]
    split_ifs with h
    · rw [hz α hα h, map_zero, zero_div, Real.exp_zero] at hl
      exact Submodule.smul_mem _ (⟨l, (mem_OO_iff _).2 hl⟩ : OO p) (Submodule.subset_span ⟨i, rfl⟩)
    · rw [show (fun j => (0 : Matrix S.J S.J (PadicAlgCl p)) j i) = 0 from rfl, smul_zero]
      exact Submodule.zero_mem _
  have h2 : τ.E.map L ≤ Submodule.span (OO p) (b '' {i | a i = 0}) := by
    rw [hE, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    by_cases h : 0 = τ.wt (a i)
    · rw [hL, h, hb']
      exact Submodule.subset_span ⟨i, hz _ (ha i) h, rfl⟩
    · rw [hL, ← hb', Matrix.mulVec_mulVec, hQ, if_neg h, Matrix.zero_mulVec]
      exact Submodule.zero_mem _
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, hi, rfl⟩
    refine h1 ⟨b i, hE ▸ Submodule.subset_span ⟨i, rfl⟩, ?_⟩
    have := hb' i
    rw [show a i = 0 from hi, map_zero] at this
    rw [hL, this]
  · rintro _ ⟨i, rfl⟩
    refine h2 ⟨fun j => Q 0 j i, Submodule.subset_span ⟨0, 1, i, fun v => ?_, ?_, ?_⟩, ?_⟩
    · rw [map_zero]
      by_contra! h
      rw [eq_zero_of_q_nonpos _ τ.pos h.le, map_zero] at h
      exact lt_irrefl _ h
    · simp
    · funext j
      rw [map_zero, _root_.one_mul, hQd]
    · rw [hcol, hQ, if_pos rfl]

theorem short_transfer {X Y Z : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] (e : X ≃+ Y) (f : Z ≃+ Y)
    (q : QuadraticMap ℤ X ℝ) (q' : QuadraticMap ℤ Y ℝ) (hq : ∀ α, q α = q' (e α)) {N : ℕ} {y : Y}
    (h : Short (q'.comp f.toIntLinearEquiv.toLinearMap) N (f.symm y)) (v : X) :
    q (e.symm y) ≤ q (e.symm y + N • v) := by
  have h3 : q' (f (f.symm y)) ≤ q' (f (f.symm y + N • f.symm (e v))) := h (f.symm (e v))
  simpa [hq] using h3

end GlobalTheory.ZH.WeightZero

namespace GlobalTheory.ZH

open WeightZero in

theorem span_rows_class_zero : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → t.τ.yy.ker = t.l.yy.ker ∧ (∀ α β, t.l.wt α = t.l.wt β ↔ ∃ m, α = β + S.N • m) ∧ Submodule.span (OO p) ((t.b.map (algebraMap _ (PadicAlgCl p))) '' {i | t.cls i = 0}) = Submodule.span (OO p) (Set.range fun i j => y₀ (algebraMap o S.R (S.proj (S.perp t.l.yy.ker) 0 j i))) := by
  intro o Ω _ _ _ hA S ρ p _ y₀ t _
  obtain ⟨e, hq, hy⟩ := t.mt
  have hker : t.τ.yy.ker = t.l.yy.ker := by
    ext a
    have := hy a 0
    rw [map_zero] at this
    exact this
  have hwt : ∀ α x h h', t.τ.wt α ⟨x, h⟩ = t.l.wt (e α) ⟨x, h'⟩ := fun α x h h' => by
    obtain ⟨a, ha⟩ := t.τ.yy_onto (QuotientAddGroup.mk α)
    rw [t.τ.wt_eq a α ha, t.l.wt_eq a _ ((hy a α).1 ha)]
  have hz : ∀ α, t.l.wt (e α) = 0 → ∃ v, α = S.N • v := fun α h =>
    TestBasis.exists_nsmul_of_wt_eq_zero t.τ α (AddMonoidHom.ext fun x => by
      rw [hwt α x.1 x.2 (hker ▸ x.2), h]
      rfl)
  have hcl : ∀ α β, t.l.wt α = t.l.wt β ↔ ∃ m, α = β + S.N • m := fun α β => by
    constructor
    · intro h
      obtain ⟨v, hv⟩ := hz (e.symm (α - β)) (by rw [e.apply_symm_apply, map_sub, h, sub_self])
      refine ⟨e v, ?_⟩
      rw [← map_nsmul, ← hv, e.apply_symm_apply, add_sub_cancel]
    · rintro ⟨m, rfl⟩
      exact map_add_nsmul _ _ _ _
  refine ⟨hker, hcl, ?_⟩
  have h1 := span_eq_of_test t.τ (t.b.map (algebraMap _ (PadicAlgCl p))) (fun i => e.symm (t.cls i))
    (fun i => short_transfer e t.mod.xe _ _ hq (t.mod.good.short i)) t.span
    (fun i => by
      have h3 : S.proj _ (t.τ.wt (e.symm (t.cls i))) = S.proj _ (t.l.wt (t.cls i)) :=
        proj_congr S (congrArg S.perp hker) _ _ fun x h h' =>
          (hwt _ x h h').trans (by rw [e.apply_symm_apply])
      rw [h3]
      exact t.wt i)
  have h2 : {i | e.symm (t.cls i) = 0} = {i | t.cls i = 0} := Set.ext fun i => e.symm.map_eq_zero_iff
  have h3 : S.proj (S.perp t.τ.yy.ker) 0 = S.proj (S.perp t.l.yy.ker) 0 :=
    proj_congr S (congrArg S.perp hker) _ _ fun _ _ _ => rfl
  rw [h2, h3] at h1
  exact h1

end GlobalTheory.ZH
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_rows_classZero_eq_invariant : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → t.τ.yy.ker = t.l.yy.ker ∧ (∀ α β, t.l.wt α = t.l.wt β ↔ ∃ m, α = β + S.N • m) ∧ Submodule.span (OO p) ((t.b.map (algebraMap _ (PadicAlgCl p))) '' {i | t.cls i = 0}) = Submodule.span (OO p) (Set.range fun i j => y₀ (algebraMap o S.R (S.proj (S.perp t.l.yy.ker) 0 j i))) := by
  atlas_forward_decl GlobalTheory.ZH.span_rows_class_zero
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.TestCrit

theorem exists_ne_zero_iff {O K k J : Type} [CommRing O] [Field K] [Algebra O K] [Field k] [Fintype J]
    [DecidableEq J] (hinj : Function.Injective (algebraMap O K)) (φ : O →+* k) (n A : Matrix J J O)
    (b : Matrix J J K) (hn : n.map (algebraMap O K) * b = 1) (I : Set J)
    (hs : Submodule.span O (b '' I) = Submodule.span O (Set.range fun i j => algebraMap O K (A i j)))
    (w : J → k) :
    (∃ i, ∑ j, φ (A i j) * (n.map φ).mulVec w j ≠ 0) ↔ ∃ i, i ∈ I ∧ w i ≠ 0 := by
  have hn' : b * n.map (algebraMap O K) = 1 := mul_eq_one_comm.1 hn
  have hb : ∀ i i', ∑ j, b i j * algebraMap O K (n j i') = (1 : Matrix J J K) i i' := fun i i' => by
    rw [← hn', Matrix.mul_apply]
    rfl
  have hsum : ∀ i, ∑ j, φ (A i j) * (n.map φ).mulVec w j = ∑ i', φ ((A * n) i i') * w i' := fun i => by
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul,
      Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
    exact Finset.sum_comm
  have hA : ∀ i i', algebraMap O K ((A * n) i i') = ∑ j, algebraMap O K (A i j) * algebraMap O K (n j i') :=
    fun i i' => by simp only [Matrix.mul_apply, map_sum, map_mul]
  simp only [hsum]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨i', -, hi'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    refine ⟨i', ?_, right_ne_zero_of_mul hi'⟩
    by_contra hI
    have h0 : ∀ a ∈ Submodule.span O (b '' I), ∑ j, a j * algebraMap O K (n j i') = 0 := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem _ h =>
        obtain ⟨i₀, hi₀, rfl⟩ := h
        rw [hb, Matrix.one_apply_ne]
        rintro rfl
        exact hI hi₀
      | zero => simp
      | add a a' _ _ ha ha' => simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, ha, ha', add_zero]
      | smul c a _ ha =>
        simp only [Pi.smul_apply, smul_mul_assoc]
        rw [← Finset.smul_sum, ha, smul_zero]
    have h1 := h0 (fun j => algebraMap O K (A i j)) (hs ▸ Submodule.subset_span ⟨i, rfl⟩)
    rw [← hA, map_eq_zero_iff _ hinj] at h1
    exact hi' (by rw [h1, map_zero, zero_mul])
  · rintro ⟨i, hI, hw⟩
    by_contra hz
    push_neg at hz
    have hm : b i ∈ Submodule.span O (Set.range fun i j => algebraMap O K (A i j)) :=
      hs ▸ Submodule.subset_span ⟨i, hI, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hm
    have h1 : ∀ i', (1 : Matrix J J O) i i' = ∑ a, c a * (A * n) a i' := fun i' => hinj (by
      have : algebraMap O K ((1 : Matrix J J O) i i') = (1 : Matrix J J K) i i' := by
        simp only [Matrix.one_apply, apply_ite (algebraMap O K), map_one, map_zero]
      have hc' : ∀ j, b i j = ∑ a, algebraMap O K (c a) * algebraMap O K (A a j) := fun j => by
        rw [← hc]
        simp only [Finset.sum_apply, Pi.smul_apply]
        simp only [Algebra.smul_def]
      rw [this, ← hb, map_sum]
      simp only [map_mul, hA, hc', Finset.sum_mul, Finset.mul_sum, _root_.mul_assoc]
      exact Finset.sum_comm)
    apply hw
    calc w i = ∑ i', φ ((1 : Matrix J J O) i i') * w i' := by
          simp [Matrix.one_apply, apply_ite φ]
      _ = ∑ a, φ (c a) * ∑ i', φ ((A * n) a i') * w i' := by
          simp only [h1, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, _root_.mul_assoc]
          exact Finset.sum_comm
      _ = 0 := by simp only [hz, mul_zero, Finset.sum_const_zero]

theorem le_preimage_G_iff_test : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ (x : Sp (kb p) ⟶ (Q.P.hom ⁻¹ᵁ Q.W tm.l).toScheme) (w : S.J → kb p), x ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = rPt p ≫ y → Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) (Q.σ tm.l) x ((tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)).mulVec w) → (⊤ ≤ (x ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ⁻¹ᵁ Q.G ↔ ∃ i, t.cls i = 0 ∧ w i ≠ 0) := by
  intro o Ω _ _ _ hA S ρ M U₀ EE hB Q p _ y y₀ t c tm _ x w hx hw
  have := hA.ft
  obtain ⟨ψ, hψ⟩ : ∃ ψ : o →+* OO p, y ≫ M.s = spMap ψ :=
    ⟨(Spec.preimage (y ≫ M.s)).hom, (Spec.map_preimage _).symm⟩
  have hg : (gPt p ≫ y) ≫ M.s = spMap ((OO p).subtype.comp ψ) := by
    rw [Category.assoc, hψ, ← Spec.map_comp]
    rfl
  have hy₀ : ∀ a : o, y₀ (algebraMap o S.R a) = (ψ a : PadicAlgCl p) := fun a =>
    (c.at_ _).trans (RatModel.val_algebraMap hg a)
  have hgy : gPt p ≫ y = (spMap (algebraMap (FractionRing t.u.V) (PadicAlgCl p)) ≫ c.yK) ≫ U₀.ι := by
    refine (congrArg (gPt p ≫ ·) c.fac.symm).trans ?_
    beta_reduce
    rw [Category.assoc, c.yK_fac, ← Category.assoc, ← Category.assoc, ← Spec.map_comp]
    congr 1
    exact Spec.map_comp (CommRingCat.ofHom (algebraMap t.u.V (FractionRing t.u.V)))
      (CommRingCat.ofHom (algebraMap (FractionRing t.u.V) (PadicAlgCl p)))
  have hU : Set.range (gPt p ≫ y) ⊆ U₀ := by
    rw [hgy]
    rintro _ ⟨a, rfl⟩
    exact ((spMap (algebraMap (FractionRing t.u.V) (PadicAlgCl p)) ≫ c.yK) a).2
  have hcen : M.Cen U₀ (y (cPt p)) y := ⟨rfl, hU⟩
  have hcl := GlobalTheory.ZH.isClosed_centre o Ω M U₀ _ p y hcen
  obtain ⟨hker, -, hspan⟩ := GlobalTheory.T.span_rows_classZero_eq_invariant o Ω S ρ p y₀ t fun a => by
    rw [hy₀]
    exact (mem_OO_iff _).1 (ψ a).2
  have hT : S.TT M (y (cPt p)) = S.perp t.l.yy.ker := by
    rw [ThetaSys.TT, hB.atTest _ p y y₀ t.τ hcen c.at_, hker]
  have hW : ⊤ ≤ y ⁻¹ᵁ Q.W tm.l := (CrdCalc.top_le_iff y _).2 tm.mem
  have hrange : Set.range ((x ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ≫ Q.P.hom) = {y (cPt p)} := by
    rw [Category.assoc, hx, RatModel.range_eq_singleton _ (IsLocalRing.closedPoint _)]
    congr 1
    exact congrArg y (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))
  have hs : (x ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ≫ Q.P.hom ≫ M.s =
      spMap ((IsLocalRing.residue (OO p)).comp ψ) := by
    rw [← Category.assoc, Category.assoc x, hx, Category.assoc, hψ, ← Spec.map_comp]
    rfl
  have hcrd := Q.rel tm.l _ x _ hw
  rw [OpenPart.le_preimage_G_iff o Ω S ρ M U₀ EE hB Q _ _ _ _ _ hrange (Or.inl hcl) hs hcrd, hT, hx,
    Matrix.mulVec_mulVec]
  set C : Matrix S.J S.J (OO p) := (Q.c tm.l).map (valR y (Q.W tm.l)) with hC
  have hn : (Q.c tm.l).map (valR (rPt p ≫ y) (Q.W tm.l)) *
      (tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)) =
      (C * tm.m.map t.u.j).map (IsLocalRing.residue (OO p)) := by
    rw [Matrix.map_mul]
    congr 1
    ext i j
    exact (CrdCalc.valR_spMap _ y _ hW).2 _
  rw [hn]
  obtain ⟨hWg, hvg⟩ := CrdCalc.valR_spMap (OO p).subtype y _ hW
  have hWg' : Set.range (gPt p ≫ y) ⊆ Q.W tm.l := (top_le_preimage_iff _ _).1 hWg
  set ξ := (gPt p ≫ y) (IsLocalRing.closedPoint _) with hξ
  have hr : Set.range (gPt p ≫ y) = {ξ} := RatModel.range_eq_singleton _ _
  have hξW : ξ ∈ Q.W tm.l := hWg' ⟨_, rfl⟩
  have hξU : ξ ∈ U₀ := hU ⟨_, rfl⟩
  have hBm : ∀ i j, Q.B tm.l i j ∈ M.O ξ := fun i => by
    have h1 : Q.B tm.l i ∈ EE.E ξ := by
      rw [Q.basis _ _ hξW]
      exact Submodule.subset_span ⟨i, rfl⟩
    rw [hB.ee.1 ξ hξU] at h1
    exact (RatModel.Lat.mem_const_iff M).1 h1
  have hinv : C.map (algebraMap (OO p) (PadicAlgCl p)) * (Q.B tm.l).map (M.val (gPt p ≫ y)) = 1 := by
    let c' : Matrix S.J S.J (M.O ξ) := fun i j => ⟨_, RatModel.valF_mem_O hξW (Q.c tm.l i j)⟩
    let B' : Matrix S.J S.J (M.O ξ) := fun i j => ⟨_, hBm i j⟩
    have h1 : c' * B' = 1 := by
      apply Matrix.map_injective (f := (M.O ξ).val.toRingHom) Subtype.val_injective
      beta_reduce
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact Q.c_inv tm.l
    have h2 := congrArg (fun N => N.map (RatModel.valHom _ _ hr)) h1
    beta_reduce at h2
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    rw [← h2]
    congr 1
    ext i j
    exact ((RatModel.val_valF hWg' _).trans (hvg _)).symm
  refine exists_ne_zero_iff Subtype.val_injective (IsLocalRing.residue (OO p)) _
    (fun i j => ψ (S.proj (S.perp t.l.yy.ker) 0 j i)) (t.b.map (algebraMap _ (PadicAlgCl p))) ?_
    {i | t.cls i = 0} ?_ w
  · rw [Matrix.map_mul, Matrix.mul_assoc, ← hinv, tm.m_eq]
    rfl
  · rw [hspan]
    simp only [hy₀]
    rfl

end GlobalTheory.ZH.TestCrit
end
