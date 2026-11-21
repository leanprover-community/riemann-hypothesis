import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.WeilBound.CoreStatements.HodgeTatePoints.GenfibMap
import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLCentre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLPulllocCentre
import Development.WeilBound.CoreStatements.HodgeTatePoints.MaSerre
import Development.WeilBound.CoreStatements.HodgeTatePoints.InChartOfMemCtrSet
import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLMorph
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModelNonemptyStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.FinClosure
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralClosureChartSpan
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralOverLocalizationScaledStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalSubringIntegralClosureMax
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MaximalIdealMembershipOfLocal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeMemIffNotUnitLocalizationStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.MaBase
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingModelChartCompatStatement

section
noncomputable section

namespace PositivityTheory.HtPt.Mc

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem cramer_sub : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (A : Subring Ω) (r : ℕ) (b : Module.Basis (Fin r) Ω E) (κ : Type) (z : κ → E) (c₀ : Fin r → κ), b.det (z ∘ c₀) ≠ 0 → (∀ c : Fin r → κ, b.det (z ∘ c) / b.det (z ∘ c₀) ∈ A) → LinearIndependent Ω (z ∘ c₀) ∧ Submodule.span A (Set.range z) = Submodule.span A (Set.range (z ∘ c₀)) := by
  intro Ω _ E _ _ A r b κ z c₀ h0 h
  classical
  obtain ⟨li, sp⟩ := (Module.Basis.is_basis_iff_det b).2 (isUnit_iff_ne_zero.2 h0)
  refine ⟨li, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)⟩
  · rintro _ ⟨k, rfl⟩
    let B := Module.Basis.mk li sp.ge
    have hc : ∀ l, B.repr (z k) l ∈ A := by
      intro l
      have e := LinearMap.congr_fun (b.det_smul_mk_coord_eq_det_update li sp.ge l) (z k)
      have e2 : b.det (z ∘ c₀) * B.repr (z k) l = b.det (z ∘ Function.update c₀ l k) := by
        rw [Function.comp_update]
        exact e
      have e3 : B.repr (z k) l = b.det (z ∘ Function.update c₀ l k) / b.det (z ∘ c₀) := by
        rw [← e2, mul_div_cancel_left₀ _ h0]
      rw [e3]
      exact h _
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun l => ⟨_, hc l⟩, ?_⟩
    have := B.sum_repr (z k)
    simp only [B, Module.Basis.mk_apply] at this
    exact this
  · rintro _ ⟨i, rfl⟩
    exact ⟨c₀ i, rfl⟩

section
variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] (A : Subring Ω) {r : ℕ}

theorem repr_mem {ι : Type} (B : Module.Basis ι Ω E) {v : E} (hv : v ∈ Submodule.span A (Set.range B)) (j : ι) :
    B.repr v j ∈ A := by
  classical
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [B.repr_self, Finsupp.single_apply]
    split_ifs
    exacts [A.one_mem, A.zero_mem]
  | zero => simp
  | add x y _ _ hx hy => simpa using A.add_mem hx hy
  | smul a x _ hx =>
    have : B.repr (a • x) j = (a : Ω) * B.repr x j := by
      show B.repr ((a : Ω) • x) j = _
      simp
    rw [this]
    exact A.mul_mem a.2 hx

theorem det_mem (B : Module.Basis (Fin r) Ω E) (v : Fin r → E)
    (hv : ∀ i, v i ∈ Submodule.span A (Set.range B)) : B.det v ∈ A := by
  rw [Module.Basis.det_apply, Matrix.det_apply']
  refine A.sum_mem fun s _ => A.mul_mem (intCast_mem _ _) (A.prod_mem fun i _ => ?_)
  exact repr_mem A B (hv _) _

theorem det_mem_span (B : Module.Basis (Fin r) Ω E) {κ : Type} (z : κ → E) (v : Fin r → E)
    (hv : ∀ i, v i ∈ Submodule.span A (Set.range z)) :
    B.det v ∈ Submodule.span A (Set.range fun c : Fin r → κ => B.det (z ∘ c)) := by
  classical
  choose c hc using fun i => Finsupp.mem_span_range_iff_exists_finsupp.1 (hv i)
  have e : v = fun i => ∑ k ∈ (c i).support, ((c i k : A) : Ω) • z k := funext fun i => (hc i).symm
  have e2 := B.det.toMultilinearMap.map_sum_finset (fun i k => ((c i k : A) : Ω) • z k) fun i => (c i).support
  rw [e]
  refine (show B.det _ = _ from e2) ▸ Submodule.sum_mem _ fun s _ => ?_
  rw [MultilinearMap.map_smul_univ]
  have : (∏ i, ((c i (s i) : A) : Ω)) = ((∏ i, c i (s i) : A) : Ω) := by simp
  rw [this]
  exact Submodule.smul_mem _ (∏ i, c i (s i)) (Submodule.subset_span ⟨s, rfl⟩)

end

theorem frame_plucker : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (A : Subring Ω) [IsLocalRing A] (r : ℕ) (b : Module.Basis (Fin r) Ω E) (κ : Type) (z : κ → E) (f : Fin r → E), LinearIndependent Ω f → Submodule.span A (Set.range z) = Submodule.span A (Set.range f) → ∃ c₀ : Fin r → κ, b.det (z ∘ c₀) ≠ 0 ∧ ∀ c : Fin r → κ, b.det (z ∘ c) / b.det (z ∘ c₀) ∈ A := by
  intro Ω _ E _ _ A _ r b κ z f li h
  classical
  haveI := Module.Finite.of_basis b
  have sp : Submodule.span Ω (Set.range f) = ⊤ :=
    li.span_eq_top_of_card_eq_finrank' (by rw [Module.finrank_eq_card_basis b])
  let B := Module.Basis.mk li sp.ge
  have hB : (B : Fin r → E) = f := Module.Basis.coe_mk _ _
  have hd : b.det f ≠ 0 := ((Module.Basis.is_basis_iff_det b).1 ⟨li, sp⟩).ne_zero
  have hbB : ∀ v, b.det v = b.det f * B.det v := fun v => by
    conv_lhs => rw [b.det.eq_smul_basis_det B, hB]
    rfl
  have hA : ∀ c : Fin r → κ, B.det (z ∘ c) ∈ A := fun c =>
    det_mem A B _ fun i => by rw [hB, ← h]; exact Submodule.subset_span ⟨c i, rfl⟩
  have h1 := det_mem_span A B z f fun i => by rw [h]; exact Submodule.subset_span ⟨i, rfl⟩
  rw [← hB, B.det_self] at h1
  have : ∃ c₀, IsUnit (⟨_, hA c₀⟩ : A) := by
    by_contra hn
    push Not at hn
    have : Submodule.span A (Set.range fun c : Fin r → κ => B.det (z ∘ c)) ≤
        Submodule.map (Algebra.linearMap A Ω) (IsLocalRing.maximalIdeal A) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨c, rfl⟩
      exact ⟨⟨_, hA c⟩, hn c, rfl⟩
    obtain ⟨y, hy, e⟩ := this h1
    have : y = 1 := Subtype.ext e
    exact hy (this ▸ isUnit_one)
  obtain ⟨c₀, hu⟩ := this
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have hw' : B.det (z ∘ c₀) * (w : Ω) = 1 := congrArg Subtype.val hw
  refine ⟨c₀, by rw [hbB]; exact mul_ne_zero hd (left_ne_zero_of_mul_eq_one hw'), fun c => ?_⟩
  rw [hbB, hbB (z ∘ c₀), mul_div_mul_left _ _ hd, div_eq_mul_inv, ← eq_inv_of_mul_eq_one_right hw']
  exact A.mul_mem (hA c) w.2

end PositivityTheory.HtPt.Mc
end
end

section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

noncomputable section

namespace PositivityTheory.HtPt.Mb.LFlatten.Flatten

section Linear

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]

theorem det_smul_cols {W : Type} [AddCommGroup W] [Module Ω W] {r : ℕ} (b : Module.Basis (Fin r) Ω W) (t : Ω)
    (g : Fin r → W) : b.det (fun k => t • g k) = t ^ r * b.det g := by
  have h := b.det.toMultilinearMap.map_smul_univ (fun _ => t) g
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h

theorem span_val_eq_iff (A : Subring Ω) (V : Submodule Ω E) {ι ι' : Type} (g : ι → V) (g' : ι' → V) :
    Submodule.span A (Set.range fun k => (g k : E)) = Submodule.span A (Set.range fun k => (g' k : E)) ↔
      Submodule.span A (Set.range g) = Submodule.span A (Set.range g') := by
  let φ : V →ₗ[A] E := V.subtype.restrictScalars A
  have hφ : Function.Injective φ := Subtype.val_injective
  have h : ∀ {ι : Type} (g : ι → V),
      Submodule.span A (Set.range fun k => (g k : E)) = (Submodule.span A (Set.range g)).map φ := by
    intro ι g
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [h, h]
  exact (Submodule.map_injective_of_injective hφ).eq_iff

theorem exists_det_ne {W : Type} [AddCommGroup W] [Module Ω W] {r n : ℕ} (b : Module.Basis (Fin r) Ω W)
    (z : Fin n → W) (hs : Submodule.span Ω (Set.range z) = ⊤) : ∃ c : Fin r → Fin n, b.det (z ∘ c) ≠ 0 := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' Ω z
  rw [hs] at hspan
  have : Finite κ := Finite.of_injective a ha
  have := Fintype.ofFinite κ
  let B : Module.Basis κ Ω W := Module.Basis.mk hli hspan.ge
  have hcard : Fintype.card κ = r := by
    have h1 := Module.finrank_eq_card_basis B
    have h2 := Module.finrank_eq_card_basis b
    rw [h1] at h2
    simpa using h2
  let e : Fin r ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ?_⟩
  have hli' : LinearIndependent Ω (z ∘ (a ∘ e)) := hli.comp e e.injective
  have hsp' : Submodule.span Ω (Set.range (z ∘ (a ∘ e))) = ⊤ := by
    rw [← Function.comp_assoc, EquivLike.range_comp]
    exact hspan
  have hu := b.isUnit_det (Module.Basis.mk hli' hsp'.ge)
  rw [Module.Basis.coe_mk] at hu
  exact hu.ne_zero

theorem dominant_minor (A : Subring Ω) [IsLocalRing A] (V : Submodule Ω E) {r r' n : ℕ}
    (b₀ : Module.Basis (Fin r) Ω V) (z : Fin n → V) {t : Ω} (ht : t ≠ 0) (b : Fin r' → E)
    (hb : LinearIndependent Ω b) (hV : Submodule.span Ω (Set.range b) = V)
    (hsp : Submodule.span A (Set.range fun k => t • (z k : E)) = Submodule.span A (Set.range b)) :
    ∃ l : Fin r → Fin n, b₀.det (z ∘ l) ≠ 0 ∧ ∀ c : Fin r → Fin n, b₀.det (z ∘ c) / b₀.det (z ∘ l) ∈ A := by
  have hbV : ∀ k, b k ∈ V := fun k => by
    rw [← hV]
    exact Submodule.subset_span ⟨k, rfl⟩
  let bV : Fin r' → V := fun k => ⟨b k, hbV k⟩
  have hliV : LinearIndependent Ω bV := LinearIndependent.of_comp V.subtype hb
  have hspV : Submodule.span Ω (Set.range bV) = ⊤ := by
    apply Submodule.map_injective_of_injective V.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top]
    exact hV
  have hrr : r' = r := by
    have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hliV hspV.ge)
    have h2 := Module.finrank_eq_card_basis b₀
    rw [h1] at h2
    simpa using h2
  subst hrr
  have hsp' : Submodule.span A (Set.range fun k => t • z k) = Submodule.span A (Set.range bV) :=
    (span_val_eq_iff A V (fun k => t • z k) bV).1 hsp
  obtain ⟨l, hl, hl2⟩ := PositivityTheory.HtPt.Mc.frame_plucker Ω V A r' b₀ (Fin n) (fun k => t • z k) bV hliV hsp'
  have hdet : ∀ c : Fin r' → Fin n, b₀.det ((fun k => t • z k) ∘ c) = t ^ r' * b₀.det (z ∘ c) :=
    fun c => det_smul_cols b₀ t (z ∘ c)
  have htr : t ^ r' ≠ 0 := pow_ne_zero _ ht
  refine ⟨l, ?_, fun c => ?_⟩
  · intro h0
    apply hl
    rw [hdet, h0, mul_zero]
  · have h3 := hl2 c
    rwa [hdet, hdet, mul_div_mul_left _ _ htr] at h3

variable {Ω' : Type} [Field Ω'] {F : Type} [AddCommGroup F] [Module Ω' F]

theorem span_image_span (i : Ω →+* Ω') (j : E →+ F) (hj : ∀ (a : Ω) (e : E), j (a • e) = i a • j e)
    (A₀ : Subring Ω) (A : Subring Ω') (hA : ∀ a ∈ A₀, i a ∈ A) (S : Set E) :
    Submodule.span A (j '' ((Submodule.span A₀ S : Submodule A₀ E) : Set E)) = Submodule.span A (j '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    rw [SetLike.mem_coe] at he
    induction he using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add y y' _ _ hy hy' =>
      rw [map_add]
      exact Submodule.add_mem _ hy hy'
    | smul a y _ hy =>
      have e1 : j (a • y) = (⟨i a, hA a a.2⟩ : A) • j y := by
        show j ((a : Ω) • y) = i a • j y
        exact hj a y
      rw [e1]
      exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem ext_basis (i : Ω →+* Ω') (j : E →+ F) (hj : IsExtOver i j) (V : Submodule Ω E) {r : ℕ}
    (b₀ : Module.Basis (Fin r) Ω V) :
    ∃ (b' : Module.Basis (Fin r) Ω' (Submodule.span Ω' (j '' (V : Set E))))
      (J : V →+ Submodule.span Ω' (j '' (V : Set E))),
      (∀ e, (J e : F) = j e) ∧ ∀ g : Fin r → V, b'.det (J ∘ g) = i (b₀.det g) := by
  obtain ⟨hsm, hli⟩ := hj
  have hmem : ∀ e : V, j e ∈ Submodule.span Ω' (j '' (V : Set E)) := fun e =>
    Submodule.subset_span ⟨e, e.2, rfl⟩
  let J : V →+ Submodule.span Ω' (j '' (V : Set E)) :=
    { toFun := fun e => ⟨j e, hmem e⟩
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  have hJs : ∀ (c : Ω) (v : V), J (c • v) = i c • J v := fun c v => Subtype.ext (hsm c v)
  have hJsum : ∀ v : V, J v = ∑ k, i (b₀.repr v k) • J (b₀ k) := by
    intro v
    conv_lhs => rw [← b₀.sum_repr v]
    rw [map_sum]
    simp only [hJs]
  have hJli : LinearIndependent Ω' (J ∘ b₀) := by
    apply LinearIndependent.of_comp (Submodule.span Ω' (j '' (V : Set E))).subtype
    exact hli r (fun k => (b₀ k : E)) (b₀.linearIndependent.map' V.subtype V.ker_subtype)
  have hJsp : ⊤ ≤ Submodule.span Ω' (Set.range (J ∘ b₀)) := by
    rintro ⟨y, hy⟩ -
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨e, he, rfl⟩ := hy
      have e1 : (⟨j e, hmem ⟨e, he⟩⟩ : Submodule.span Ω' (j '' (V : Set E))) = J ⟨e, he⟩ := rfl
      rw [e1, hJsum]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul a y _ hy => exact Submodule.smul_mem _ a hy
  let b' := Module.Basis.mk hJli hJsp
  have hb' : ∀ k, b' k = J (b₀ k) := fun k => Module.Basis.mk_apply _ _ _
  have hrep : ∀ (v : V) (a : Fin r), b'.repr (J v) a = i (b₀.repr v a) := by
    intro v a
    have h1 : J v = ∑ k, i (b₀.repr v k) • b' k := by
      rw [hJsum v]
      simp only [hb']
    rw [h1, Module.Basis.repr_sum_self]
  refine ⟨b', J, fun e => rfl, fun g => ?_⟩
  rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]
  congr 1
  ext a c
  simp only [Module.Basis.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Function.comp, hrep]

end Linear

theorem reg_near {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) {ι : Type}
    [Finite ι] (a : ι → Ω) (h : ∀ t, a t ∈ regAt ξ p) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ∀ t, a t ∈ regAt ξ q := by
  choose U hU using fun t => PositivityTheory.HtPt.Ma.reg_open X Ω ξ p (a t) (h t)
  refine ⟨⟨⋂ t, (U t : Set X), isOpen_iInter_of_finite fun t => (U t).isOpen⟩, ?_, ?_⟩
  · exact Set.mem_iInter.2 fun t => (hU t).1
  · intro q hq t
    exact (hU t).2 q (Set.mem_iInter.1 hq t)

theorem vb_on {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
    (M : PModel o x) {E : Type} [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E) (V : Submodule Ω E)
    (hcoh : L.IsCohOn Set.univ) {d n r : ℕ} (b₀ : Module.Basis (Fin r) Ω V) (z : Fin n → V)
    (hz : ∀ c (p : Cpt M.ξ), InChart M.ξ x c p →
      L p = Submodule.span (regAt M.ξ p) (Set.range fun k => (x c ^ d)⁻¹ • (z k : E)))
    {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω')
    {F : Type} [AddCommGroup F] [Module Ω' F] (j : E →+ F) (hj : IsExtOver i j) :
    (L.pullLoc ξ' i j).IsVBOn
      {p' | p' ∈ ctrSet o x i ξ' ∧ ∃ l, InChart ξ' (fun l => i (b₀.det (z ∘ l))) l p'} r
      (Submodule.span Ω' (j '' (V : Set E))) := by
  obtain ⟨b', J, hJ, hdetJ⟩ := ext_basis i j hj V b₀
  intro p' hp'
  obtain ⟨hp'c, l, hl⟩ := hp'
  obtain ⟨p₀, ⟨hreg, -⟩, -, -⟩ :=
    PositivityTheory.HtPt.Mb.LCentre.Centre.exists_centre o Ω κ x M X' Ω' ξ' i p' hp'c
  obtain ⟨c, hc⟩ := M.tie.cover p₀
  have hxc : x c ≠ 0 := hc.1
  obtain ⟨U, hpU, hU⟩ := reg_near ξ' p'
    (Sum.elim (fun c' : Fin r → Fin n => i (b₀.det (z ∘ c')) / i (b₀.det (z ∘ l)))
      (fun k : κ => i (x k / x c)))
    (by
      rintro (c' | k)
      · exact hl.2 c'
      · exact hreg _ (hc.2 k))
  let w : Fin n → Submodule.span Ω' (j '' (V : Set E)) := fun k => i (x c ^ d)⁻¹ • J (z k)
  have hcoe : ∀ k, ((w k : Submodule.span Ω' (j '' (V : Set E))) : F) = i (x c ^ d)⁻¹ • j (z k) := by
    intro k
    simp only [w, Submodule.coe_smul, hJ]
  have hdw : ∀ c' : Fin r → Fin n, b'.det (w ∘ c') = i (x c ^ d)⁻¹ ^ r * i (b₀.det (z ∘ c')) := by
    intro c'
    rw [← hdetJ]
    exact det_smul_cols b' (i (x c ^ d)⁻¹) (J ∘ (z ∘ c'))
  have hit : i (x c ^ d)⁻¹ ^ r ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero i).2 (inv_ne_zero (pow_ne_zero _ hxc)))
  have hwl : b'.det (w ∘ l) ≠ 0 := by
    rw [hdw]
    exact mul_ne_zero hit hl.1
  have hratio : ∀ c' : Fin r → Fin n, b'.det (w ∘ c') / b'.det (w ∘ l) =
      i (b₀.det (z ∘ c')) / i (b₀.det (z ∘ l)) := by
    intro c'
    rw [hdw, hdw, mul_div_mul_left _ _ hit]
  have hbasis : Submodule.span Ω' (Set.range (w ∘ l)) = ⊤ := by
    exact ((Module.Basis.is_basis_iff_det b').2 (isUnit_iff_ne_zero.2 hwl)).2
  refine ⟨U, hpU, fun k => i (x c ^ d)⁻¹ • j (z (l k)), ?_, ?_⟩
  · have e1 : (Set.range fun k => i (x c ^ d)⁻¹ • j (z (l k))) =
        (Submodule.span Ω' (j '' (V : Set E))).subtype '' Set.range (w ∘ l) := by
      rw [← Set.range_comp]
      congr 1
      funext k
      exact (hcoe (l k)).symm
    rw [e1, ← Submodule.map_span, hbasis, Submodule.map_subtype_top]
  · intro q' hq' hqU
    obtain ⟨hq'c, -⟩ := hq'
    obtain ⟨q₀, hq₀, -, hchart⟩ :=
      PositivityTheory.HtPt.Mb.LCentre.Centre.exists_centre o Ω κ x M X' Ω' ξ' i q' hq'c
    have hqa := hU q' hqU
    have hq0 : InChart M.ξ x c q₀ := hchart c hxc fun k => hqa (Sum.inr k)
    have hcr := PositivityTheory.HtPt.Mc.cramer_sub Ω' _ (regAt ξ' q') r b' (Fin n) w l hwl
      (fun c' => by rw [hratio]; exact hqa (Sum.inl c'))
    show LinearIndependent Ω' _ ∧ _
    refine ⟨?_, ?_⟩
    · have h5 := hcr.1.map' (Submodule.span Ω' (j '' (V : Set E))).subtype (Submodule.ker_subtype _)
      have e4 : (fun k => i (x c ^ d)⁻¹ • j (z (l k))) =
          ⇑(Submodule.span Ω' (j '' (V : Set E))).subtype ∘ w ∘ l := by
        funext k
        exact (hcoe (l k)).symm
      rw [e4]
      exact h5
    · rw [PositivityTheory.HtPt.Mb.pullloc_centre o Ω κ x M E L X' Ω' ξ' i F j q₀ q' hcoh hq₀, hz c q₀ hq0,
        span_image_span i j hj.1 (regAt M.ξ q₀) (regAt ξ' q') hq₀.1, ← Set.range_comp]
      have e2 := (span_val_eq_iff (regAt ξ' q') (Submodule.span Ω' (j '' (V : Set E))) w (w ∘ l)).2 hcr.2
      have e3 : (⇑j ∘ fun k => (x c ^ d)⁻¹ • (z k : E)) = fun k => ((w k : _) : F) := by
        funext k
        rw [hcoe]
        exact hj.1 _ _
      rw [e3, e2]
      simp only [Function.comp_apply, hcoe]

theorem plucker_block (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω)
    (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E) (V : Submodule Ω E)
    [FiniteDimensional Ω V] (hcoh : L.IsCohOn Set.univ) (hgen : ∀ p, Submodule.span Ω (L p : Set E) = V) :
    ∃ (κ' : Type) (_ : Finite κ') (w : κ' → Ω), (∃ l, w l ≠ 0) ∧
      (∀ p : Cpt M.ξ, (∃ (r : ℕ) (b : Fin r → E), L.IsFrameAt b p) → ∃ l, InChart M.ξ w l p) ∧
      ∀ (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω')
        (F : Type) [AddCommGroup F] [Module Ω' F] (j : E →+ F), IsExtOver i j →
        (L.pullLoc ξ' i j).IsVBOn {p' | p' ∈ ctrSet o x i ξ' ∧ ∃ l, InChart ξ' (fun l => i (w l)) l p'}
          (Module.finrank Ω V) (Submodule.span Ω' (j '' (V : Set E))) := by
  obtain ⟨d, n, z, hz⟩ := PositivityTheory.HtPt.Ma.serre o Ω κ x M E L hcoh
  let p₀ : Cpt M.ξ := ⟨genPt M.ξ, specializes_refl _⟩
  obtain ⟨c₀, hc₀⟩ := M.tie.cover p₀
  have hzV : ∀ k, z k ∈ V := by
    intro k
    rw [← hgen p₀]
    have h1 : (x c₀ ^ d)⁻¹ • z k ∈ L p₀ := by
      rw [hz c₀ p₀ hc₀]
      exact Submodule.subset_span ⟨k, rfl⟩
    have h2 : (x c₀ ^ d)⁻¹ • z k ∈ Submodule.span Ω (L p₀ : Set E) := Submodule.subset_span h1
    have h3 := Submodule.smul_mem (Submodule.span Ω (L p₀ : Set E)) (x c₀ ^ d) h2
    rwa [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hc₀.1), one_smul] at h3
  have hspanE : Submodule.span Ω (Set.range z) = V := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hzV k
    · rw [← hgen p₀, hz c₀ p₀ hc₀, Submodule.span_span_of_tower, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let zV : Fin n → V := fun k => ⟨z k, hzV k⟩
  have hspanV : Submodule.span Ω (Set.range zV) = ⊤ := by
    apply Submodule.map_injective_of_injective V.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top]
    exact hspanE
  let b₀ := Module.finBasis Ω V
  refine ⟨Fin (Module.finrank Ω V) → Fin n, inferInstance, fun l => b₀.det (zV ∘ l), ?_, ?_, ?_⟩
  · exact exists_det_ne b₀ zV hspanV
  · rintro p ⟨r', b, hbli, hbL⟩
    obtain ⟨c, hc⟩ := M.tie.cover p
    have hV' : Submodule.span Ω (Set.range b) = V := by
      rw [← hgen p, hbL, Submodule.span_span_of_tower]
    have hloc : IsLocalRing (regAt M.ξ p) := (PositivityTheory.HtPt.Ma.reg_local _ _ M.ξ).1 p
    have hsp : Submodule.span (regAt M.ξ p) (Set.range fun k => (x c ^ d)⁻¹ • ((zV k : V) : E)) =
        Submodule.span (regAt M.ξ p) (Set.range b) := by
      rw [← hbL]
      exact (hz c p hc).symm
    obtain ⟨l, hl, hl2⟩ := dominant_minor (regAt M.ξ p) V b₀ zV (inv_ne_zero (pow_ne_zero _ hc.1)) b hbli hV' hsp
    exact ⟨l, show _ ∧ _ from ⟨hl, hl2⟩⟩
  · intro X' Ω' _ ξ' i F _ _ j hj
    exact vb_on M L V hcoh b₀ zV (fun c p hc => hz c p hc) ξ' i j hj

end PositivityTheory.HtPt.Mb.LFlatten.Flatten

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

theorem PositivityTheory.HtPt.Mb.flatten : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E) (V : Submodule Ω E) [FiniteDimensional Ω V], L.IsCohOn Set.univ → (∀ p, Submodule.span Ω (L p : Set E) = V) → ∃ (κ' : Type) (_ : Finite κ') (w : κ' → Ω), (∃ l, w l ≠ 0) ∧ (∀ p : Cpt M.ξ, (∃ (r : ℕ) (b : Fin r → E), L.IsFrameAt b p) → ∃ l, InChart M.ξ w l p) ∧ ∀ (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (F : Type) [AddCommGroup F] [Module Ω' F] (j : E →+ F), IsExtOver i j → (L.pullLoc ξ' i j).IsVBOn {p' | p' ∈ ctrSet o x i ξ' ∧ ∃ l, InChart ξ' (fun l => i (w l)) l p'} (Module.finrank Ω V) (Submodule.span Ω' (j '' (V : Set E))) :=
  @PositivityTheory.HtPt.Mb.LFlatten.Flatten.plucker_block
end
end

section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LJoinExists

theorem join_exists : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (i : Ω →+* Ω') (κ' : Type) [Finite κ'] (w : κ' → Ω'), (∀ a : o, i (algebraMap o Ω a) = algebraMap o Ω' a) → (∃ l, w l ≠ 0) → Subfield.closure (Set.range i ∪ {a | ∃ l l', a = w l / w l'}) = ⊤ → ∃ (M' : PModel o (joinCo i x w)) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f i := by
  intro o _ Ω _ _ κ _ x M Ω' _ _ i κ' _ w hi ⟨l, hl⟩ hcl
  let p : Cpt M.ξ := ⟨genPt M.ξ, specializes_rfl⟩
  obtain ⟨c, hc⟩ := M.tie.cover p
  have hic : i (x c) ≠ 0 := (map_ne_zero i).2 hc.1
  have hJ : joinCo i x w (c, l) ≠ 0 := mul_ne_zero hic hl
  have hgen : ∀ j l', joinCo i x w (j, l') / joinCo i x w (c, l) ∈ chRing o (joinCo i x w) (c, l) :=
    fun j l' => Algebra.subset_adjoin ⟨(j, l'), rfl⟩
  have hmap : ∀ a ∈ chRing o x c, i a ∈ chRing o (joinCo i x w) (c, l) := by
    intro a ha
    have ha' : a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := ha
    induction ha' using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      have : i (x j / x c) = joinCo i x w (j, l) / joinCo i x w (c, l) := by
        simp only [joinCo, map_div₀]
        rw [mul_div_mul_right _ _ hl]
      rw [this]
      exact hgen _ _
    | algebraMap r =>
      rw [hi]
      exact Subalgebra.algebraMap_mem _ r
    | add y z _ _ hy hz =>
      rw [map_add]
      exact add_mem (hy (by assumption)) (hz (by assumption))
    | mul y z _ _ hy hz =>
      rw [map_mul]
      exact mul_mem (hy (by assumption)) (hz (by assumption))
  have hAF : ∀ a ∈ chRing o (joinCo i x w) (c, l),
      a ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') :=
    fun a ha => Subfield.subset_closure ha
  have hiF : ∀ a : Ω, i a ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') := by
    intro a
    have h2 := (PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c p hc).2
    have key : ∀ b ∈ regAt M.ξ p, i b ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') := by
      intro b hb
      obtain ⟨s, hs, t, ht, -, rfl⟩ := (h2 b).1 hb
      rw [map_div₀]
      exact div_mem (hAF _ (hmap _ hs)) (hAF _ (hmap _ ht))
    obtain ⟨u, hu, v, hv, -, rfl⟩ := (PositivityTheory.HtPt.Ma.reg_local M.X Ω M.ξ).2.2 M.tie.gen p a
    rw [map_div₀]
    exact div_mem (key u hu) (key v hv)
  have hw : ∀ l', w l' / w l ∈ chRing o (joinCo i x w) (c, l) := by
    intro l'
    have : w l' / w l = joinCo i x w (c, l') / joinCo i x w (c, l) := by
      simp only [joinCo]
      rw [mul_div_mul_left _ _ hic]
    rw [this]
    exact hgen _ _
  have hle : Subfield.closure (Set.range i ∪ {a | ∃ l l', a = w l / w l'}) ≤
      Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') := by
    refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨a, rfl⟩
      exact hiF a
    · rintro _ ⟨a, b, rfl⟩
      rw [← div_div_div_cancel_right₀ hl (w a) (w b)]
      exact div_mem (hAF _ (hw a)) (hAF _ (hw b))
  have hfrac : ∀ a : Ω', ∃ u ∈ chRing o (joinCo i x w) (c, l), ∃ v ∈ chRing o (joinCo i x w) (c, l),
      a = u / v := by
    intro a
    have ha : a ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') :=
      hle (by rw [hcl]; exact Subfield.mem_top a)
    obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.1 ha
    have hs : Subring.closure (chRing o (joinCo i x w) (c, l) : Set Ω') =
        (chRing o (joinCo i x w) (c, l)).toSubring :=
      Subring.closure_eq (chRing o (joinCo i x w) (c, l)).toSubring
    rw [hs] at hy hz
    exact ⟨y, hy, z, hz, rfl⟩
  obtain ⟨M'⟩ := GlobalTheory.T.projective_model_nonempty o Ω' (κ × κ') (joinCo i x w) ⟨(c, l), hJ, hfrac⟩
  have hctr : ∀ p', p' ∈ ctrSet o x i M'.ξ := fun p' => (PositivityTheory.HtPt.Mb.join_charts o Ω κ κ' x Ω' i w M' hi p').1
  obtain ⟨f, hf, -⟩ := PositivityTheory.HtPt.Mb.morph o Ω κ x M o Ω' (κ × κ') (joinCo i x w) M' i hctr
  exact ⟨M', f, hf⟩

end PositivityTheory.HtPt.Mb.LJoinExists

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

theorem PositivityTheory.HtPt.Mb.join_exists : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (i : Ω →+* Ω') (κ' : Type) [Finite κ'] (w : κ' → Ω'), (∀ a : o, i (algebraMap o Ω a) = algebraMap o Ω' a) → (∃ l, w l ≠ 0) → Subfield.closure (Set.range i ∪ {a | ∃ l l', a = w l / w l'}) = ⊤ → ∃ (M' : PModel o (joinCo i x w)) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f i :=
  @PositivityTheory.HtPt.Mb.LJoinExists.join_exists
end

section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LJoinIso.JoinIso

theorem chRing_mem {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {ι : Type} {J : ι → Ω} {d : ι}
    {S : Subring Ω} (ho : ∀ r : o, algebraMap o Ω r ∈ S) (h : ∀ q, J q / J d ∈ S) :
    ∀ a ∈ chRing o J d, a ∈ S := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨q, rfl⟩ := hy
    exact h q
  | algebraMap r => exact ho r
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2

theorem eq_of_units {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
    (M : PModel o x) {c : κ} {p q : Cpt M.ξ} (hp : InChart M.ξ x c p) (hq : InChart M.ξ x c q)
    (h : ∀ u ∈ chRing o x c, unitAt M.ξ p u ↔ unitAt M.ξ q u) : p = q := by
  have hle : ∀ {p q : Cpt M.ξ}, InChart M.ξ x c p → InChart M.ξ x c q →
      (∀ u ∈ chRing o x c, unitAt M.ξ p u → unitAt M.ξ q u) → regAt M.ξ p ≤ regAt M.ξ q := by
    intro p q hp hq h a ha
    obtain ⟨u, hu, v, hv, hvu, rfl⟩ := ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c p hp).2 a).1 ha
    exact ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c q hq).2 _).2 ⟨u, hu, v, hv, h v hv hvu, rfl⟩
  have h1 := (PositivityTheory.HtPt.Ma.reg_le_spec o Ω κ x M p q).1 (hle hp hq fun u hu => (h u hu).1)
  have h2 := (PositivityTheory.HtPt.Ma.reg_le_spec o Ω κ x M q p).1 (hle hq hp fun u hu => (h u hu).2)
  exact Subtype.ext (h2.antisymm h1).eq

theorem isoAt_of_chart : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (κ' : Type) [Finite κ'] (w : κ' → Ω) (M' : PModel o (joinCo (RingHom.id Ω) x w)) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) → ∀ p : Cpt M.ξ, (∃ l, InChart M.ξ w l p) → IsoAt M'.ξ f (RingHom.id Ω) p := by
  intro o _ Ω _ _ κ _ x M κ' _ w M' f hd p ⟨l, hl⟩
  obtain ⟨c, hc⟩ := M.tie.cover p
  have hJ0 : joinCo (RingHom.id Ω) x w (c, l) ≠ 0 := mul_ne_zero hc.1 hl.1
  have ratio : ∀ j m, joinCo (RingHom.id Ω) x w (j, m) / joinCo (RingHom.id Ω) x w (c, l) =
      (x j / x c) * (w m / w l) := fun j m => by
    simp only [joinCo, RingHom.id_apply, mul_div_mul_comm]
  have hpJ : ∀ q, joinCo (RingHom.id Ω) x w q / joinCo (RingHom.id Ω) x w (c, l) ∈ regAt M.ξ p := by
    rintro ⟨j, m⟩
    rw [ratio]
    exact mul_mem (hc.2 j) (hl.2 m)
  have hAp := (PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c p hc).1
  have hctr : p ∈ ctrSet o (joinCo (RingHom.id Ω) x w) (RingHom.id Ω) M.ξ :=
    ⟨(c, l), hJ0, chRing_mem (fun r => hAp _ (Subalgebra.algebraMap_mem _ r)) hpJ⟩
  obtain ⟨p', ⟨hle', hun'⟩, -, hch'⟩ :=
    PositivityTheory.HtPt.Mb.centre o Ω (κ × κ') (joinCo (RingHom.id Ω) x w) M' M.X Ω M.ξ (RingHom.id Ω) p hctr
  have hle : ∀ a ∈ regAt M'.ξ p', a ∈ regAt M.ξ p := hle'
  have hun : ∀ a ∈ regAt M'.ξ p', unitAt M.ξ p a → unitAt M'.ξ p' a := hun'
  have hp'c : InChart M'.ξ (joinCo (RingHom.id Ω) x w) (c, l) p' := hch' (c, l) hJ0 hpJ
  have dom := PositivityTheory.HtPt.Mb.dom_local M.X Ω M.ξ M'.X Ω M'.ξ (RingHom.id Ω) f hd
  obtain ⟨h, hq1', hq2'⟩ := dom p'
  have hq1 : ∀ a ∈ regAt M.ξ ⟨f p'.1, h⟩, a ∈ regAt M'.ξ p' := hq1'
  have hq2 : ∀ a ∈ regAt M.ξ ⟨f p'.1, h⟩, unitAt M'.ξ p' a → unitAt M.ξ ⟨f p'.1, h⟩ a := hq2'
  have hx : ∀ j, x j / x c ∈ regAt M'.ξ p' := fun j => by
    have e : joinCo (RingHom.id Ω) x w (j, l) / joinCo (RingHom.id Ω) x w (c, l) = x j / x c := by
      rw [ratio, div_self hl.1, mul_one]
    rw [← e]
    exact hp'c.2 (j, l)
  obtain ⟨c₁, hc₁⟩ := M.tie.cover ⟨f p'.1, h⟩
  have hu : unitAt M.ξ ⟨f p'.1, h⟩ (x c / x c₁) :=
    hq2 _ (hc₁.2 c) ⟨div_ne_zero hc.1 hc₁.1, hq1 _ (hc₁.2 c), by rw [inv_div]; exact hx c₁⟩
  have hqc : InChart M.ξ x c ⟨f p'.1, h⟩ := ⟨hc.1, fun j => by
    have e : x j / x c = (x j / x c₁) * (x c / x c₁)⁻¹ := by
      have h1 := hc.1
      have h2 := hc₁.1
      field_simp
    rw [e]
    exact mul_mem (hc₁.2 j) hu.2.2⟩
  have hqp : (⟨f p'.1, h⟩ : Cpt M.ξ) = p := by
    refine eq_of_units M hqc hc fun u hu => ?_
    have uq := (PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c _ hqc).1 u hu
    exact ⟨fun k => ⟨k.1, hAp u hu, hle _ (hq1 _ k.2.2)⟩, fun k => hq2 u uq (hun u (hq1 u uq) k)⟩
  have e' : f p'.1 = p.1 := congrArg Subtype.val hqp
  rw [hqp] at hq1
  have hreg : regAt M'.ξ p' = regAt M.ξ p := le_antisymm hle hq1
  have uniq : ∀ p'' : Cpt M'.ξ, f p''.1 = p.1 → p'' = p' := by
    intro p'' e
    obtain ⟨h2, r1', r2'⟩ := dom p''
    have e2 : (⟨f p''.1, h2⟩ : Cpt M.ξ) = p := Subtype.ext e
    rw [e2] at r1' r2'
    have r1 : ∀ a ∈ regAt M.ξ p, a ∈ regAt M'.ξ p'' := r1'
    have r2 : ∀ a ∈ regAt M.ξ p, unitAt M'.ξ p'' a → unitAt M.ξ p a := r2'
    have hch : InChart M'.ξ (joinCo (RingHom.id Ω) x w) (c, l) p'' := ⟨hJ0, fun q => r1 _ (hpJ q)⟩
    refine eq_of_units M' hch hp'c fun u hu => ?_
    have up' := (PositivityTheory.HtPt.Ma.regat_loc o Ω (κ × κ') _ M' (c, l) p' hp'c).1 u hu
    have up := hle u up'
    exact ⟨fun k => hun u up' (r2 u up k), fun k => ⟨k.1, r1 u up, r1 _ (hle _ k.2.2)⟩⟩
  refine ⟨⟨p', e', fun p'' e => uniq p'' e⟩, fun p'' e => ?_, hd⟩
  rw [uniq p'' e, hreg, Subring.map_id]

end PositivityTheory.HtPt.Mb.LJoinIso.JoinIso

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

theorem PositivityTheory.HtPt.Mb.join_iso : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (κ' : Type) [Finite κ'] (w : κ' → Ω) (M' : PModel o (joinCo (RingHom.id Ω) x w)) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) → ∀ p : Cpt M.ξ, (∃ l, InChart M.ξ w l p) → IsoAt M'.ξ f (RingHom.id Ω) p :=
  @PositivityTheory.HtPt.Mb.LJoinIso.JoinIso.isoAt_of_chart
end

section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LJoinMany.JoinMany

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
  {A : Type} [Fintype A] {κa : A → Type} (w : ∀ a, κa a → Ω)

theorem inChart_prod_of_forall (p : Cpt ξ) (h : ∀ a, ∃ l, InChart ξ (w a) l p) :
    ∃ c, InChart ξ (fun c : (∀ a, κa a) => ∏ a, w a (c a)) c p := by
  choose c hc using h
  refine ⟨c, Finset.prod_ne_zero_iff.2 fun a _ => (hc a).1, fun c' => ?_⟩
  rw [← Finset.prod_div_distrib]
  exact prod_mem fun a _ => (hc a).2 (c' a)

theorem inChart_of_inChart_prod [DecidableEq A] {p : Cpt ξ} {c : ∀ a, κa a}
    (h : InChart ξ (fun c : (∀ a, κa a) => ∏ a, w a (c a)) c p) (a : A) : InChart ξ (w a) (c a) p := by
  obtain ⟨h0, h1⟩ := h
  have hne : ∀ b, w b (c b) ≠ 0 := fun b => (Finset.prod_ne_zero_iff.1 h0) b (Finset.mem_univ b)
  refine ⟨hne a, fun l => ?_⟩
  have key : (∏ b, w b (Function.update c a l b)) / (∏ b, w b (c b)) = w a l / w a (c a) := by
    rw [← Finset.prod_div_distrib, Fintype.prod_eq_single a]
    · simp
    · intro b hb
      simp [Function.update_of_ne hb, div_self (hne b)]
  rw [← key]
  exact h1 _

end PositivityTheory.HtPt.Mb.LJoinMany.JoinMany

namespace PositivityTheory.HtPt.Mb.LJoinMany

theorem join_finitely_many : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω), (∀ a, ∃ l, w a l ≠ 0) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → IsoAt M'.ξ f (RingHom.id Ω) p := by
  intro o _ Ω _ _ κ _ x M A _ κa _ w hw
  classical
  haveI := Fintype.ofFinite A
  have hW : ∃ l : (∀ a, κa a), (∏ a, w a (l a)) ≠ 0 := by
    choose c hc using hw
    exact ⟨c, Finset.prod_ne_zero_iff.2 fun a _ => hc a⟩
  have hcl : Subfield.closure (Set.range (RingHom.id Ω) ∪
      {z | ∃ l l' : (∀ a, κa a), z = (∏ a, w a (l a)) / ∏ a, w a (l' a)}) = ⊤ :=
    eq_top_iff.2 fun z _ => Subfield.subset_closure (Or.inl ⟨z, rfl⟩)
  obtain ⟨M', f, hf⟩ := PositivityTheory.HtPt.Mb.join_exists o Ω κ x M Ω (RingHom.id Ω) (∀ a, κa a)
    (fun c => ∏ a, w a (c a)) (fun _ => rfl) hW hcl
  refine ⟨κ × (∀ a, κa a), inferInstance, _, M', f, hf, ?_, ?_⟩
  · intro a p'
    obtain ⟨-, c, hc⟩ := PositivityTheory.HtPt.Mb.join_charts o Ω κ (∀ a, κa a) x Ω (RingHom.id Ω)
      (fun c => ∏ a, w a (c a)) M' (fun _ => rfl) p'
    exact ⟨c a, JoinMany.inChart_of_inChart_prod _ w hc a⟩
  · intro p hp
    exact PositivityTheory.HtPt.Mb.join_iso o Ω κ x M (∀ a, κa a) (fun c => ∏ a, w a (c a)) M' f hf p
      (JoinMany.inChart_prod_of_forall _ w p hp)

end PositivityTheory.HtPt.Mb.LJoinMany

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

theorem PositivityTheory.HtPt.Mb.join_many : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω), (∀ a, ∃ l, w a l ≠ 0) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → IsoAt M'.ξ f (RingHom.id Ω) p :=
  @PositivityTheory.HtPt.Mb.LJoinMany.join_finitely_many
end

section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LNormChart.ChNorm

theorem mem_of_isIntegral_of_inv_mem {Ω : Type} [Field Ω] (R : Subring Ω) {v : Ω} (hv : IsIntegral R v)
    (hv0 : v ≠ 0) (hu : v⁻¹ ∈ R) : v ∈ R := by
  obtain ⟨p, hp, hpv⟩ := hv
  have huv : v * v⁻¹ = 1 := mul_inv_cancel₀ hv0
  have key : ∀ i m : ℕ, i ≤ m → v ^ i * v⁻¹ ^ m = v⁻¹ ^ (m - i) := by
    intro i m him
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le him
    rw [pow_add, ← mul_assoc, ← mul_pow, huv, one_pow, one_mul, Nat.add_sub_cancel_left]
  rw [hp.as_sum] at hpv
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X_pow] at hpv
  generalize p.natDegree = n at hpv
  cases n with
  | zero => simp at hpv
  | succ m =>
    have h2 := congrArg (· * v⁻¹ ^ m) hpv
    simp only [add_mul, Finset.sum_mul, zero_mul] at h2
    rw [pow_succ, mul_comm (v ^ m) v, mul_assoc, key m m le_rfl, Nat.sub_self, pow_zero, mul_one] at h2
    have e : v = -∑ i ∈ Finset.range (m + 1), algebraMap R Ω (p.coeff i) * v⁻¹ ^ (m - i) := by
      rw [eq_neg_iff_add_eq_zero, ← h2]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [mul_assoc, key i m (by simp at hi; omega)]
    rw [e]
    refine neg_mem (sum_mem fun i _ => mul_mem ?_ (pow_mem hu _))
    exact (p.coeff i).2

end PositivityTheory.HtPt.Mb.LNormChart.ChNorm

namespace PositivityTheory.HtPt.Mb.LNormChart.ChNorm

theorem chRing_join_iff {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω)
    {d n : ℕ} (z : κ ⊕ Fin n → Ω) (hz : ∀ c, z (Sum.inl c) = x c ^ d) (c : κ) (hc : x c ≠ 0) (a : Ω) :
    a ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) ↔
      a ∈ Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) := by
  have hd : x c ^ d ≠ 0 := pow_ne_zero _ hc
  have hrat : ∀ q : κ × (κ ⊕ Fin n), joinCo (RingHom.id Ω) x z q / joinCo (RingHom.id Ω) x z (c, Sum.inl c) =
      x q.1 / x c * (z q.2 / x c ^ d) := by
    intro q
    simp only [joinCo, RingHom.id_apply, hz c]
    exact mul_div_mul_comm _ _ _ _
  have hT : chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) =
      Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro _ ⟨q, rfl⟩
      dsimp only
      rw [hrat]
      exact mul_mem (Algebra.subset_adjoin (Or.inl ⟨q.1, rfl⟩)) (Algebra.subset_adjoin (Or.inr ⟨q.2, rfl⟩))
    · apply Algebra.adjoin_le
      rintro _ (⟨j, rfl⟩ | ⟨k, rfl⟩)
      · have h1 : joinCo (RingHom.id Ω) x z (j, Sum.inl c) / joinCo (RingHom.id Ω) x z (c, Sum.inl c) ∈
            chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) :=
          Algebra.subset_adjoin (Set.mem_range_self (j, Sum.inl c))
        rw [hrat, hz c, div_self hd, mul_one] at h1
        exact h1
      · have h1 : joinCo (RingHom.id Ω) x z (c, k) / joinCo (RingHom.id Ω) x z (c, Sum.inl c) ∈
            chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) :=
          Algebra.subset_adjoin (Set.mem_range_self (c, k))
        rw [hrat, div_self hc, one_mul] at h1
        exact h1
  rw [hT]

end PositivityTheory.HtPt.Mb.LNormChart.ChNorm

namespace PositivityTheory.HtPt.Mb.LNormChart.ChNorm

theorem joinCo_div {Ω : Type} [Field Ω] {κ : Type} (x : κ → Ω) {d n : ℕ} (z : κ ⊕ Fin n → Ω)
    (hz : ∀ c, z (Sum.inl c) = x c ^ d) (c : κ) (q : κ × (κ ⊕ Fin n)) :
    joinCo (RingHom.id Ω) x z q / joinCo (RingHom.id Ω) x z (c, Sum.inl c) = x q.1 / x c * (z q.2 / x c ^ d) := by
  simp only [joinCo, RingHom.id_apply, hz c]
  exact mul_div_mul_comm _ _ _ _

theorem join_chart_normalisation : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (d n : ℕ) (z : κ ⊕ Fin n → Ω) (M' : PModel o (joinCo (RingHom.id Ω) x z)), (∀ c, z (Sum.inl c) = x c ^ d) → (∀ c, x c ≠ 0 → ∀ a : Ω, IsIntegral (chRing o x c) a ↔ a ∈ Submodule.span (chRing o x c) (Set.range fun k => z k / x c ^ d)) → ∀ c, x c ≠ 0 → (∀ a : Ω, a ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) ↔ IsIntegral (chRing o x c) a) ∧ ∀ p' : Cpt M'.ξ, (∀ j, x j / x c ∈ regAt M'.ξ p') → InChart M'.ξ (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) p' := by
  intro o _ Ω _ _ κ _ x d n z M' hz hspan c hc
  have hd : x c ^ d ≠ 0 := pow_ne_zero _ hc
  have hyS : ∀ k, IsIntegral (chRing o x c) (z k / x c ^ d) := fun k =>
    (hspan c hc _).2 (Submodule.subset_span ⟨k, rfl⟩)
  have hxS : ∀ j, x j / x c ∈ chRing o x c := fun j => Algebra.subset_adjoin ⟨j, rfl⟩
  refine ⟨fun a => ?_, fun p' hp' => ?_⟩
  · rw [chRing_join_iff x z hz c hc a]
    constructor
    · intro ha
      have hle : Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) ≤
          (integralClosure (chRing o x c) Ω).restrictScalars o := by
        apply Algebra.adjoin_le
        rintro _ (⟨j, rfl⟩ | ⟨k, rfl⟩)
        · exact (Subalgebra.mem_restrictScalars o).2 ((mem_integralClosure_iff _ _).2
            (isIntegral_algebraMap (x := (⟨_, hxS j⟩ : chRing o x c))))
        · exact (Subalgebra.mem_restrictScalars o).2 ((mem_integralClosure_iff _ _).2 (hyS k))
      exact (mem_integralClosure_iff _ _).1 ((Subalgebra.mem_restrictScalars o).1 (hle ha))
    · intro ha
      have hSle : chRing o x c ≤
          Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) :=
        Algebra.adjoin_mono Set.subset_union_left
      refine Submodule.span_induction
        (p := fun b _ => b ∈ Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)))
        ?_ ?_ ?_ ?_ ((hspan c hc a).1 ha)
      · rintro _ ⟨k, rfl⟩
        exact Algebra.subset_adjoin (Or.inr ⟨k, rfl⟩)
      · exact zero_mem _
      · intro a b _ _ ha hb
        exact add_mem ha hb
      · intro s b _ hb
        rw [Subalgebra.smul_def]
        exact mul_mem (hSle s.2) hb
  · obtain ⟨hctr, l, hl⟩ :=
      PositivityTheory.HtPt.Mb.join_charts o Ω κ (κ ⊕ Fin n) x Ω (RingHom.id Ω) z M' (fun _ => rfl) p'
    obtain ⟨c', -, hc'⟩ := hctr
    have ho : ∀ r : o, algebraMap o Ω r ∈ regAt M'.ξ p' := fun r =>
      hc' _ (Subalgebra.algebraMap_mem _ r)
    have hSle : ∀ a ∈ chRing o x c, a ∈ regAt M'.ξ p' := by
      intro a ha
      have h1 : a ∈ (chRing o x c).toSubring := ha
      rw [chRing, Algebra.adjoin_eq_ring_closure] at h1
      exact (Subring.closure_le.2 (Set.union_subset (by rintro _ ⟨r, rfl⟩; exact ho r)
        (by rintro _ ⟨j, rfl⟩; exact hp' j))) h1
    let φ : chRing o x c →+* regAt M'.ξ p' :=
      { toFun := fun s => ⟨s, hSle s s.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hvint : IsIntegral (regAt M'.ξ p') (z l / x c ^ d) :=
      IsIntegral.map_of_comp_eq φ (RingHom.id Ω) (by ext; rfl) (hyS l)
    obtain ⟨hzl, hzr⟩ := hl
    have hv : z l / x c ^ d ∈ regAt M'.ξ p' :=
      mem_of_isIntegral_of_inv_mem _ hvint (div_ne_zero hzl hd) (by rw [inv_div, ← hz c]; exact hzr _)
    have hy : ∀ k, z k / x c ^ d ∈ regAt M'.ξ p' := fun k => by
      have e : z k / x c ^ d = z k / z l * (z l / x c ^ d) := by field_simp
      rw [e]
      exact mul_mem (hzr k) hv
    refine ⟨?_, fun q => ?_⟩
    · simp only [joinCo, RingHom.id_apply, hz c]
      exact mul_ne_zero hc hd
    · rw [joinCo_div x z hz c q]
      exact mul_mem (hp' q.1) (hy q.2)

end PositivityTheory.HtPt.Mb.LNormChart.ChNorm

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

theorem PositivityTheory.HtPt.Mb.norm_chart : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (d n : ℕ) (z : κ ⊕ Fin n → Ω) (M' : PModel o (joinCo (RingHom.id Ω) x z)), (∀ c, z (Sum.inl c) = x c ^ d) → (∀ c, x c ≠ 0 → ∀ a : Ω, IsIntegral (chRing o x c) a ↔ a ∈ Submodule.span (chRing o x c) (Set.range fun k => z k / x c ^ d)) → ∀ c, x c ≠ 0 → (∀ a : Ω, a ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) ↔ IsIntegral (chRing o x c) a) ∧ ∀ p' : Cpt M'.ξ, (∀ j, x j / x c ∈ regAt M'.ξ p') → InChart M'.ξ (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) p' :=
  @PositivityTheory.HtPt.Mb.LNormChart.ChNorm.join_chart_normalisation
end

section
noncomputable section

namespace PositivityTheory.HtPt.Mb.LCentreUnique.Centre.Sep

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem isLocalRing_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    IsLocalRing (regAt ξ p) := by
  show IsLocalRing (genMap ξ p).range
  exact IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective

theorem isUnit_regAt_iff {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ)
    (a : regAt ξ p) : IsUnit a ↔ unitAt ξ p (a : Ω) := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h.exists_right_inv
    have e : (a : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
    have ha : (a : Ω) ≠ 0 := fun h0 => by simp [h0] at e
    refine ⟨ha, a.2, ?_⟩
    rw [inv_eq_of_mul_eq_one_right e]
    exact b.2
  · rintro ⟨h0, -, h2⟩
    exact isUnit_iff_exists_inv.2 ⟨⟨_, h2⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

theorem unitAt_iff_of_dominated {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {i : Ω →+* Ω'} {p' : Cpt ξ'} {q : Cpt ξ}
    (h : (∀ a ∈ regAt ξ q, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt ξ q, unitAt ξ' p' (i a) → unitAt ξ q a)
    {a : Ω} (ha : a ∈ regAt ξ q) : unitAt ξ q a ↔ unitAt ξ' p' (i a) := by
  refine ⟨fun hu => ⟨(map_ne_zero i).2 hu.1, h.1 a hu.2.1, ?_⟩, h.2 a ha⟩
  rw [← map_inv₀]
  exact h.1 _ hu.2.2

theorem eq_of_dominated_of_inChart {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ]
    {x : κ → Ω} (M : PModel o x) {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
    {i : Ω →+* Ω'} {p' : Cpt ξ'} {c : κ} {q r : Cpt M.ξ} (hq : InChart M.ξ x c q) (hr : InChart M.ξ x c r)
    (dq : (∀ a ∈ regAt M.ξ q, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q, unitAt ξ' p' (i a) → unitAt M.ξ q a)
    (dr : (∀ a ∈ regAt M.ξ r, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ r, unitAt ξ' p' (i a) → unitAt M.ξ r a) :
    q = r := by
  have cq := (PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c q hq).1
  have cr := (PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c r hr).1
  haveI := isLocalRing_regAt M.ξ q
  let f : chRing o x c →+* regAt M.ξ q :=
    ((chRing o x c).val : chRing o x c →+* Ω).codRestrict (regAt M.ξ q) fun u => cq _ u.2
  have hP : ∀ u : chRing o x c, u ∈ (IsLocalRing.maximalIdeal (regAt M.ξ q)).comap f ↔ ¬ unitAt M.ξ q (u : Ω) := by
    intro u
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_regAt_iff]
    rfl
  obtain ⟨p, -, huniq⟩ := PositivityTheory.HtPt.Ma.prime_pt o Ω κ x M c hq.1 _
    (inferInstance : ((IsLocalRing.maximalIdeal (regAt M.ξ q)).comap f).IsPrime)
  have e1 := huniq q ⟨hq, hP⟩
  have e2 := huniq r ⟨hr, fun u => by
    rw [hP, unitAt_iff_of_dominated dq (cq _ u.2), unitAt_iff_of_dominated dr (cr _ u.2)]⟩
  exact e1.trans e2.symm

theorem eq_of_dominated : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ') (q₁ q₂ : Cpt M.ξ), ((∀ a ∈ regAt M.ξ q₁, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₁, unitAt ξ' p' (i a) → unitAt M.ξ q₁ a) → ((∀ a ∈ regAt M.ξ q₂, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₂, unitAt ξ' p' (i a) → unitAt M.ξ q₂ a) → q₁ = q₂ := by
  intro o _ Ω _ _ κ _ x M X' Ω' _ ξ' i p' q₁ q₂ d₁ d₂
  obtain ⟨c₁, hc₁⟩ := M.tie.cover q₁
  obtain ⟨c₂, hc₂⟩ := M.tie.cover q₂
  have hctr : p' ∈ ctrSet o x i ξ' :=
    ⟨c₁, hc₁.1, fun a ha => d₁.1 a ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c₁ q₁ hc₁).1 a ha)⟩
  obtain ⟨p₀, d₀, -, hp₀⟩ := PositivityTheory.HtPt.Mb.centre o Ω κ x M X' Ω' ξ' i p' hctr
  have e₁ : q₁ = p₀ := eq_of_dominated_of_inChart M hc₁ (hp₀ c₁ hc₁.1 fun j => d₁.1 _ (hc₁.2 j)) d₁ d₀
  have e₂ : q₂ = p₀ := eq_of_dominated_of_inChart M hc₂ (hp₀ c₂ hc₂.1 fun j => d₂.1 _ (hc₂.2 j)) d₂ d₀
  exact e₁.trans e₂.symm

end PositivityTheory.HtPt.Mb.LCentreUnique.Centre.Sep

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

theorem PositivityTheory.HtPt.Mb.centre_unique : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ') (q₁ q₂ : Cpt M.ξ), ((∀ a ∈ regAt M.ξ q₁, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₁, unitAt ξ' p' (i a) → unitAt M.ξ q₁ a) → ((∀ a ∈ regAt M.ξ q₂, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₂, unitAt ξ' p' (i a) → unitAt M.ξ q₂ a) → q₁ = q₂ :=
  @PositivityTheory.HtPt.Mb.LCentreUnique.Centre.Sep.eq_of_dominated
end
end

section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

noncomputable section

namespace PositivityTheory.HtPt.Mb.LFracExt.FracExt

def genCpt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Cpt ξ :=
  ⟨genPt ξ, specializes_rfl⟩

theorem mem_regAt_genCpt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ)
    (a : Ω) : a ∈ regAt ξ (genCpt ξ) := by
  obtain ⟨s, hs⟩ := h.bij.2 a
  refine ⟨s, ?_⟩
  have e : X.presheaf.stalkSpecializes (genCpt ξ).2 = 𝟙 _ := TopCat.Presheaf.stalkSpecializes_refl _ _
  simp only [genMap, e, Category.id_comp]
  exact hs

theorem exists_frac {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
    (M : PModel o x) {c : κ} (hc : x c ≠ 0) (a : Ω) :
    ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, a = u / v := by
  have hp : InChart M.ξ x c (genCpt M.ξ) := ⟨hc, fun _ => mem_regAt_genCpt M.tie.gen _⟩
  obtain ⟨u, hu, v, hv, -, e⟩ := ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c _ hp).2 a).1 (mem_regAt_genCpt M.tie.gen a)
  exact ⟨u, hu, v, hv, e⟩

theorem algebraMap_mem_chRing {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω)
    (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ) {a : Ω}
    (ha : a ∈ chRing o x c) : algebraMap Ω Ω' a ∈ chRing o (fun k => algebraMap Ω Ω' (x k)) c := by
  induction ha using Algebra.adjoin_induction with
  | mem a h =>
    obtain ⟨j, rfl⟩ := h
    rw [map_div₀]
    exact Algebra.subset_adjoin ⟨j, rfl⟩
  | algebraMap r =>
    rw [← IsScalarTower.algebraMap_apply]
    exact Subalgebra.algebraMap_mem _ r
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem exists_integral_div : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ]
    {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω']
    [IsScalarTower o Ω Ω'] (c : κ), x c ≠ 0 → ∀ a : Ω', ∃ b v : Ω',
      IsIntegral (chRing o (fun k => algebraMap Ω Ω' (x k)) c) b ∧
        v ∈ chRing o (fun k => algebraMap Ω Ω' (x k)) c ∧ v ≠ 0 ∧ a = b / v := by
  intro o _ Ω _ _ κ _ x M Ω' _ _ _ _ _ c hc a
  haveI : IsFractionRing (chRing o x c) Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨u, hu, v, hv, e⟩ := exists_frac M hc z
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, e⟩
  have halg : IsAlgebraic (chRing o x c) a := by
    haveI : Algebra.IsAlgebraic (chRing o x c) Ω' :=
      (IsFractionRing.comap_isAlgebraic_iff (A := chRing o x c) (K := Ω) (C := Ω')).2 inferInstance
    exact Algebra.IsAlgebraic.isAlgebraic a
  obtain ⟨y, hy0, hi⟩ := halg.exists_integral_multiple
  have hy0' : (y : Ω) ≠ 0 := fun h => hy0 (Subtype.ext h)
  have hv : algebraMap Ω Ω' (y : Ω) ≠ 0 := (map_ne_zero _).2 hy0'
  let φ : chRing o x c →+* chRing o (fun k => algebraMap Ω Ω' (x k)) c :=
    ((algebraMap Ω Ω').comp (chRing o x c).val.toRingHom).codRestrict _
      fun r => algebraMap_mem_chRing x Ω' c r.2
  have hb := IsIntegral.map_of_comp_eq φ (RingHom.id Ω') (by ext r; rfl) hi
  refine ⟨y • a, algebraMap Ω Ω' (y : Ω), hb, algebraMap_mem_chRing x Ω' c y.2, hv, ?_⟩
  have e : y • a = algebraMap Ω Ω' (y : Ω) * a := by
    rw [Algebra.smul_def]; rfl
  rw [e, mul_div_cancel_left₀ _ hv]

end PositivityTheory.HtPt.Mb.LFracExt.FracExt

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

theorem PositivityTheory.HtPt.Mb.frac_ext : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ), x c ≠ 0 → ∀ a : Ω', ∃ b v : Ω', IsIntegral (chRing o (fun k => algebraMap Ω Ω' (x k)) c) b ∧ v ∈ chRing o (fun k => algebraMap Ω Ω' (x k)) c ∧ v ≠ 0 ∧ a = b / v :=
  @PositivityTheory.HtPt.Mb.LFracExt.FracExt.exists_integral_div
end
end

section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

noncomputable section

namespace PositivityTheory.HtPt.Mb.LFiniteExt.ChartFinite

theorem mem_regAt_genPt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (h : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ ⟨genPt ξ, specializes_rfl⟩ := by
  obtain ⟨s, hs⟩ := h.bij.2 a
  refine ⟨s, ?_⟩
  have e : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
    TopCat.Presheaf.stalkSpecializes_refl _ _
  simp only [genMap]
  rw [e]
  erw [Category.id_comp]
  exact hs

theorem exists_eq_div_chRing {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type}
    [Finite κ] {x : κ → Ω} (M : PModel o x) {c : κ} (hc : x c ≠ 0) (a : Ω) :
    ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, a = u / v := by
  have hp : InChart M.ξ x c ⟨genPt M.ξ, specializes_rfl⟩ :=
    ⟨hc, fun c' => mem_regAt_genPt M.tie.gen _⟩
  obtain ⟨u, hu, v, hv, -, e⟩ :=
    ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c _ hp).2 a).1 (mem_regAt_genPt M.tie.gen a)
  exact ⟨u, hu, v, hv, e⟩

theorem finite_integralClosure_chRing {o : Type} [CommRing o] [Algebra.EssFiniteType ℤ o] {Ω : Type}
    [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω']
    [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ)
    (hc : x c ≠ 0) :
    Module.Finite (chRing o (fun k => algebraMap Ω Ω' (x k)) c)
      (integralClosure (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω') := by
  let φ : Ω →ₐ[o] Ω' := IsScalarTower.toAlgHom o Ω Ω'
  have hφ : Function.Injective φ := φ.toRingHom.injective
  have hmap : (chRing o x c).map φ = chRing o (fun k => algebraMap Ω Ω' (x k)) c := by
    simp only [chRing]
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    congr 2
    ext j
    simp [φ]
  let e : chRing o x c ≃ₐ[o] chRing o (fun k => algebraMap Ω Ω' (x k)) c :=
    ((chRing o x c).equivMapOfInjective φ hφ).trans (Subalgebra.equivOfEq _ _ hmap)
  have he : ∀ a, ((e a : chRing o (fun k => algebraMap Ω Ω' (x k)) c) : Ω') =
      algebraMap Ω Ω' (a : Ω) := fun a => rfl
  haveI : Algebra.FiniteType o (chRing o (fun k => algebraMap Ω Ω' (x k)) c) := by
    rw [← Subalgebra.fg_iff_finiteType]
    exact Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩
  haveI : Algebra.EssFiniteType o (chRing o (fun k => algebraMap Ω Ω' (x k)) c) :=
    Algebra.EssFiniteType.of_finiteType _ _
  haveI : Algebra.EssFiniteType ℤ (chRing o (fun k => algebraMap Ω Ω' (x k)) c) :=
    Algebra.EssFiniteType.comp ℤ o _
  letI : Algebra (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω :=
    ((chRing o x c).val.toRingHom.comp e.symm.toRingEquiv.toRingHom).toAlgebra
  have hmapΩ : ∀ a : chRing o x c,
      algebraMap (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω (e a) = (a : Ω) := by
    intro a
    change ((e.symm (e a) : chRing o x c) : Ω) = a
    rw [AlgEquiv.symm_apply_apply]
  haveI : IsScalarTower (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω Ω' :=
    IsScalarTower.of_algebraMap_eq fun a => by
      obtain ⟨b, rfl⟩ := e.surjective a
      rw [hmapΩ]
      exact he b
  haveI : FaithfulSMul (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h => by
      obtain ⟨a, rfl⟩ := e.surjective a
      obtain ⟨b, rfl⟩ := e.surjective b
      rw [hmapΩ, hmapΩ] at h
      rw [Subtype.ext h]
  haveI : IsFractionRing (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω :=
    IsFractionRing.of_field _ _ fun z => by
      obtain ⟨u, hu, v, hv, rfl⟩ := exists_eq_div_chRing M hc z
      exact ⟨e ⟨u, hu⟩, e ⟨v, hv⟩, by rw [hmapΩ, hmapΩ]⟩
  exact PositivityTheory.HtPt.Mb.fin_closure _ Ω Ω'

end PositivityTheory.HtPt.Mb.LFiniteExt.ChartFinite

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

theorem PositivityTheory.HtPt.Mb.finite_ext : ∀ {o : Type} [CommRing o] [Algebra.EssFiniteType ℤ o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ), x c ≠ 0 → Module.Finite (chRing o (fun k => algebraMap Ω Ω' (x k)) c) (integralClosure (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω') :=
  @PositivityTheory.HtPt.Mb.LFiniteExt.ChartFinite.finite_integralClosure_chRing
end
end

section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

noncomputable section
namespace PositivityTheory.HtPt.Mb.LNormExists.NormEx

instance isLocalRing_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    IsLocalRing (regAt ξ p) :=
  (LocalSubring.range (genMap ξ p)).isLocalRing

theorem int_trans {o K : Type} [CommRing o] [Field K] [Algebra o K] (A B : Subalgebra o K)
    (hAB : ∀ a ∈ A, a ∈ B) (hB : ∀ b ∈ B, IsIntegral A b) (a : K) (ha : IsIntegral B a) : IsIntegral A a := by
  letI : Algebra A B := (Subalgebra.inclusion hAB).toRingHom.toAlgebra
  haveI : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral A B := ⟨fun b => by
    have := hB b b.2
    exact (isIntegral_algebraMap_iff (A := B) (B := K) (x := b) Subtype.val_injective).1 this⟩
  exact isIntegral_trans a ha

theorem mem_of_isIntegral_loc {o K : Type} [CommRing o] [Field K] [Algebra o K] (A : Subalgebra o K) (D : Subring K)
    (hA : ∀ a, IsIntegral A a → a ∈ A) (hAD : ∀ a ∈ A, a ∈ D)
    (hD : ∀ a ∈ D, ∃ u ∈ A, ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ D ∧ a = u / v) (a : K) (ha : IsIntegral D a) : a ∈ D := by
  obtain ⟨v, -, hv0, hvi, hi⟩ := GlobalTheory.T.integral_over_localization_scaled A D hAD hD a ha
  have e : a = (v * a) * v⁻¹ := by field_simp
  rw [e]
  exact mul_mem (hAD _ (hA _ hi)) hvi

theorem ideal_ext {o K : Type} [CommRing o] [Field K] [Algebra o K] (A : Subalgebra o K) (R : Subring K)
    (hAR : ∀ a ∈ A, a ∈ R) (hR : ∀ r ∈ R, ∃ u ∈ A, ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ R ∧ r = u / v)
    (P₁ P₂ : Ideal (integralClosure R K).toSubring)
    (hag : ∀ t : (integralClosure R K).toSubring, IsIntegral A (t : K) → (t ∈ P₁ ↔ t ∈ P₂)) : P₁ = P₂ := by
  have hRT : ∀ r ∈ R, r ∈ (integralClosure R K).toSubring := fun r hr =>
    isIntegral_algebraMap (x := (⟨r, hr⟩ : R))
  have key : ∀ Q₁ Q₂ : Ideal (integralClosure R K).toSubring,
      (∀ t : (integralClosure R K).toSubring, IsIntegral A (t : K) → t ∈ Q₁ → t ∈ Q₂) → Q₁ ≤ Q₂ := by
    intro Q₁ Q₂ h t ht
    obtain ⟨v, hv, hv0, hvi, hi⟩ := GlobalTheory.T.integral_over_localization_scaled A R hAR hR t t.2
    have h1 := h (⟨v, hRT v (hAR v hv)⟩ * t) hi (Q₁.mul_mem_left _ ht)
    have h2 := Q₂.mul_mem_left ⟨v⁻¹, hRT _ hvi⟩ h1
    have e : (⟨v⁻¹, hRT _ hvi⟩ : (integralClosure R K).toSubring) * (⟨v, hRT v (hAR v hv)⟩ * t) = t := by
      apply Subtype.ext
      change v⁻¹ * (v * (t : K)) = t
      field_simp
    rwa [e] at h2
  exact le_antisymm (key _ _ fun t ht => (hag t ht).1) (key _ _ fun t ht => (hag t ht).2)

theorem exists_ne {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    (M : PModel o x) : ∃ c, x c ≠ 0 := by
  obtain ⟨c, hc⟩ := M.tie.cover ⟨genPt M.ξ, specializes_rfl⟩
  exact ⟨c, hc.1⟩

theorem join_chart {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω) (d n : ℕ)
    (z : κ ⊕ Fin n → Ω) (hz : ∀ c, z (Sum.inl c) = x c ^ d)
    (hi : ∀ c, x c ≠ 0 → ∀ a : Ω, IsIntegral (chRing o x c) a ↔
      a ∈ Submodule.span (chRing o x c) (Set.range fun k => z k / x c ^ d))
    (c : κ) (hc : x c ≠ 0) (a : Ω) (ha : IsIntegral (chRing o x c) a) :
    a ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) := by
  have hcd : x c ^ d ≠ 0 := pow_ne_zero _ hc
  have h1 : ∀ k, z k / x c ^ d ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) := fun k => by
    have e : joinCo (RingHom.id Ω) x z (c, k) / joinCo (RingHom.id Ω) x z (c, Sum.inl c) = z k / x c ^ d := by
      simp only [joinCo, RingHom.id_apply, hz]
      rw [mul_div_mul_left _ _ hc]
    rw [← e]
    exact Algebra.subset_adjoin ⟨(c, k), rfl⟩
  have h2 : ∀ j, x j / x c ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) := fun j => by
    have e : joinCo (RingHom.id Ω) x z (j, Sum.inl c) / joinCo (RingHom.id Ω) x z (c, Sum.inl c) = x j / x c := by
      simp only [joinCo, RingHom.id_apply, hz]
      rw [mul_div_mul_right _ _ hcd]
    rw [← e]
    exact Algebra.subset_adjoin ⟨(j, Sum.inl c), rfl⟩
  have h3 : chRing o x c ≤ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) :=
    Algebra.adjoin_le (by rintro _ ⟨j, rfl⟩; exact h2 j)
  have key : ∀ a ∈ Submodule.span (chRing o x c) (Set.range fun k => z k / x c ^ d),
      a ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) := by
    intro a h
    induction h using Submodule.span_induction with
    | mem a h => obtain ⟨k, rfl⟩ := h; exact h1 k
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul r a _ h => exact mul_mem (h3 r.2) h
  exact key a ((hi c hc a).1 ha)

theorem map_chRing {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω)
    (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ) (a : Ω)
    (ha : a ∈ chRing o x c) : algebraMap Ω Ω' a ∈ chRing o (fun k => algebraMap Ω Ω' (x k)) c := by
  induction ha using Algebra.adjoin_induction with
  | mem a h =>
    obtain ⟨j, rfl⟩ := h
    rw [map_div₀]
    exact Algebra.subset_adjoin ⟨j, rfl⟩
  | algebraMap r =>
    rw [← IsScalarTower.algebraMap_apply]
    exact Subalgebra.algebraMap_mem _ r
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem exists_of_mem_chRing {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω)
    (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ) (a : Ω')
    (ha : a ∈ chRing o (fun k => algebraMap Ω Ω' (x k)) c) : ∃ b ∈ chRing o x c, algebraMap Ω Ω' b = a := by
  induction ha using Algebra.adjoin_induction with
  | mem a h =>
    obtain ⟨j, rfl⟩ := h
    exact ⟨x j / x c, Algebra.subset_adjoin ⟨j, rfl⟩, map_div₀ _ _ _⟩
  | algebraMap r =>
    exact ⟨algebraMap o Ω r, Subalgebra.algebraMap_mem _ r, (IsScalarTower.algebraMap_apply o Ω Ω' r).symm⟩
  | add a b _ _ ha hb =>
    obtain ⟨a', h1, rfl⟩ := ha
    obtain ⟨b', h2, rfl⟩ := hb
    exact ⟨a' + b', add_mem h1 h2, map_add _ _ _⟩
  | mul a b _ _ ha hb =>
    obtain ⟨a', h1, rfl⟩ := ha
    obtain ⟨b', h2, rfl⟩ := hb
    exact ⟨a' * b', mul_mem h1 h2, map_mul _ _ _⟩

theorem normal_of_charts {o : Type} [CommRing o] {Ω' : Type} [Field Ω'] [Algebra o Ω'] {κ' : Type} [Finite κ']
    {y : κ' → Ω'} (M' : PModel o y) (S : Set κ') (hS : ∀ p' : Cpt M'.ξ, ∃ c ∈ S, InChart M'.ξ y c p')
    (hI : ∀ c ∈ S, ∀ a : Ω', IsIntegral (chRing o y c) a → a ∈ chRing o y c) : Flat.NormalCpt M'.ξ := by
  intro p' a ha
  obtain ⟨c, hcS, hp⟩ := hS p'
  have h := PositivityTheory.HtPt.Ma.regat_loc o Ω' κ' y M' c p' hp
  refine mem_of_isIntegral_loc (chRing o y c) (regAt M'.ξ p') (hI c hcS) h.1 (fun a ha => ?_) a ha
  obtain ⟨u, hu, v, hv, hvu, rfl⟩ := (h.2 a).1 ha
  exact ⟨u, hu, v, hv, hvu.1, hvu.2.2, rfl⟩

theorem unitAt_map {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} (i : Ω →+* Ω') {p : Cpt ξ} {p' : Cpt ξ'}
    (h : ∀ a ∈ regAt ξ p, i a ∈ regAt ξ' p') {u : Ω} (hu : unitAt ξ p u) : unitAt ξ' p' (i u) :=
  ⟨(map_ne_zero i).2 hu.1, h _ hu.2.1, by rw [← map_inv₀]; exact h _ hu.2.2⟩

section Sit

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
  (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω']
  {κ' : Type} [Finite κ'] {y : κ' → Ω'} (M' : PModel o y) (f : M'.X ⟶ M.X) (e : κ → κ')

variable {M Ω' M' f} in

theorem dom_of_eq (hD : Dominates M'.ξ M.ξ f (algebraMap Ω Ω')) {p : Cpt M.ξ} {p' : Cpt M'.ξ} (h : f p'.1 = p.1) :
    (∀ a ∈ regAt M.ξ p, algebraMap Ω Ω' a ∈ regAt M'.ξ p') ∧
      ∀ a ∈ regAt M.ξ p, unitAt M'.ξ p' (algebraMap Ω Ω' a) → unitAt M.ξ p a := by
  obtain ⟨h', hl⟩ := PositivityTheory.HtPt.Mb.dom_local M.X Ω M.ξ M'.X Ω' M'.ξ (algebraMap Ω Ω') f hD p'
  have e : (⟨f p'.1, h'⟩ : Cpt M.ξ) = p := Subtype.ext h
  rwa [e] at hl

theorem fibre_iff (hD : Dominates M'.ξ M.ξ f (algebraMap Ω Ω'))
    (hB : ∀ c, x c ≠ 0 → ∀ a : Ω', IsIntegral (chRing o (fun k => algebraMap Ω Ω' (x k)) c) a → a ∈ chRing o y (e c))
    (hC : ∀ c, x c ≠ 0 → ∀ p' : Cpt M'.ξ, (∀ j, algebraMap Ω Ω' (x j) / algebraMap Ω Ω' (x c) ∈ regAt M'.ξ p') →
      InChart M'.ξ y (e c) p')
    (c : κ) (p : Cpt M.ξ) (hp : InChart M.ξ x c p) (p' : Cpt M'.ξ) :
    f p'.1 = p.1 ↔ InChart M'.ξ y (e c) p' ∧
      ∀ u ∈ chRing o x c, (unitAt M.ξ p u ↔ unitAt M'.ξ p' (algebraMap Ω Ω' u)) := by
  have hr := PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c p hp
  constructor
  · intro h
    have hl := dom_of_eq hD h
    refine ⟨hC c hp.1 p' fun j => ?_, fun u hu => ⟨unitAt_map _ hl.1, hl.2 u (hr.1 u hu)⟩⟩
    rw [← map_div₀]
    exact hl.1 _ (hp.2 j)
  · rintro ⟨hp', hu⟩
    have hr' := PositivityTheory.HtPt.Ma.regat_loc o Ω' κ' y M' (e c) p' hp'
    have hA : ∀ u ∈ chRing o x c, algebraMap Ω Ω' u ∈ regAt M'.ξ p' := fun u hu' =>
      hr'.1 _ (hB c hp.1 _ (isIntegral_algebraMap (x := (⟨_, map_chRing x Ω' c u hu'⟩ :
        chRing o (fun k => algebraMap Ω Ω' (x k)) c))))
    have hl : (∀ a ∈ regAt M.ξ p, algebraMap Ω Ω' a ∈ regAt M'.ξ p') ∧
        ∀ a ∈ regAt M.ξ p, unitAt M'.ξ p' (algebraMap Ω Ω' a) → unitAt M.ξ p a := by
      refine ⟨fun a ha => ?_, fun a ha h => ?_⟩
      · obtain ⟨u, h1, v, h2, hv, rfl⟩ := (hr.2 a).1 ha
        have := ((hu v h2).1 hv).2.2
        rw [map_div₀, div_eq_mul_inv]
        exact mul_mem (hA u h1) this
      · obtain ⟨u, h1, v, h2, hv, rfl⟩ := (hr.2 a).1 ha
        have h3 : unitAt M'.ξ p' (algebraMap Ω Ω' u) := by
          have h4 := Flat.ZUnit.mul h ((hu v h2).1 hv)
          have h5 : algebraMap Ω Ω' (u / v) * algebraMap Ω Ω' v = algebraMap Ω Ω' u := by
            rw [← map_mul, div_mul_cancel₀ _ hv.1]
          rwa [h5] at h4
        have h4 := Flat.ZUnit.mul ((hu u h1).2 h3) (Flat.ZUnit.inv hv)
        rwa [← div_eq_mul_inv] at h4
    obtain ⟨h', hl'⟩ := PositivityTheory.HtPt.Mb.dom_local M.X Ω M.ξ M'.X Ω' M'.ξ (algebraMap Ω Ω') f hD p'
    exact congrArg Subtype.val (PositivityTheory.HtPt.Mb.centre_unique M M'.ξ (algebraMap Ω Ω') p' ⟨f p'.1, h'⟩ p hl' hl)

theorem chart_over (hD : Dominates M'.ξ M.ξ f (algebraMap Ω Ω'))
    (hB : ∀ c, x c ≠ 0 → ∀ a : Ω', IsIntegral (chRing o (fun k => algebraMap Ω Ω' (x k)) c) a → a ∈ chRing o y (e c))
    (hC : ∀ c, x c ≠ 0 → ∀ p' : Cpt M'.ξ, (∀ j, algebraMap Ω Ω' (x j) / algebraMap Ω Ω' (x c) ∈ regAt M'.ξ p') →
      InChart M'.ξ y (e c) p')
    (c : κ) (hc : x c ≠ 0) (p' : Cpt M'.ξ) :
    InChart M'.ξ y (e c) p' ↔ ∃ p : Cpt M.ξ, p.1 = f p'.1 ∧ InChart M.ξ x c p := by
  constructor
  · intro hp'
    have hr' := PositivityTheory.HtPt.Ma.regat_loc o Ω' κ' y M' (e c) p' hp'
    have hA : ∀ u ∈ chRing o x c, algebraMap Ω Ω' u ∈ regAt M'.ξ p' := fun u hu' =>
      hr'.1 _ (hB c hc _ (isIntegral_algebraMap (x := (⟨_, map_chRing x Ω' c u hu'⟩ :
        chRing o (fun k => algebraMap Ω Ω' (x k)) c))))
    obtain ⟨p₀, hl, -, hch⟩ := PositivityTheory.HtPt.Mb.centre o Ω κ x M M'.X Ω' M'.ξ (algebraMap Ω Ω') p' ⟨c, hc, hA⟩
    obtain ⟨h', hl'⟩ := PositivityTheory.HtPt.Mb.dom_local M.X Ω M.ξ M'.X Ω' M'.ξ (algebraMap Ω Ω') f hD p'
    exact ⟨p₀, congrArg Subtype.val (PositivityTheory.HtPt.Mb.centre_unique M M'.ξ (algebraMap Ω Ω') p' p₀ ⟨f p'.1, h'⟩ hl hl'),
      hch c hc fun j => hA _ (Algebra.subset_adjoin ⟨j, rfl⟩)⟩
  · rintro ⟨p, hpf, hp⟩
    have hl := dom_of_eq hD hpf.symm
    refine hC c hc p' fun j => ?_
    rw [← map_div₀]
    exact hl.1 _ (hp.2 j)

end Sit

theorem isIntegral_mono {o K : Type} [CommRing o] [Field K] [Algebra o K] (A : Subalgebra o K) (R : Subring K)
    (h : ∀ a ∈ A, a ∈ R) (b : K) (hb : IsIntegral A b) : IsIntegral R b :=
  IsIntegral.map_of_comp_eq (A.val.toRingHom.codRestrict R fun a => h a a.2) (RingHom.id K) (by ext; rfl) hb

theorem isIntegral_mono' {K : Type} [Field K] {R D : Subring K} (h : R ≤ D) (b : K) (hb : IsIntegral R b) :
    IsIntegral D b :=
  IsIntegral.map_of_comp_eq (Subring.inclusion h) (RingHom.id K) (by ext; rfl) hb

section Sit

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
  (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω']
  {κ' : Type} [Finite κ'] {y : κ' → Ω'} (M' : PModel o y) (f : M'.X ⟶ M.X) (e : κ → κ')

local notation "i₀" => algebraMap Ω Ω'
local notation "A₀" => chRing o (fun k => algebraMap Ω Ω' (x k))

theorem normAt_of_charts (hD : Dominates M'.ξ M.ξ f (algebraMap Ω Ω'))
    (hy : ∀ c, x c ≠ 0 → y (e c) ≠ 0)
    (hB : ∀ c, x c ≠ 0 → ∀ a : Ω', a ∈ chRing o y (e c) ↔ IsIntegral (chRing o (fun k => algebraMap Ω Ω' (x k)) c) a)
    (hC : ∀ c, x c ≠ 0 → ∀ p' : Cpt M'.ξ, (∀ j, algebraMap Ω Ω' (x j) / algebraMap Ω Ω' (x c) ∈ regAt M'.ξ p') →
      InChart M'.ξ y (e c) p')
    (hN : Flat.NormalCpt M'.ξ) (p : Cpt M.ξ) : NormAt M'.ξ f (algebraMap Ω Ω') p := by
  obtain ⟨c, hp⟩ := M.tie.cover p
  have hc := hp.1
  have hr := PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c p hp
  have hB1 : ∀ c, x c ≠ 0 → ∀ a : Ω', IsIntegral (A₀ c) a → a ∈ chRing o y (e c) := fun c hc a => (hB c hc a).2
  have hAR : ∀ a ∈ A₀ c, a ∈ (regAt M.ξ p).map i₀ := fun a ha => by
    obtain ⟨b, hb, rfl⟩ := exists_of_mem_chRing x Ω' c a ha
    exact ⟨b, hr.1 b hb, rfl⟩
  have hR : ∀ r ∈ (regAt M.ξ p).map i₀, ∃ u ∈ A₀ c, ∃ v ∈ A₀ c, v ≠ 0 ∧ v⁻¹ ∈ (regAt M.ξ p).map i₀ ∧ r = u / v := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨u, hu, v, hv, hvu, rfl⟩ := (hr.2 a).1 ha
    exact ⟨i₀ u, map_chRing x Ω' c u hu, i₀ v, map_chRing x Ω' c v hv, (map_ne_zero _).2 hvu.1,
      ⟨v⁻¹, hvu.2.2, map_inv₀ _ _⟩, map_div₀ _ _ _⟩
  have first : ∀ p' : Cpt M'.ξ, f p'.1 = p.1 →
      ∃ (P : Ideal (integralClosure ((regAt M.ξ p).map i₀) Ω').toSubring) (_ : P.IsMaximal),
        regAt M'.ξ p' = (LocalSubring.ofPrime _ P).toSubring ∧
        ∀ t : (integralClosure ((regAt M.ξ p).map i₀) Ω').toSubring,
          t ∈ P ↔ ¬ ((t : Ω') ≠ 0 ∧ (t : Ω')⁻¹ ∈ regAt M'.ξ p') := by
    intro p' hf
    have hl := dom_of_eq hD hf
    have hch := ((fibre_iff M Ω' M' f e hD hB1 hC c p hp p').1 hf).1
    have hr' := PositivityTheory.HtPt.Ma.regat_loc o Ω' κ' y M' (e c) p' hch
    have hRD : (regAt M.ξ p).map i₀ ≤ regAt M'.ξ p' := by
      rintro _ ⟨a, ha, rfl⟩
      exact hl.1 a ha
    refine GlobalTheory.T.local_subring_integral_closure_max ((regAt M.ξ p).map i₀) (regAt M'.ξ p') (chRing o y (e c)).toSubring hRD ?_ ?_ ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩ h0 hinv
      have hu : unitAt M'.ξ p' (i₀ a) := ⟨h0, hl.1 a ha, hinv⟩
      exact ⟨a⁻¹, (hl.2 a ha hu).2.2, map_inv₀ _ _⟩
    · intro t ht
      exact hN p' t (isIntegral_mono' hRD t ht)
    · intro b hb
      exact isIntegral_mono _ _ hAR b ((hB c hc b).1 hb)
    · intro a ha
      obtain ⟨u, hu, v, hv, hvu, rfl⟩ := (hr'.2 a).1 ha
      exact ⟨u, hu, v, hv, hvu.1, hvu.2.2, rfl⟩
  refine ⟨fun p' hf => ?_, fun P hPm => ?_, hD⟩
  · obtain ⟨P, hPm, hD', -⟩ := first p' hf
    exact ⟨P, hPm, hD'⟩
  · have hBT : ∀ b : chRing o y (e c), (b : Ω') ∈ (integralClosure ((regAt M.ξ p).map i₀) Ω').toSubring := fun b =>
      isIntegral_mono _ _ hAR _ ((hB c hc b).1 b.2)
    let ι : chRing o y (e c) →+* (integralClosure ((regAt M.ξ p).map i₀) Ω').toSubring :=
      { toFun := fun b => ⟨b, hBT b⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    obtain ⟨p', ⟨hch, hmem⟩, huniq⟩ := PositivityTheory.HtPt.Ma.prime_pt o Ω' κ' y M' (e c) (hy c hc) (P.comap ι) inferInstance
    have hr' := PositivityTheory.HtPt.Ma.regat_loc o Ω' κ' y M' (e c) p' hch
    have hf : f p'.1 = p.1 := by
      refine (fibre_iff M Ω' M' f e hD hB1 hC c p hp p').2 ⟨hch, fun u hu => ?_⟩
      have hub : i₀ u ∈ chRing o y (e c) := (hB c hc _).2
        (isIntegral_algebraMap (x := (⟨_, map_chRing x Ω' c u hu⟩ : A₀ c)))
      have h1 : ι ⟨i₀ u, hub⟩ ∈ P ↔ ¬ unitAt M'.ξ p' (i₀ u) := hmem ⟨i₀ u, hub⟩
      have h2 := GlobalTheory.T.maximal_ideal_membership_of_local ((regAt M.ξ p).map i₀) P hPm (ι ⟨i₀ u, hub⟩) ⟨u, hr.1 u hu, rfl⟩
      have h3 : unitAt M.ξ p u ↔ (i₀ u ≠ 0 ∧ (i₀ u)⁻¹ ∈ (regAt M.ξ p).map i₀) := by
        refine ⟨fun h => ⟨(map_ne_zero _).2 h.1, ⟨u⁻¹, h.2.2, map_inv₀ _ _⟩⟩, ?_⟩
        rintro ⟨h0, a, ha, e'⟩
        have hu0 : u ≠ 0 := fun h => h0 (by rw [h, map_zero])
        have : a = u⁻¹ := (algebraMap Ω Ω').injective (by rw [map_inv₀]; exact e')
        exact ⟨hu0, hr.1 u hu, this ▸ ha⟩
      rw [h3]
      exact not_iff_not.1 (h2.symm.trans h1)
    obtain ⟨P', hPm', hD', hP'⟩ := first p' hf
    have e' : P = P' := by
      refine ideal_ext (A₀ c) ((regAt M.ξ p).map i₀) hAR hR P P' fun t ht => ?_
      have hb : (t : Ω') ∈ chRing o y (e c) := (hB c hc _).2 ht
      have h1 : t ∈ P ↔ ¬ unitAt M'.ξ p' (t : Ω') := hmem ⟨t, hb⟩
      rw [h1, hP' t]
      exact not_congr ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hr'.1 _ hb, h.2⟩⟩
    subst e'
    refine ⟨p', ⟨hf, hD'⟩, ?_⟩
    rintro p'' ⟨hf'', hD''⟩
    have hch'' := ((fibre_iff M Ω' M' f e hD hB1 hC c p hp p'').1 hf'').1
    have hr'' := PositivityTheory.HtPt.Ma.regat_loc o Ω' κ' y M' (e c) p'' hch''
    refine huniq p'' ⟨hch'', fun u => ?_⟩
    have h := GlobalTheory.T.prime_mem_iff_not_unit_localization _ P inferInstance (ι u)
    rw [← hD''] at h
    refine h.trans (not_congr ⟨fun h => ⟨h.1, hr''.1 _ u.2, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩)

end Sit

theorem exists_normalisation : ∀ (o : Type) [CommRing o] [Algebra.EssFiniteType ℤ o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'], ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω') (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (algebraMap Ω Ω') ∧ Flat.NormalCpt M'.ξ ∧ IsFinite f ∧ ∀ p : Cpt M.ξ, NormAt M'.ξ f (algebraMap Ω Ω') p := by
  intro o _ _ Ω _ _ κ _ x M Ω' _ _ _ _ _
  have hinj : ∀ c, x c ≠ 0 → algebraMap Ω Ω' (x c) ≠ 0 := fun c hc => by
    simpa using hc
  have hinj' : ∀ c, algebraMap Ω Ω' (x c) ≠ 0 → x c ≠ 0 := fun c hc h => hc (by simp [h])
  obtain ⟨d, n, z, hz1, hz2⟩ := GlobalTheory.T.integral_closure_chart_span o Ω' κ (fun k => algebraMap Ω Ω' (x k))
    (fun c hc => PositivityTheory.HtPt.Mb.finite_ext M Ω' c (hinj' c hc))
  set x' : κ → Ω' := fun k => algebraMap Ω Ω' (x k) with hx'
  set y := joinCo (RingHom.id Ω') x' z with hy
  obtain ⟨c₀, hc₀⟩ := exists_ne M
  have hyne : ∀ c, x c ≠ 0 → y (c, Sum.inl c) ≠ 0 := fun c hc => by
    simp only [hy, joinCo, RingHom.id_apply, hz1]
    exact mul_ne_zero (hinj c hc) (pow_ne_zero _ (hinj c hc))
  have hJ := fun c (hc : x c ≠ 0) a (ha : IsIntegral (chRing o x' c) a) =>
    join_chart (o := o) x' d n z hz1 hz2 c (hinj c hc) a ha
  obtain ⟨M'⟩ : Nonempty (PModel o y) := GlobalTheory.T.projective_model_nonempty o Ω' (κ × (κ ⊕ Fin n)) y
    ⟨(c₀, Sum.inl c₀), hyne c₀ hc₀, fun a => by
      obtain ⟨b, v, hb, hv, hv0, rfl⟩ := PositivityTheory.HtPt.Mb.frac_ext M Ω' c₀ hc₀ a
      exact ⟨b, hJ c₀ hc₀ b hb, v, hJ c₀ hc₀ v (isIntegral_algebraMap (x := (⟨v, hv⟩ : chRing o x' c₀))), rfl⟩⟩
  have hT := PositivityTheory.HtPt.Mb.norm_chart o Ω' κ x' d n z M' hz1 hz2
  have hB : ∀ c, x c ≠ 0 → ∀ a : Ω', a ∈ chRing o y (c, Sum.inl c) ↔ IsIntegral (chRing o x' c) a :=
    fun c hc => (hT c (hinj c hc)).1
  have hC : ∀ c, x c ≠ 0 → ∀ p' : Cpt M'.ξ, (∀ j, x' j / x' c ∈ regAt M'.ξ p') → InChart M'.ξ y (c, Sum.inl c) p' :=
    fun c hc => (hT c (hinj c hc)).2
  have hcov : ∀ p' : Cpt M'.ξ, ∃ c, x c ≠ 0 ∧ InChart M'.ξ y (c, Sum.inl c) p' := by
    intro p'
    obtain ⟨⟨c, k⟩, h0, h1⟩ := M'.tie.cover p'
    have hc' : x' c ≠ 0 := left_ne_zero_of_mul h0
    have hk : z k ≠ 0 := right_ne_zero_of_mul h0
    refine ⟨c, hinj' c hc', hC c (hinj' c hc') p' fun j => ?_⟩
    have := h1 (j, k)
    simp only [hy, joinCo, RingHom.id_apply] at this
    rwa [mul_div_mul_right _ _ hk] at this
  have hreg : ∀ (c : κ) (p' : Cpt M'.ξ), InChart M'.ξ y (c, Sum.inl c) p' → ∀ a ∈ chRing o x c, algebraMap Ω Ω' a ∈ regAt M'.ξ p' := by
    intro c p' hp a ha
    have hc : x c ≠ 0 := hinj' c (left_ne_zero_of_mul hp.1)
    exact (PositivityTheory.HtPt.Ma.regat_loc o Ω' _ y M' _ p' hp).1 _ ((hB c hc _).2
      (isIntegral_algebraMap (x := (⟨_, map_chRing x Ω' c a ha⟩ : chRing o x' c))))
  obtain ⟨f, hf, -⟩ := PositivityTheory.HtPt.Mb.morph o Ω κ x M o Ω' _ y M' (algebraMap Ω Ω') fun p' => by
    obtain ⟨c, hc, hp⟩ := hcov p'
    exact ⟨c, hc, hreg c p' hp⟩
  have hN : Flat.NormalCpt M'.ξ := by
    refine normal_of_charts M' {q | ∃ c, x c ≠ 0 ∧ q = (c, Sum.inl c)} (fun p' => ?_) ?_
    · obtain ⟨c, hc, hp⟩ := hcov p'
      exact ⟨_, ⟨c, hc, rfl⟩, hp⟩
    · rintro _ ⟨c, hc, rfl⟩ a ha
      rw [hB c hc]
      refine int_trans (chRing o x' c) (chRing o y (c, Sum.inl c)) (fun b hb => (hB c hc b).2
        (isIntegral_algebraMap (x := (⟨b, hb⟩ : chRing o x' c)))) (fun b hb => (hB c hc b).1 hb) a ha
  refine ⟨_, inferInstance, y, M', f, hf, hN, ?_, fun p => ?_⟩
  · refine GlobalTheory.T.dominating_model_chart_compat M Ω' M' f (fun c => (c, Sum.inl c)) hf hyne
      (fun c hc p' => chart_over M Ω' M' f _ hf (fun c hc a ha => (hB c hc a).2 ha) hC c hc p') fun c hc => ?_
    refine ⟨(Set.finite_range fun k => z k / x' c ^ d).toFinset, fun a => ?_⟩
    rw [Set.Finite.coe_toFinset]
    exact (hB c hc a).trans (hz2 c (hinj c hc) a)
  · exact normAt_of_charts M Ω' M' f (fun c => (c, Sum.inl c)) hf hyne hB hC hN p

end PositivityTheory.HtPt.Mb.LNormExists.NormEx

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

theorem PositivityTheory.HtPt.Mb.norm_exists : ∀ (o : Type) [CommRing o] [Algebra.EssFiniteType ℤ o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'], ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω') (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (algebraMap Ω Ω') ∧ Flat.NormalCpt M'.ξ ∧ IsFinite f ∧ ∀ p : Cpt M.ξ, NormAt M'.ξ f (algebraMap Ω Ω') p :=
  @PositivityTheory.HtPt.Mb.LNormExists.NormEx.exists_normalisation
end
end

section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LPullEq

theorem pull_eq_pullLoc_of_dominates : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ]
    (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E) (X' : Scheme.{0}) (Ω' : Type)
    [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (F : Type) [AddCommGroup F] [Module Ω' F]
    (j : E →+ F) (f : X' ⟶ M.X), L.IsCohOn Set.univ → Dominates ξ' M.ξ f i →
      L.pull ξ' f j = L.pullLoc ξ' i j ∧ ∀ p', p' ∈ ctrSet o x i ξ' := by
  intro o _ Ω _ _ κ _ x M E _ _ L X' Ω' _ ξ' i F _ _ j f hL hd
  have dl := PositivityTheory.HtPt.Mb.dom_local M.X Ω M.ξ X' Ω' ξ' i f hd
  refine ⟨?_, fun p' => ?_⟩
  · funext p'
    obtain ⟨h, hc⟩ := dl p'
    rw [PositivityTheory.HtPt.Mb.pullloc_centre o Ω κ x M E L X' Ω' ξ' i F j ⟨f p'.1, h⟩ p' hL hc]
    unfold Lat.pull
    congr 1
    ext e'
    constructor
    · rintro ⟨_, e, he, rfl⟩
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨h, e, he, rfl⟩
  · obtain ⟨h, h1, -⟩ := dl p'
    obtain ⟨c, hc⟩ := M.tie.cover ⟨f p'.1, h⟩
    exact ⟨c, hc.1, fun a ha => h1 a (((M.tie.ring c hc.1) a).1 ha _ hc)⟩

end PositivityTheory.HtPt.Mb.LPullEq

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

theorem PositivityTheory.HtPt.Mb.pull_eq : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (F : Type) [AddCommGroup F] [Module Ω' F] (j : E →+ F) (f : X' ⟶ M.X), L.IsCohOn Set.univ → Dominates ξ' M.ξ f i → L.pull ξ' f j = L.pullLoc ξ' i j ∧ ∀ p', p' ∈ ctrSet o x i ξ' :=
  @PositivityTheory.HtPt.Mb.LPullEq.pull_eq_pullLoc_of_dominates
end

section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LTopCommon

theorem exists_common_normal_model : ∀ (o : Type) [CommRing o] [Algebra.EssFiniteType ℤ o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω) (B : Type) [Finite B] (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module Ω (E b)] (L : ∀ b, Lat M.ξ (E b)) (V : ∀ b, Submodule Ω (E b)) [∀ b, FiniteDimensional Ω (V b)], (∀ a, ∃ l, w a l ≠ 0) → (∀ b, (L b).IsCohOn Set.univ) → (∀ b p, Submodule.span Ω (L b p : Set (E b)) = V b) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ Flat.NormalCpt M'.ξ ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ (∀ b, ((L b).pull M'.ξ f (AddMonoidHom.id (E b))).IsVB (Module.finrank Ω (V b)) (V b)) ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → (∀ b, ∃ (r : ℕ) (g : Fin r → E b), (L b).IsFrameAt g p) → NormAt M'.ξ f (RingHom.id Ω) p := by
  intro o _ _ Ω _ _ κ _ x M A _ κa _ w B _ E _ _ L V _ hw hL hV
  choose κb hκb v hv0 hv1 hv2 using fun b => PositivityTheory.HtPt.Mb.flatten o Ω κ x M (E b) (L b) (V b) (hL b) (hV b)
  let κs : A ⊕ B → Type := fun s => match s with
    | .inl a => κa a
    | .inr b => κb b
  let ws : ∀ s, κs s → Ω := fun s => match s with
    | .inl a => w a
    | .inr b => v b
  haveI : ∀ s, Finite (κs s) := fun s => match s with
    | .inl a => inferInstanceAs (Finite (κa a))
    | .inr b => hκb b
  have hws : ∀ s, ∃ l, ws s l ≠ 0 := fun s => match s with
    | .inl a => hw a
    | .inr b => hv0 b
  obtain ⟨κ₁, _, y₁, M₁, f, hf, hch, hiso⟩ := PositivityTheory.HtPt.Mb.join_many o Ω κ x M (A ⊕ B) κs ws hws
  obtain ⟨κ₂, hκ₂, y₂, M₂, g, hg, hN, -, hnorm⟩ := PositivityTheory.HtPt.Mb.norm_exists o Ω κ₁ y₁ M₁ Ω
  replace hg : Dominates M₂.ξ M₁.ξ g (RingHom.id Ω) := hg
  replace hnorm : ∀ p, NormAt M₂.ξ g (RingHom.id Ω) p := hnorm
  have hgf : Dominates M₂.ξ M.ξ (g ≫ f) (RingHom.id Ω) := by
    unfold Dominates at *
    rw [← Category.assoc, hg, Category.assoc, hf]
    simp
  have hch₂ : ∀ s (p' : Cpt M₂.ξ), ∃ l, InChart M₂.ξ (ws s) l p' := by
    intro s p'
    obtain ⟨h, h1, -⟩ := PositivityTheory.HtPt.Mb.dom_local _ Ω M₁.ξ _ Ω M₂.ξ _ g hg p'
    obtain ⟨l, hl⟩ := hch s ⟨_, h⟩
    exact ⟨l, hl.1, fun c => h1 _ (hl.2 c)⟩
  refine ⟨κ₂, hκ₂, y₂, M₂, g ≫ f, hgf, hN, fun a => hch₂ (.inl a), fun b => ?_, fun p hp hfr => ?_⟩
  · obtain ⟨e, hc⟩ := PositivityTheory.HtPt.Mb.pull_eq o Ω κ x M (E b) (L b) _ Ω M₂.ξ _ (E b) (AddMonoidHom.id _) (g ≫ f) (hL b) hgf
    have key := hv2 b _ Ω M₂.ξ (RingHom.id Ω) (E b) (AddMonoidHom.id _) ⟨fun _ _ => rfl, fun _ _ h => h⟩
    have hu : {p' | p' ∈ ctrSet o x (RingHom.id Ω) M₂.ξ ∧ ∃ l, InChart M₂.ξ (fun l => RingHom.id Ω (v b l)) l p'}
        = Set.univ := Set.eq_univ_of_forall fun p' => ⟨hc p', hch₂ (.inr b) p'⟩
    have hs : Submodule.span Ω (AddMonoidHom.id (E b) '' (V b : Set (E b))) = V b := by simp
    rw [hu, hs] at key
    rw [e]
    exact key
  · refine (PositivityTheory.HtPt.Mb.iso_comp _ Ω M.ξ _ _ Ω (RingHom.id Ω) p).1 M₁.ξ M₂.ξ f g hg (hiso p ?_) fun p₁ _ => hnorm p₁
    rintro (a | b)
    · exact hp a
    · exact hv1 b p (hfr b)

end PositivityTheory.HtPt.Mb.LTopCommon

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

theorem PositivityTheory.HtPt.Mb.top_common : ∀ (o : Type) [CommRing o] [Algebra.EssFiniteType ℤ o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω) (B : Type) [Finite B] (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module Ω (E b)] (L : ∀ b, Lat M.ξ (E b)) (V : ∀ b, Submodule Ω (E b)) [∀ b, FiniteDimensional Ω (V b)], (∀ a, ∃ l, w a l ≠ 0) → (∀ b, (L b).IsCohOn Set.univ) → (∀ b p, Submodule.span Ω (L b p : Set (E b)) = V b) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ Flat.NormalCpt M'.ξ ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ (∀ b, ((L b).pull M'.ξ f (AddMonoidHom.id (E b))).IsVB (Module.finrank Ω (V b)) (V b)) ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → (∀ b, ∃ (r : ℕ) (g : Fin r → E b), (L b).IsFrameAt g p) → NormAt M'.ξ f (RingHom.id Ω) p :=
  @PositivityTheory.HtPt.Mb.LTopCommon.exists_common_normal_model
end
