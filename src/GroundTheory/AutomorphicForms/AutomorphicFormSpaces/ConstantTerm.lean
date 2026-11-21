import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.HasModerateGrowthZero

section
open NumberField IsDedekindDomain Topology Filter Set
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace AutomorphicForm

set_option linter.unusedSectionVars false

theorem exists_finset_eval_eq_zero {X : Type*} (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W] :
    ∃ S : Finset X, ∀ w ∈ W, (∀ x ∈ S, w x = 0) → w = 0 := by
  classical
  let kerS : Finset X → Submodule ℂ W := fun S =>
    ⨅ x ∈ S, LinearMap.ker ((LinearMap.proj (R := ℂ) (φ := fun _ : X => ℂ) x).comp W.subtype)
  have mem_kerS : ∀ (S : Finset X) (w : W), w ∈ kerS S ↔ ∀ x ∈ S, (w : X → ℂ) x = 0 := by
    intro S w
    simp only [kerS, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, LinearMap.coe_proj, Function.eval]
  have key : ∀ m : ℕ, ∀ S : Finset X, Module.finrank ℂ (kerS S) = m →
      ∃ S' : Finset X, kerS S' = ⊥ := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro S hS
      by_cases h : kerS S = ⊥
      · exact ⟨S, h⟩
      · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
        have : ∃ x, (w : X → ℂ) x ≠ 0 := by
          by_contra hc
          push Not at hc
          exact hw0 (Subtype.ext (funext hc))
        obtain ⟨x, hx⟩ := this
        have hle : kerS (insert x S) ≤ kerS S := fun v hv =>
          (mem_kerS S v).2 fun y hy => (mem_kerS _ v).1 hv y (Finset.mem_insert_of_mem hy)
        have hne : kerS (insert x S) ≠ kerS S := by
          intro e
          rw [← e] at hw
          exact hx ((mem_kerS _ w).1 hw x (Finset.mem_insert_self x S))
        have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)
        exact ih _ (hS ▸ hlt) _ rfl
  obtain ⟨S, hS⟩ := key _ ∅ rfl
  refine ⟨S, fun w hw h0 => ?_⟩
  have : (⟨w, hw⟩ : W) ∈ kerS S := (mem_kerS S _).2 h0
  rw [hS, Submodule.mem_bot] at this
  exact congrArg Subtype.val this

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

open Reduction

abbrev finPart (g : AdelicGLn.AdelicGL K n) : AdelicGLn.FiniteAdelicGL K n :=
  (AdelicGLn.prodEquiv K n g).2

theorem inv_mul_finEmb_mul (k : AdelicGLn.AdelicGL K n) (y : AdelicGLn.FiniteAdelicGL K n) :
    k⁻¹ * finEmb K n y * k = finEmb K n ((finPart k)⁻¹ * y * finPart k) := by
  apply (AdelicGLn.prodEquiv K n).injective
  rw [map_mul, map_mul, map_inv, prodEquiv_finEmb, prodEquiv_finEmb]
  ext <;> simp [finPart]

theorem finEmb_mem_maxCompact {y : AdelicGLn.FiniteAdelicGL K n}
    (hy : y ∈ AdelicGLn.integralFiniteGL K n) : finEmb K n y ∈ maxCompact := by
  rw [AdelicGLn.mem_integralFiniteGL_iff_forall] at hy
  refine ⟨fun w => ?_, fun v => ?_⟩
  · have : infAt w (finEmb K n y) = 1 := by
      show (AdelicGLn.infiniteEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n y)).1) w = 1
      rw [prodEquiv_finEmb, map_one]
      rfl
    rw [this]
    exact one_mem _
  · have : finAt v (finEmb K n y) = AdelicGLn.finiteRestrictedEquiv K n y v := by
      show (AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n y)).2) v = _
      rw [prodEquiv_finEmb]
    rw [this]
    exact hy v

theorem rightTranslate_one' {M : Type*} [MulOneClass M] {F : Type*} (f : M → F) :
    rightTranslate (1 : M) f = f := by
  funext g
  simp only [rightTranslate, mul_one]

theorem rightTranslate_mul' {M : Type*} [Semigroup M] {F : Type*} (a b : M)
    (f : M → F) : rightTranslate (a * b) f = rightTranslate a (rightTranslate b f) := by
  funext g
  simp only [rightTranslate, mul_assoc]

theorem IsSmooth.eventually_mul_finEmb_mul {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsSmooth φ)
    (g k : AdelicGLn.AdelicGL K n) :
    ∀ᶠ y in 𝓝 (1 : AdelicGLn.FiniteAdelicGL K n), φ (g * finEmb K n y * k) = φ (g * k) := by
  have hc : Tendsto (fun y : AdelicGLn.FiniteAdelicGL K n => (finPart k)⁻¹ * y * finPart k)
      (𝓝 1) (𝓝 1) := by
    have : Continuous fun y : AdelicGLn.FiniteAdelicGL K n => (finPart k)⁻¹ * y * finPart k :=
      (continuous_const.mul continuous_id).mul continuous_const
    simpa using this.tendsto 1
  refine (hc.eventually (hφ.2 (g * k))).mono fun y hy => ?_
  rw [← hy, ← inv_mul_finEmb_mul]
  congr 1
  group

theorem exists_openSubgroup_rightInvariant {φ : AdelicGLn.AdelicGL K n → ℂ} (hs : IsSmooth φ)
    (hk : IsKFinite φ) :
    ∃ U : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n),
      (U : Set (AdelicGLn.FiniteAdelicGL K n)) ⊆ AdelicGLn.integralFiniteGL K n ∧
        ∀ g, ∀ u ∈ U, φ (g * finEmb K n u) = φ g := by
  classical
  set Kc := (maxCompact : Subgroup (AdelicGLn.AdelicGL K n))
  set s : Set (AdelicGLn.AdelicGL K n → ℂ) :=
    range fun k : Kc => rightTranslate (k : AdelicGLn.AdelicGL K n) φ with hs_def
  set W := Submodule.span ℂ s
  have : FiniteDimensional ℂ W := hk
  obtain ⟨S, hS⟩ := exists_finset_eval_eq_zero W
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent ℂ s
  have hbfin : b.Finite := by
    have hli : LinearIndependent ℂ (fun x : b => (⟨(x : AdelicGLn.AdelicGL K n → ℂ),
        Submodule.subset_span (hbs x.2)⟩ : W)) := by
      apply LinearIndependent.of_comp W.subtype
      exact hbli
    exact Set.finite_coe_iff.1 hli.finite

  have hbk : ∀ w ∈ b, ∃ k : Kc, w = rightTranslate (k : AdelicGLn.AdelicGL K n) φ := by
    intro w hw
    obtain ⟨k, hk⟩ := hbs hw
    exact ⟨k, hk.symm⟩

  have hstab : ∀ u ∈ AdelicGLn.integralFiniteGL K n, ∀ w ∈ W,
      rightTranslate (finEmb K n u) w ∈ W := by
    intro u hu w hw
    refine Submodule.span_induction (p := fun w _ => rightTranslate (finEmb K n u) w ∈ W)
      ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨k, rfl⟩
      rw [← rightTranslate_mul']
      exact Submodule.subset_span ⟨⟨_, mul_mem (finEmb_mem_maxCompact hu) k.2⟩, rfl⟩
    · exact W.zero_mem
    · intro x y _ _ hx hy
      exact W.add_mem hx hy
    · intro c x _ hx
      exact W.smul_mem c hx

  have hnhds : ∀ᶠ u in 𝓝 (1 : AdelicGLn.FiniteAdelicGL K n),
      u ∈ AdelicGLn.integralFiniteGL K n ∧
        ∀ w ∈ hbfin.toFinset, ∀ x ∈ S, w (x * finEmb K n u) = w x := by
    have h0 : ∀ᶠ u in 𝓝 (1 : AdelicGLn.FiniteAdelicGL K n), u ∈ AdelicGLn.integralFiniteGL K n :=
      (AdelicGLn.isOpen_integralFiniteGL K n).mem_nhds (one_mem _)
    refine h0.and ?_
    rw [eventually_all_finset]
    intro w hw
    rw [eventually_all_finset]
    intro x _
    obtain ⟨k, rfl⟩ := hbk w (hbfin.mem_toFinset.1 hw)
    simpa only [rightTranslate] using hs.eventually_mul_finEmb_mul x k

  let H : Subgroup (AdelicGLn.FiniteAdelicGL K n) :=
    { carrier := {u | u ∈ AdelicGLn.integralFiniteGL K n ∧
        ∀ w ∈ W, rightTranslate (finEmb K n u) w = w}
      one_mem' := ⟨one_mem _, fun w _ => by rw [map_one, rightTranslate_one']⟩
      mul_mem' := fun {u v} hu hv => ⟨mul_mem hu.1 hv.1, fun w hw => by
        rw [map_mul, rightTranslate_mul', hv.2 w hw, hu.2 w hw]⟩
      inv_mem' := fun {u} hu => ⟨inv_mem hu.1, fun w hw => by
        have := congrArg (rightTranslate (finEmb K n u⁻¹)) (hu.2 w hw)
        rw [← rightTranslate_mul', ← map_mul, inv_mul_cancel, map_one, rightTranslate_one'] at this
        exact this.symm⟩ }
  have hHnhds : (H : Set (AdelicGLn.FiniteAdelicGL K n)) ∈ 𝓝 1 := by
    refine Filter.mem_of_superset hnhds fun u hu => ⟨hu.1, fun w hw => ?_⟩

    rw [show W = Submodule.span ℂ b from hbspan.symm] at hw
    refine Submodule.span_induction (p := fun w _ => rightTranslate (finEmb K n u) w = w)
      ?_ ?_ ?_ ?_ hw
    · intro w hwb
      have hwW : w ∈ W := Submodule.subset_span (hbs hwb)
      have hd := W.sub_mem (hstab u hu.1 w hwW) hwW
      have := hS _ hd fun x hx => by
        simp only [Pi.sub_apply, rightTranslate]
        rw [hu.2 w (hbfin.mem_toFinset.2 hwb) x hx, sub_self]
      exact sub_eq_zero.1 this
    · rfl
    · intro x y _ _ hx hy
      rw [show rightTranslate (finEmb K n u) (x + y) =
        rightTranslate (finEmb K n u) x + rightTranslate (finEmb K n u) y from rfl, hx, hy]
    · intro c x _ hx
      rw [show rightTranslate (finEmb K n u) (c • x) = c • rightTranslate (finEmb K n u) x from rfl,
        hx]
  refine ⟨⟨H, Subgroup.isOpen_of_mem_nhds H hHnhds⟩, fun u hu => hu.1, fun g u hu => ?_⟩
  have hφW : φ ∈ W := Submodule.subset_span ⟨1, rightTranslate_one' φ⟩
  exact congrFun (hu.2 φ hφW) g

theorem continuous_of_isSmooth_of_isKFinite {φ : AdelicGLn.AdelicGL K n → ℂ} (hs : IsSmooth φ)
    (hk : IsKFinite φ) : Continuous φ := by
  obtain ⟨U, -, hU⟩ := exists_openSubgroup_rightInvariant hs hk
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  let e : AdelicGLn.AdelicGL K n → AdelicGLn.InfiniteAdelicGL K n × AdelicGLn.FiniteAdelicGL K n :=
    fun g => AdelicGLn.prodEquiv K n (g₀⁻¹ * g)
  have he : Continuous e :=
    (AdelicGLn.prodEquiv K n).continuous.comp (continuous_const.mul continuous_id)
  let F : AdelicGLn.InfiniteAdelicGL K n × AdelicGLn.FiniteAdelicGL K n → ℂ :=
    fun p => φ (g₀ * infEmb K n (archEquiv K n p.1) * finEmb K n p.2)
  have hφF : φ = F ∘ e := by
    funext g
    simp only [F, e, Function.comp_apply, mul_assoc]
    rw [infEmb_mul_finEmb, mul_inv_cancel_left]
  have hslice : Continuous (archSlice φ g₀) := by
    letI := (isExpLieAlgebra K n).chartedSpace
    exact (hs.1 g₀).continuous
  have hF : ContinuousAt F (e g₀) := by
    have hFeq : F =ᶠ[𝓝 (e g₀)] fun p => archSlice φ g₀ (archEquiv K n p.1) := by
      have he1 : e g₀ = 1 := by simp only [e, inv_mul_cancel, map_one]
      have hmem : (univ ×ˢ (U : Set (AdelicGLn.FiniteAdelicGL K n))) ∈ 𝓝 (e g₀) := by
        rw [he1]
        exact prod_mem_nhds univ_mem (U.isOpen.mem_nhds (one_mem U))
      filter_upwards [hmem] with p hp
      exact hU _ p.2 hp.2
    refine ContinuousAt.congr ?_ hFeq.symm
    exact (hslice.comp ((archEquiv K n).continuous.comp continuous_fst)).continuousAt
  rw [hφF]
  exact hF.comp he.continuousAt

theorem IsAutomorphicForm.continuous {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsAutomorphicForm φ) :
    Continuous φ :=
  continuous_of_isSmooth_of_isKFinite hφ.isSmooth hφ.isKFinite

end AutomorphicForm

end

end GroundTheory.Automorphic
end

section
open NumberField IsDedekindDomain Topology Filter Set MeasureTheory
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace AutomorphicForm

set_option linter.unusedSectionVars false

abbrev UPos (n r : ℕ) : Type := {p : Fin n × Fin n // (p.1 : ℕ) < r ∧ r ≤ (p.2 : ℕ)}

section Ring

variable {n r : ℕ} {R : Type*} [CommRing R]

def blockEntry (X : UPos n r → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if h : (i : ℕ) < r ∧ r ≤ (j : ℕ) then X ⟨(i, j), h⟩ else 0

theorem blockEntry_apply (X : UPos n r → R) (i j : Fin n) :
    blockEntry X i j = if h : (i : ℕ) < r ∧ r ≤ (j : ℕ) then X ⟨(i, j), h⟩ else 0 := rfl

theorem blockEntry_mul_blockEntry (X Y : UPos n r → R) : blockEntry X * blockEntry Y = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [blockEntry_apply, blockEntry_apply]
  split_ifs with h1 h2
  · omega
  · rw [mul_zero]
  · rw [zero_mul]
  · rw [zero_mul]

theorem blockEntry_add (X Y : UPos n r → R) : blockEntry (X + Y) = blockEntry X + blockEntry Y := by
  ext i j
  simp only [blockEntry_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

theorem blockEntry_zero : blockEntry (0 : UPos n r → R) = 0 := by
  ext i j
  simp only [blockEntry_apply, Matrix.zero_apply, Pi.zero_apply]
  split_ifs <;> rfl

def unipMatrix (X : UPos n r → R) : Matrix (Fin n) (Fin n) R := 1 + blockEntry X

theorem unipMatrix_mul (X Y : UPos n r → R) : unipMatrix X * unipMatrix Y = unipMatrix (X + Y) := by
  simp only [unipMatrix, mul_add, add_mul, one_mul, mul_one, blockEntry_mul_blockEntry, add_zero,
    blockEntry_add]
  abel

theorem unipMatrix_zero : unipMatrix (0 : UPos n r → R) = 1 := by
  simp [unipMatrix, blockEntry_zero]

def unipGL (X : UPos n r → R) : GL (Fin n) R :=
  ⟨unipMatrix X, unipMatrix (-X), by rw [unipMatrix_mul, add_neg_cancel, unipMatrix_zero],
    by rw [unipMatrix_mul, neg_add_cancel, unipMatrix_zero]⟩

@[simp] theorem coe_unipGL (X : UPos n r → R) :
    ((unipGL X : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = unipMatrix X := rfl

theorem coe_unipGL_inv (X : UPos n r → R) :
    (((unipGL X)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = unipMatrix (-X) := rfl

theorem unipGL_add (X Y : UPos n r → R) : unipGL (X + Y) = unipGL X * unipGL Y :=
  Units.ext (unipMatrix_mul X Y).symm

theorem unipGL_zero : unipGL (0 : UPos n r → R) = 1 := Units.ext unipMatrix_zero

theorem unipGL_injective : Function.Injective (unipGL : (UPos n r → R) → GL (Fin n) R) := by
  intro X Y h
  funext p
  have := congrArg (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2) h
  simp only [coe_unipGL, unipMatrix, Matrix.add_apply, blockEntry_apply, dif_pos p.2] at this
  simpa using this

end Ring

variable {K : Type*} [Field K] [NumberField K] {n r : ℕ}

theorem diagonal_unipGL (ξ : UPos n r → K) :
    AdelicGLn.diagonal K n (unipGL ξ) = unipGL (fun p => algebraMap K 𝔸[K] (ξ p)) := by
  ext i j
  simp only [AdelicGLn.diagonal_apply, coe_unipGL, unipMatrix, Matrix.add_apply, blockEntry_apply,
    Matrix.one_apply]
  split_ifs <;> simp

theorem continuous_unipMatrix :
    Continuous (unipMatrix : (UPos n r → 𝔸[K]) → Matrix (Fin n) (Fin n) 𝔸[K]) := by
  refine continuous_const.add (continuous_pi fun i => continuous_pi fun j => ?_)
  simp only [blockEntry_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem continuous_unipGL :
    Continuous (unipGL : (UPos n r → 𝔸[K]) → AdelicGLn.AdelicGL K n) :=
  Units.continuous_iff.2 ⟨continuous_unipMatrix, continuous_unipMatrix.comp continuous_neg⟩

variable (K n r)

abbrev unipMeasure : Measure (UPos n r → 𝔸[K]) := Measure.pi fun _ => GroundTheory.Global.adeleMeasure K

def unipFundamentalDomain : Set (UPos n r → 𝔸[K]) :=
  Set.univ.pi fun _ => GroundTheory.Global.fundamentalSet K

def unipLattice : AddSubgroup (UPos n r → 𝔸[K]) :=
  (AddMonoidHom.compLeft (algebraMap K 𝔸[K]).toAddMonoidHom (UPos n r)).range

variable {K n r}

instance countable_unipLattice : Countable (unipLattice K n r) := by
  have := GroundTheory.Global.countable_numberField K
  have e : (unipLattice K n r : Set (UPos n r → 𝔸[K])) =
      Set.range (AddMonoidHom.compLeft (algebraMap K 𝔸[K]).toAddMonoidHom (UPos n r)) :=
    AddMonoidHom.coe_range _
  have hc : (unipLattice K n r : Set (UPos n r → 𝔸[K])).Countable := e ▸ Set.countable_range _
  exact hc.to_subtype

theorem measurableSet_unipFundamentalDomain : MeasurableSet (unipFundamentalDomain K n r) :=
  MeasurableSet.univ_pi fun _ => GroundTheory.Global.measurableSet_fundamentalSet K

theorem isAddFundamentalDomain_unipFundamentalDomain :
    IsAddFundamentalDomain (unipLattice K n r) (unipFundamentalDomain K n r)
      (unipMeasure K n r) := by
  classical
  refine IsAddFundamentalDomain.mk' measurableSet_unipFundamentalDomain.nullMeasurableSet
    fun X => ?_
  choose k hk huniq using fun p => GroundTheory.Global.existsUnique_sub_mem_fundamentalSet K (X p)
  refine ⟨⟨fun p => algebraMap K 𝔸[K] (-k p), fun p => -k p, rfl⟩, ?_, ?_⟩
  · intro p _
    change algebraMap K 𝔸[K] (-k p) + X p ∈ GroundTheory.Global.fundamentalSet K
    rw [map_neg, neg_add_eq_sub]
    exact hk p
  · rintro ⟨_, ξ, rfl⟩ h
    refine Subtype.ext (funext fun p => ?_)
    have hp : algebraMap K 𝔸[K] (ξ p) + X p ∈ GroundTheory.Global.fundamentalSet K := h p (mem_univ p)
    have : -ξ p = k p := huniq p (-ξ p) (by
      show X p - algebraMap K 𝔸[K] (-ξ p) ∈ GroundTheory.Global.fundamentalSet K
      rwa [map_neg, sub_neg_eq_add, add_comm])
    change algebraMap K 𝔸[K] (ξ p) = algebraMap K 𝔸[K] (-k p)
    rw [← this, neg_neg]

theorem exists_isCompact_superset_unipFundamentalDomain :
    ∃ C, IsCompact C ∧ unipFundamentalDomain K n r ⊆ C := by
  refine ⟨Set.univ.pi fun _ => closure (GroundTheory.Global.fundamentalSetInfinite K) ×ˢ
    (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)),
    isCompact_univ_pi fun _ => (GroundTheory.Global.isCompact_closure_fundamentalSetInfinite K).prod
      (GroundTheory.Global.isCompact_integralFiniteAdeles K), ?_⟩
  intro X hX p _
  exact ⟨subset_closure (hX p (mem_univ p)).1, (hX p (mem_univ p)).2⟩

variable (r) in

def constantTerm (φ : AdelicGLn.AdelicGL K n → ℂ) (g : AdelicGLn.AdelicGL K n) : ℂ :=
  ∫ X in unipFundamentalDomain K n r, φ (unipGL X * g) ∂unipMeasure K n r

theorem IsLeftInvariant.unipGL_vadd {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsLeftInvariant φ)
    (g : AdelicGLn.AdelicGL K n) (ξ : unipLattice K n r) (X : UPos n r → 𝔸[K]) :
    φ (unipGL (ξ +ᵥ X) * g) = φ (unipGL X * g) := by
  obtain ⟨_, ξ, rfl⟩ := ξ
  change φ (unipGL ((fun p => algebraMap K 𝔸[K] (ξ p)) + X) * g) = _
  rw [unipGL_add, ← diagonal_unipGL, mul_assoc, hφ]

theorem constantTerm_eq_setIntegral {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsLeftInvariant φ)
    {D : Set (UPos n r → 𝔸[K])}
    (hD : IsAddFundamentalDomain (unipLattice K n r) D (unipMeasure K n r))
    (g : AdelicGLn.AdelicGL K n) :
    constantTerm r φ g = ∫ X in D, φ (unipGL X * g) ∂unipMeasure K n r :=
  isAddFundamentalDomain_unipFundamentalDomain.setIntegral_eq hD fun ξ X => hφ.unipGL_vadd g ξ X

theorem integrableOn_constantTerm {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : Continuous φ)
    (g : AdelicGLn.AdelicGL K n) :
    IntegrableOn (fun X => φ (unipGL X * g)) (unipFundamentalDomain K n r) (unipMeasure K n r) := by
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  have hc : Continuous fun X : UPos n r → 𝔸[K] => φ (unipGL X * g) :=
    hφ.comp (continuous_unipGL.mul continuous_const)
  exact (hc.continuousOn.integrableOn_compact hC).mono_set hDC

theorem constantTerm_add {φ ψ : AdelicGLn.AdelicGL K n → ℂ} (hφ : Continuous φ)
    (hψ : Continuous ψ) (g : AdelicGLn.AdelicGL K n) :
    constantTerm r (φ + ψ) g = constantTerm r φ g + constantTerm r ψ g :=
  integral_add (integrableOn_constantTerm hφ g) (integrableOn_constantTerm hψ g)

theorem constantTerm_smul (c : ℂ) (φ : AdelicGLn.AdelicGL K n → ℂ) (g : AdelicGLn.AdelicGL K n) :
    constantTerm r (c • φ) g = c • constantTerm r φ g :=
  integral_smul c _

theorem constantTerm_zero (g : AdelicGLn.AdelicGL K n) :
    constantTerm r (0 : AdelicGLn.AdelicGL K n → ℂ) g = 0 := by
  simp [constantTerm]

theorem constantTerm_rightTranslate (φ : AdelicGLn.AdelicGL K n → ℂ) (h g : AdelicGLn.AdelicGL K n) :
    constantTerm r (rightTranslate h φ) g = constantTerm r φ (g * h) := by
  simp only [constantTerm, rightTranslate, mul_assoc]

def IsCuspidal (φ : AdelicGLn.AdelicGL K n → ℂ) : Prop :=
  ∀ r : ℕ, 0 < r → r < n → ∀ g, constantTerm r φ g = 0

variable (K n) in

def cuspForms : Submodule ℂ (AdelicGLn.AdelicGL K n → ℂ) where
  carrier := {φ | IsAutomorphicForm φ ∧ IsCuspidal φ}
  zero_mem' := ⟨isAutomorphicForm_zero, fun r _ _ g => constantTerm_zero g⟩
  add_mem' {φ ψ} hφ hψ := ⟨hφ.1.add hψ.1, fun r hr hrn g => by
    rw [constantTerm_add hφ.1.continuous hψ.1.continuous, hφ.2 r hr hrn g, hψ.2 r hr hrn g,
      add_zero]⟩
  smul_mem' c φ hφ := ⟨hφ.1.smul c, fun r hr hrn g => by
    rw [constantTerm_smul, hφ.2 r hr hrn g, smul_zero]⟩

theorem mem_cuspForms {φ : AdelicGLn.AdelicGL K n → ℂ} :
    φ ∈ cuspForms K n ↔ IsAutomorphicForm φ ∧ IsCuspidal φ :=
  Iff.rfl

theorem cuspForms_le_automorphicForms : cuspForms K n ≤ automorphicForms K n :=
  fun _ hφ => hφ.1

end AutomorphicForm

end

end GroundTheory.Automorphic
end
