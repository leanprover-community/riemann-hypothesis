module

public import Mathlib
public import Formalism.SelfDualUnimodular.LocalLatticeDictionary.ExistsUnitNorm

@[expose] public section

noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.LatDictZ.Z0.SGB

open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0.SGA

variable {K : Type} [Field K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V]

def restr (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V) : W →ₗ⋆[K] W →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => h x y)
    (by intro x y z; simp) (by intro c x y; simp) (by intro x y z; simp) (by intro c x y; simp)

def coef (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) : V →ₗ[K] K := (h X X)⁻¹ • h X

theorem coef_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (X x : V) : coef h X x = (h X X)⁻¹ * h X x := rfl

def proj (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) : V →ₗ[K] LinearMap.ker (h X) :=
  LinearMap.codRestrict (LinearMap.ker (h X)) (LinearMap.id - (coef h X).smulRight X) (by
    intro x
    rw [LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_sub, map_smul,
      smul_eq_mul, coef_apply]
    field_simp
    ring)

theorem proj_val (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) (x : V) :
    (proj h X hX x : V) = x - coef h X x • X := rfl

theorem coef_self (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) : coef h X X = 1 := by
  rw [coef_apply, inv_mul_cancel₀ hX]

theorem coef_ker (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (w : LinearMap.ker (h X)) : coef h X w = 0 := by
  rw [coef_apply, LinearMap.mem_ker.mp w.2, mul_zero]

theorem decomp (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) (x : V) :
    x = coef h X x • X + (proj h X hX x : V) := by
  rw [proj_val]
  abel

def ext (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) :
    V →ₗ[K] V :=
  (coef h X).smulRight X + (LinearMap.ker (h X)).subtype ∘ₗ (g : _ →ₗ[K] _) ∘ₗ proj h X hX

theorem ext_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) (x : V) :
    ext h X hX g x = coef h X x • X + (g (proj h X hX x) : V) := rfl

theorem coef_ext (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) (x : V) :
    coef h X (ext h X hX g x) = coef h X x := by
  rw [ext_apply, map_add (f := _), map_smul, coef_self h X hX, coef_ker h X (g (proj h X hX x)), smul_eq_mul,
    mul_one, add_zero]

theorem proj_ext (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) (x : V) :
    proj h X hX (ext h X hX g x) = g (proj h X hX x) := by
  apply Subtype.ext
  rw [proj_val, coef_ext, ext_apply]
  abel

theorem ext_comp (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) (x : V) :
    ext h X hX g.symm (ext h X hX g x) = x := by
  rw [ext_apply, coef_ext, proj_ext, LinearEquiv.symm_apply_apply]
  exact (decomp h X hX x).symm

def extE (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (ext h X hX g) (ext h X hX g.symm)
    (by
      ext x
      have := ext_comp h X hX g.symm x
      rwa [LinearEquiv.symm_symm] at this)
    (by ext x; exact ext_comp h X hX g x)

theorem extE_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) (x : V) :
    extE h X hX g x = ext h X hX g x := rfl

theorem h_ker_X (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hs : ∀ u v, star (h u v) = h v u)
    (w : LinearMap.ker (h X)) : h w X = 0 := by
  rw [← hs X w, LinearMap.mem_ker.mp w.2, star_zero]

theorem h_decomp (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) (hs : ∀ u v, star (h u v) = h v u)
    (x y : V) :
    h x y = star (coef h X x) * coef h X y * h X X + h (proj h X hX x) (proj h X hX y) := by
  conv_lhs => rw [decomp h X hX x, decomp h X hX y]
  simp only [LinearMap.map_add₂, map_add (f := _), LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, starRingEnd_apply,
    LinearMap.add_apply, LinearMap.smul_apply]
  rw [LinearMap.mem_ker.mp (proj h X hX y).2, h_ker_X h X hs (proj h X hX x)]
  ring

theorem extE_isom (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) (hs : ∀ u v, star (h u v) = h v u)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X))
    (hg : ∀ u v, h (g u : V) (g v : V) = h (u : V) (v : V)) (x y : V) :
    h (extE h X hX g x) (extE h X hX g y) = h x y := by
  rw [h_decomp h X hX hs, h_decomp h X hX hs x y, extE_apply, extE_apply, coef_ext, coef_ext, proj_ext,
    proj_ext, hg]

variable {S : Subring K}

theorem mem_iff_split {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V} (hM : IsSelfDualMod S h M) {X : V}
    (hXM : X ∈ M) (hXu : IsUnitIn S (h X X)) (x : V) :
    x ∈ M ↔ coef h X x ∈ S ∧ (proj h X hXu.1 x : V) ∈ M := by
  constructor
  · intro hx
    have hc : coef h X x ∈ S := by
      rw [coef_apply]
      exact S.mul_mem hXu.2.2 (hM.int X hXM x hx)
    refine ⟨hc, ?_⟩
    rw [proj_val]
    exact M.sub_mem hx (hM.smul_mem _ hc X hXM)
  · rintro ⟨hc, hp⟩
    rw [decomp h X hXu.1 x]
    exact M.add_mem (hM.smul_mem _ hc X hXM) hp

theorem nondeg_restr {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : ∀ u v, star (h u v) = h v u)
    (hnd : ∀ x, (∀ y, h x y = 0) → x = 0) {X : V} (hX : h X X ≠ 0) (w : LinearMap.ker (h X))
    (hw : ∀ y, restr h (LinearMap.ker (h X)) w y = 0) : w = 0 := by
  refine Subtype.ext (hnd _ (fun z => ?_))
  rw [decomp h X hX z, map_add (f := _), map_smul, smul_eq_mul, h_ker_X h X hs w, mul_zero, zero_add]
  exact hw (proj h X hX z)

theorem symm_restr {h : V →ₗ⋆[K] V →ₗ[K] K} (hsy : h.IsSymm) (W : Submodule K V) :
    (restr h W).IsSymm := by
  first
    | exact fun x y => hsy x y
    | exact ⟨fun x y => hsy.eq x y⟩

end Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
