import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GmapEqSelfOfFix
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscIsoOfProj
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SummandLocalization

section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

def ProjInto : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ (X Y : Submodule K V) (hc : IsCompl X Y), (∀ x ∈ X, ∀ y ∈ Y, h x y = 0) →
    ∀ L : Submodule (𝓞 K) V, IsLatIn X L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
    ∀ Λ : Submodule (𝓞 K) V, (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) →
      dualF h 𝔭 Λ = Λ → Λ ⊓ X.restrictScalars (𝓞 K) = locF 𝔭 L →
      ∀ x ∈ Λ, X.projection Y hc x ∈ locF 𝔭 (dualIn h X L)

def ProjOnto : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ (X Y : Submodule K V) (hc : IsCompl X Y), (∀ x ∈ X, ∀ y ∈ Y, h x y = 0) →
    ∀ L : Submodule (𝓞 K) V, IsLatIn X L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
    ∀ Λ : Submodule (𝓞 K) V, (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) →
      dualF h 𝔭 Λ = Λ → Λ ⊓ X.restrictScalars (𝓞 K) = locF 𝔭 L →
      ∀ v ∈ locF 𝔭 (dualIn h X L), ∃ x ∈ Λ, X.projection Y hc x = v

def FibCount : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M T : Submodule (𝓞 K) V, IsLatIn U M → IsLatIn (orthK h U) T → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
      fibP h U 𝔭 M T ≠ 0 → fibP h U 𝔭 M T = discAut h (orthK h U) T 𝔭

end Formalism.L2.SG.Pf.G6

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.G6

theorem glueLoc_of (hi : ProjInto) (ho : ProjOnto) (hn : FibCount) : GlueLoc := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hcU M T hM hT 𝔭 h𝔭
  refine ⟨fun hne => ⟨?_, hn K F V hK hF h hs hnd U hcU M T hM hT 𝔭 h𝔭 hne⟩,
    fun g hg => fibP_gmap hM 𝔭 T hg⟩
  obtain ⟨⟨Λ, hΛ0, hΛd, hΛU, hΛW⟩⟩ := (Nat.card_ne_zero.mp hne).1
  have oU : ∀ x ∈ U, ∀ y ∈ orthK h U, h x y = 0 := fun x hx y hy => mem_orthK.mp hy x hx
  have oW : ∀ x ∈ orthK h U, ∀ y ∈ U, h x y = 0 := by
    intro x hx y hy
    have e := hs.eq x y
    rw [oU y hy x hx] at e
    simpa using e
  exact discIso_of_proj h hcU hΛU hΛW
    (hi K F V hK hF h hs hnd U (orthK h U) hcU oU M hM 𝔭 h𝔭 Λ hΛ0 hΛd hΛU)
    (ho K F V hK hF h hs hnd U (orthK h U) hcU oU M hM 𝔭 h𝔭 Λ hΛ0 hΛd hΛU)
    (hi K F V hK hF h hs hnd (orthK h U) U hcU.symm oW T hT 𝔭 h𝔭 Λ hΛ0 hΛd hΛW)
    (ho K F V hK hF h hs hnd (orthK h U) U hcU.symm oW T hT 𝔭 h𝔭 Λ hΛ0 hΛd hΛW)

end Formalism.L2.SG.Pf.Cnt
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mem_dual_iff {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {v : V} :
    v ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y v ∈ (1 : Submodule (𝓞 K) K) := by
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]

theorem form_ozmul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (c : 𝓞 K) (y v : V) : h y (c • v) = c • h y v := by
  rw [← algebraMap_smul K c v, LinearMap.map_smul, algebraMap_smul]

theorem form_ozmul_left_mem (h : V →ₗ⋆[K] V →ₗ[K] K) (c : 𝓞 K) {y v : V}
    (hy : h y v ∈ (1 : Submodule (𝓞 K) K)) : h (c • y) v ∈ (1 : Submodule (𝓞 K) K) := by
  rw [← algebraMap_smul K c y, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  obtain ⟨c0, hc0⟩ := Submodule.mem_one.mp (VecSplit.star_alg_mem_one c)
  obtain ⟨z0, hz0⟩ := Submodule.mem_one.mp hy
  exact Submodule.mem_one.mpr ⟨c0 * z0, by rw [map_mul, hc0, hz0]⟩

theorem mem_locF_dualIn {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} {L : Submodule (𝓞 K) V}
    (hL : L.FG) (𝔭 : Ideal (𝓞 F)) {v : V} (hv : v ∈ X)
    (H : ∀ y ∈ L, h y v ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) : v ∈ locF 𝔭 (dualIn h X L) := by
  classical
  obtain ⟨s, hs⟩ := hL
  have H' : ∀ y ∈ s, ∃ t ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s},
      t • h y v ∈ (1 : Submodule (𝓞 K) K) := by
    intro y hy
    exact H y (hs ▸ Submodule.subset_span hy)
  choose! t ht using H'
  refine ⟨∏ y ∈ s, t y, Submonoid.prod_mem _ fun y hy => (ht y hy).1, ?_⟩
  refine ⟨X.restrictScalars (𝓞 K) |>.smul_mem _ hv, ?_⟩
  show (∏ y ∈ s, t y) • v ∈ Formalism.HermitianLatticesTheory.dual h L
  rw [mem_dual_iff]
  intro y hy
  rw [← hs] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    rw [form_ozmul_right, ← Finset.prod_erase_mul s t hy, mul_smul]
    exact Submodule.smul_mem _ _ (ht y hy).2
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha => exact form_ozmul_left_mem h c ha

theorem projection_into_holds : ProjInto := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd X Y hc hXY L hL 𝔭 h𝔭 Λ hΛ0 hΛd hΛX x hx
  apply mem_locF_dualIn hL.1 𝔭 (Submodule.projection_apply_mem hc x)
  intro y hy
  have hyΛ : y ∈ Λ := by
    have : y ∈ locF 𝔭 L := LocalizedFibreSets.le_locF 𝔭 L hy
    rw [← hΛX] at this
    exact this.1
  have hyX : y ∈ X := le_of_isLatIn hL y hy
  have e := Submodule.projection_add_projection_eq_self hc x
  have h0 : h y (Y.projection X hc.symm x) = 0 := hXY y hyX _ (Submodule.projection_apply_mem _ x)
  have hx' : x ∈ dualF h 𝔭 Λ := by rw [hΛd]; exact hx
  have := hx' y hyΛ
  rw [← e, map_add, h0, add_zero] at this
  exact this

end Formalism.L2.SG.Pf.G6
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

def SummandLoc : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    ∀ X : Submodule K V, ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ Λ : Submodule (𝓞 K) V,
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) →
      ∃ π : V →ₗ[K] V, (∀ v, π v ∈ X) ∧ (∀ x ∈ X, π x = x) ∧ ∀ y ∈ Λ, π y ∈ Λ

def RieszH : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h → ∀ f : V →ₗ[K] K, ∃ x : V, ∀ y, h x y = f y

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem coe_algebraMap_OF (t : 𝓞 F) :
    ((algebraMap (𝓞 F) (𝓞 K) t : 𝓞 K) : K) = algebraMap F K (t : F) := by
  change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = _
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]

theorem form_mem_locF_of (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V}
    {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsPrime) {v y : V}
    (hv : v ∈ locF 𝔭 (dualIn h X L)) (hy : y ∈ locF 𝔭 L) : h y v ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  have := h𝔭
  obtain ⟨t, ht, hty⟩ := (LocalSpans.mem_locF 𝔭 L y).1 hy
  obtain ⟨u, hu, huv⟩ := (LocalSpans.mem_locF 𝔭 _ v).1 hv
  have H := (mem_dual_iff.1 huv.2) _ hty
  refine (LocalSpans.mem_locF 𝔭 _ _).2 ⟨t * u, fun hm => (h𝔭.mem_or_mem hm).elim ht hu, ?_⟩
  have hst : starRingEnd K (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t)) =
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) := by
    have e := coe_algebraMap_OF (K := K) t
    change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = _ at e
    rw [e, starRingEnd_apply]
    exact (hF _).2 ⟨_, rfl⟩
  rw [form_ozmul_right, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) y, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, hst, algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) (h y v)] at H
  rw [map_mul, mul_smul, smul_comm]
  exact H

theorem riesz_hermitian_holds : RieszH := by
  intro K V _ _ _ _ _ h _ hnd f
  classical
  let b := Module.finBasis K V
  let Φ : (Fin (finrank K V) → K) →ₗ[K] Module.Dual K V :=
    { toFun := fun c => ∑ i, c i • h (b i)
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by simp [Finset.smul_sum, smul_smul] }
  have hΦ : ∀ c, h (∑ i, star (c i) • b i) = Φ c := by
    intro c
    simp [Φ, map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply, star_star]
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have hx : (∑ i, star (c i) • b i) = 0 := by
      apply hnd
      intro y
      rw [hΦ, hc]
      rfl
    funext i
    have := Fintype.linearIndependent_iff.mp b.linearIndependent (fun i => star (c i)) hx i
    simpa using this
  have hsurj : Function.Surjective Φ := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
    rw [Module.finrank_fin_fun, Subspace.dual_finrank_eq]
  obtain ⟨c, hc⟩ := hsurj f
  exact ⟨∑ i, star (c i) • b i, fun y => by rw [hΦ, hc]⟩

theorem mem_of_smul_mem {X : Submodule K V} {𝔭 : Ideal (𝓞 F)} {u : 𝓞 F} (hu : u ∉ 𝔭) {v : V}
    (hv : algebraMap (𝓞 F) (𝓞 K) u • v ∈ X) : v ∈ X := by
  have hu0 : (u : F) ≠ 0 := by
    intro e
    apply hu
    have : u = 0 := RingOfIntegers.ext (by simpa using e)
    rw [this]
    exact 𝔭.zero_mem
  have hc0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u) ≠ 0 := by
    have e := coe_algebraMap_OF (K := K) u
    change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u) = _ at e
    rw [e]
    exact (map_ne_zero _).2 hu0
  have h1 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u) • v ∈ X := by
    rw [algebraMap_smul]
    exact hv
  have := X.smul_mem (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u))⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this

theorem projOnto_of (hS : SummandLoc) (hR : RieszH) : ProjOnto := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd X Y hc hXY L hL 𝔭 h𝔭 Λ hΛ0 hΛd hΛX v hv
  have hp : 𝔭.IsPrime := h𝔭.isPrime
  obtain ⟨π, hπX, hπid, hπΛ⟩ := hS K F V X 𝔭 h𝔭 Λ hΛ0
  obtain ⟨x, hx⟩ := hR K V h hs hnd ((h v).comp π)
  have key : ∀ y, h y x = h (π y) v := by
    intro y
    rw [← hs.eq x y, hx y, LinearMap.comp_apply, hs.eq v (π y)]
  have hvX : v ∈ X := by
    obtain ⟨u, hu, huv⟩ := (LocalSpans.mem_locF 𝔭 _ v).1 hv
    exact mem_of_smul_mem hu huv.1
  have hxΛ : x ∈ Λ := by
    rw [← hΛd]
    show ∀ y ∈ Λ, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
    intro y hy
    rw [key]
    have : π y ∈ locF 𝔭 L := by
      rw [← hΛX]
      exact ⟨hπΛ y hy, hπX y⟩
    exact form_mem_locF_of hF hp hv this
  refine ⟨x, hxΛ, ?_⟩
  set w := X.projection Y hc x - v with hw
  have hwX : w ∈ X := X.sub_mem (Submodule.projection_apply_mem hc x) hvX
  have hw0 : w = 0 := by
    apply hnd
    intro z
    have ez := Submodule.projection_add_projection_eq_self hc z
    rw [← ez, map_add]
    have h1 : h w (Y.projection X hc.symm z) = 0 := hXY w hwX _ (Submodule.projection_apply_mem _ z)
    have hzX : X.projection Y hc z ∈ X := Submodule.projection_apply_mem hc z
    have ex := Submodule.projection_add_projection_eq_self hc x
    have e3 : h (X.projection Y hc z) (X.projection Y hc x) = h (X.projection Y hc z) x := by
      conv_rhs => rw [← ex]
      rw [map_add, hXY _ hzX _ (Submodule.projection_apply_mem _ x), add_zero]
    have h2 : h (X.projection Y hc z) w = 0 := by
      rw [hw, map_sub, e3, key, hπid _ hzX, sub_self]
    rw [h1, add_zero, ← hs.eq (X.projection Y hc z) w, h2, map_zero]
  exact sub_eq_zero.mp hw0

end Formalism.L2.SG.Pf.G6
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.LocalSpans

theorem summand_localization : SummandLoc :=
  _root_.UpperTheory.Reformulated.B.SummandLocalization.summand_localization

end Formalism.L2.SG.Pf.G6
end
end
