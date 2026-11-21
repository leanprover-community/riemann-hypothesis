import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevB
import Formalism.LocalToGlobal.GroupLattices.FockModels.Cartan
import Formalism.LocalToGlobal.GroupLattices.FockModels.WeylDim
import Formalism.LocalToGlobal.GroupLattices.FockModels.SpanTopOf
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsLat
import Formalism.LocalToGlobal.GroupLattices.FockModels.OperatorsPreserveLattices
import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.DataForm
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.DeterminantTwistRowActionMem
import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.ExampleFunctionModuleEqSpan
import Formalism.SharpRestriction.InertJacobiLevels.ExtraGatC
import Formalism.LocalRingCardinality.Lemmas

section
open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model

section Weyl

variable {O Kf : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [CharZero Kf]

theorem Dl0_le (m : ℕ) (lam : Fin (m + 1) → ℤ) (Λ : Submodule O (Fin (m + 1) → Kf)) (hΛ : IsLattice O Λ) :
    Dl0 O m lam Λ ≤ (dualWeyl Kf (m + 1) (m + 1) (nuOf lam)).restrictScalars O := by
  unfold Dl0
  split_ifs with hanti
  · obtain ⟨g, hg, rfl⟩ := hΛ
    refine (iInf_le _ g).trans ((iInf_le _ ⟨hg, rfl⟩).trans ?_)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨w0, hw0, hw0x⟩ := hx
    have hnu : Antitone (nuOf lam) := toNat_antitone lam hanti
    have h1 : (mapAlgHom (Algebra.ofId O Kf)).toLinearMap w0 ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam) :=
      dualWeylMap O Kf (algebraMap O Kf) _ _ _ w0 (weylLeDual O _ _ le_rfl _ hnu hw0)
    have h2 : x = rowAct Kf g⁻¹ (rowAct Kf g x) := by
      rw [rowAct_inv_left Kf _ _ g hg]
    have h3 : x ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam) := by
      rw [h2]
      refine dualWeylRowStable Kf _ _ _ g⁻¹ _ ?_
      have : rowAct Kf g x = (mapAlgHom (Algebra.ofId O Kf)).toLinearMap w0 := hw0x.symm
      rw [this]; exact h1
    exact (dualWeyl Kf (m + 1) (m + 1) (nuOf lam)).smul_mem _ h3
  · exact bot_le

end Weyl

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf)

abbrev nuV (v : Fin P.nV) (s : Fin (P.n' v)) : Fin (P.m + 1) → ℕ := nuOf (lamAt (P.lam0 v) s)

theorem nuV_anti (v : Fin P.nV) (s : Fin (P.n' v)) : Antitone (nuV P v s) :=
  toNat_antitone _ (lamAt_antitone' _ (P.dom v) s)

abbrev IdxV (v : Fin P.nV) (s : Fin (P.n' v)) : Type := ↥(ssIdx (P.m + 1) (P.m + 1) (nuV P v s))

instance (v : Fin P.nV) (s : Fin (P.n' v)) : Finite (IdxV P v s) := (sSIdxFinite _ _ _).to_subtype

def bV (v : Fin P.nV) (s : Fin (P.n' v)) : IdxV P v s → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf :=
  (sSBasis Kf (P.m + 1) (P.m + 1) (nuV P v s)).choose

theorem bV_spec (v : Fin P.nV) (s : Fin (P.n' v)) :
    IsWeightBasis Kf (P.m + 1) (P.m + 1) (nuV P v s) (bV P v s) (fun i => rowWt i.1) :=
  (sSBasis Kf (P.m + 1) (P.m + 1) (nuV P v s)).choose_spec.1

def prodF (F : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf) : P.Xsp :=
  ∏ v, P.vEmb v (∏ s, blockEmb Kf s (F v s))

def BI (I : ∀ v s, IdxV P v s) : P.Xsp := prodF P fun v s => bV P v s (I v s)

def EV : P.Xsp := prodF P fun v s => hw Kf le_rfl (nuV P v s)

theorem htupW_le (L : P.Tup) (hL : ∀ v (s : Fin (P.n' v)), IsLattice O (extO O (P.ι v) (P.σ v) s.val (L v))) :
    P.HtupW L ≤ (Submodule.span Kf (Set.range (BI P))).restrictScalars O := by
  classical
  let Tv : ∀ v, Submodule Kf (MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) Kf) := fun v =>
    Submodule.span Kf {X | ∃ I : ∀ s, IdxV P v s, X = ∏ s, blockEmb Kf s (bV P v s (I s))}
  have hv : ∀ v, HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val (L v)) ≤ (Tv v).restrictScalars O := by
    intro v
    unfold HtenW tensorLat
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    refine prod_mem_of_span (R := Kf) (fun s => (blockEmb Kf s).toLinearMap) (fun s => Set.range (bV P v s)) (Tv v)
      (fun f hf => ?_) F (fun s => ?_)
    · choose I hI using hf
      exact Submodule.subset_span ⟨I, by simp only [AlgHom.toLinearMap_apply, hI]⟩
    · rw [(bV_spec P v s).2.1]
      exact Dl0_le _ _ _ (hL v s) (hF s)
  unfold Places.HtupW Places.tenV
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  refine prod_mem_of_span (R := Kf) (fun v => (P.vEmb v).toLinearMap)
    (fun v => {X | ∃ I : ∀ s, IdxV P v s, X = ∏ s, blockEmb Kf s (bV P v s (I s))}) _ (fun f hf => ?_) F
    (fun v => hv v (hF v))
  choose I hI using hf
  exact Submodule.subset_span ⟨fun v s => I v s, by simp only [AlgHom.toLinearMap_apply, hI]; rfl⟩

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model

section Rename₂

variable {R σ τ M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]

theorem isWH_rename (g : σ → τ) (w1 : σ → M) (w2 : τ → N) (L : M →+ N) (hL : ∀ x, w2 (g x) = L (w1 x))
    (f : MvPolynomial σ R) (μ : M) (hf : IsWeightedHomogeneous w1 f μ) :
    IsWeightedHomogeneous w2 (rename g f) (L μ) := by
  classical
  rw [f.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro d hd
  rw [rename_monomial]
  apply isWeightedHomogeneous_monomial
  rw [← hf (mem_support_iff.1 hd), Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (by simp) (by intros; rw [add_smul])]
  simp only [Finsupp.sum, map_sum, map_nsmul, hL]

theorem isWH_prod {ι : Type*} (s : Finset ι) (w : σ → M) (φ : ι → MvPolynomial σ R) (n : ι → M)
    (h : ∀ i ∈ s, IsWeightedHomogeneous w (φ i) (n i)) :
    IsWeightedHomogeneous w (∏ i ∈ s, φ i) (∑ i ∈ s, n i) := IsWeightedHomogeneous.prod s φ n h

end Rename₂

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf)

def om (x : Σ v : Fin P.nV, Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) : Fin P.nV × Fin (P.m + 1) → ℕ :=
  fun y => if y = (x.1, x.2.2.1) then 1 else 0

def atV (v : Fin P.nV) : (Fin (P.m + 1) → ℕ) →+ (Fin P.nV × Fin (P.m + 1) → ℕ) where
  toFun μ := fun y => if y.1 = v then μ y.2 else 0
  map_zero' := by funext y; simp
  map_add' a b := by funext y; by_cases h : y.1 = v <;> simp [h]

theorem emb_isWH (v : Fin P.nV) (s : Fin (P.n' v)) (f : MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf)
    (μ : Fin (P.m + 1) → ℕ) (hf : IsWeightedHomogeneous (rowW (P.m + 1) (P.m + 1)) f μ) :
    IsWeightedHomogeneous (om P) (P.vEmb v (blockEmb Kf s f)) (atV P v μ) := by
  simp only [blockEmb, Places.vEmb]
  rw [rename_rename]
  refine isWH_rename _ (rowW (P.m + 1) (P.m + 1)) (om P) (atV P v) ?_ f μ hf
  intro x
  funext y
  obtain ⟨y1, y2⟩ := y
  simp only [om, atV, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply, rowW, Pi.single_apply,
    Prod.mk.injEq]
  by_cases h1 : y1 = v
  · subst h1
    simp
  · simp [h1]

def wtOf (μ : ∀ v, Fin (P.n' v) → Fin (P.m + 1) → ℕ) : Fin P.nV × Fin (P.m + 1) → ℕ :=
  ∑ v, ∑ s, atV P v (μ v s)

theorem prodF_isWH (F : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf)
    (μ : ∀ v, Fin (P.n' v) → Fin (P.m + 1) → ℕ)
    (h : ∀ v s, IsWeightedHomogeneous (rowW (P.m + 1) (P.m + 1)) (F v s) (μ v s)) :
    IsWeightedHomogeneous (om P) (prodF P F) (wtOf P μ) := by
  simp only [prodF, wtOf]
  apply isWH_prod
  intro v _
  rw [map_prod]
  apply isWH_prod
  intro s _
  exact emb_isWH P v s (F v s) (μ v s) (h v s)

theorem wtOf_apply (μ : ∀ v, Fin (P.n' v) → Fin (P.m + 1) → ℕ) (v : Fin P.nV) (a : Fin (P.m + 1)) :
    wtOf P μ (v, a) = ∑ s, μ v s a := by
  simp only [wtOf, Finset.sum_apply, atV, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Finset.sum_eq_single v]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem eq_of_dom {S : Type*} [Fintype S] {k : ℕ} (μ ν : S → Fin k → ℕ)
    (hdom : ∀ s (c : ℕ), (∑ a : Fin k with a.val < c, μ s a) ≤ ∑ a : Fin k with a.val < c, ν s a)
    (hsum : ∀ a, ∑ s, μ s a = ∑ s, ν s a) : μ = ν := by
  have hpart : ∀ s c, (∑ a : Fin k with a.val < c, μ s a) = ∑ a : Fin k with a.val < c, ν s a := by
    intro s c
    have htot : ∑ s, (∑ a : Fin k with a.val < c, μ s a) = ∑ s, ∑ a : Fin k with a.val < c, ν s a := by
      rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => hsum a
    exact (Finset.sum_eq_sum_iff_of_le (fun s _ => hdom s c)).1 htot s (Finset.mem_univ s)
  funext s a
  have hs : (Finset.univ.filter fun b : Fin k => b.val < a.val + 1) =
      insert a (Finset.univ.filter fun b : Fin k => b.val < a.val) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hsplit : ∀ f : Fin k → ℕ,
      (∑ b : Fin k with b.val < a.val + 1, f b) = (∑ b : Fin k with b.val < a.val, f b) + f a := by
    intro f
    rw [hs, Finset.sum_insert (by simp), add_comm]
  have h1 := hpart s (a.val + 1)
  rw [hsplit (μ s), hsplit (ν s), hpart s a.val] at h1
  exact Nat.add_left_cancel h1

instance : Infinite Kf := Infinite.of_injective (Nat.cast : ℕ → Kf) Nat.cast_injective


theorem bV_dom (v : Fin P.nV) (s : Fin (P.n' v)) (i : IdxV P v s) (c : ℕ) :
    (∑ a : Fin (P.m + 1) with a.val < c, rowWt i.1 a) ≤ ∑ a : Fin (P.m + 1) with a.val < c, nuV P v s a := by
  obtain ⟨_, _, hb⟩ := Formalism.MainNotions.G.LatticeSystems.lb_basis Kf (P.m + 1) (P.m + 1) (nuV P v s)
  exact hb i c

theorem bV_top (v : Fin P.nV) (s : Fin (P.n' v)) (i : IdxV P v s) (h : rowWt i.1 = nuV P v s) :
    ∃ c : Kf, bV P v s i = c • hw Kf le_rfl (nuV P v s) := by
  have hanti : Antitone (nuV P v s) := by
    unfold nuV
    exact Formalism.MainNotions.G.LatticeSystems.kp_nuOf_antitone _ (Formalism.MainNotions.G.LatticeSystems.kp_lamAt_antitone _ (P.dom v) s)
  unfold bV
  generalize_proofs hh
  obtain ⟨⟨_, hspan, hhom⟩, _⟩ := hh.choose_spec
  have hmem : hh.choose i ∈ dualWeyl Kf (P.m + 1) (P.m + 1) (nuV P v s) := by
    rw [← hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hwt : IsWeightedHomogeneous (rowW (P.m + 1) (P.m + 1)) (hh.choose i)
      (rowNu (r := P.m + 1) (nuV P v s)) := by
    have e : rowNu (r := P.m + 1) (nuV P v s) = nuV P v s := by
      funext a
      simp [rowNu, a.isLt]
    have h2 : IsWeightedHomogeneous (rowW (P.m + 1) (P.m + 1)) (hh.choose i) (rowWt i.1) := hhom i
    rw [h] at h2
    rw [e]
    exact h2
  exact ⟨_, Formalism.L2.G.Model.sw_line Kf le_rfl (nuV P v s) hanti _ hmem hwt⟩

theorem prodF_smul (c : ∀ v, Fin (P.n' v) → Kf) (F : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf) :
    prodF P (fun v s => c v s • F v s) = (∏ v, ∏ s, c v s) • prodF P F := by
  simp only [prodF, smul_eq_C_mul, map_mul, Finset.prod_mul_distrib, map_prod]
  simp [Places.vEmb, blockEmb, rename_C, ← map_prod]

abbrev LamTot : Fin P.nV × Fin (P.m + 1) → ℕ := wtOf P (nuV P)

theorem mem_line (e : P.Xsp) (he : e ∈ Submodule.span Kf (Set.range (BI P)))
    (hwt : IsWeightedHomogeneous (om P) e (LamTot P)) : ∃ c : Kf, e = c • EV P := by
  classical
  have hBI : ∀ I, BI P I = prodF P (fun v s => bV P v s (I v s)) := fun I => rfl
  have hEV : EV P = prodF P (fun v s => hw Kf le_rfl (nuV P v s)) := rfl
  have hwtI : ∀ I, IsWeightedHomogeneous (om P) (BI P I) (wtOf P (fun v s => rowWt (I v s).1)) := by
    intro I
    rw [hBI]
    apply prodF_isWH
    intro v s
    show IsWeightedHomogeneous _ (bV P v s (I v s)) (rowWt (I v s).1)
    unfold bV
    generalize_proofs hh
    exact hh.choose_spec.1.2.2 (I v s)
  have htop : ∀ I, wtOf P (fun v s => rowWt (I v s).1) = LamTot P →
      BI P I ∈ Submodule.span Kf {EV P} := by
    intro I hI
    have hall : ∀ v s, rowWt (I v s).1 = nuV P v s := by
      intro v
      have hv := eq_of_dom (fun s => rowWt (I v s).1) (fun s => nuV P v s)
        (fun s c => bV_dom P v s (I v s) c) (by
          intro a
          have h1 := congrFun hI (v, a)
          simp only [LamTot, wtOf_apply] at h1
          exact h1)
      exact fun s => congrFun hv s
    have hc : ∀ v s, ∃ c : Kf, bV P v s (I v s) = c • hw Kf le_rfl (nuV P v s) :=
      fun v s => bV_top P v s (I v s) (hall v s)
    choose c hc using hc
    have hF : (fun v s => bV P v s (I v s)) = (fun v s => c v s • hw Kf le_rfl (nuV P v s)) := by
      funext v s
      exact hc v s
    rw [hBI, hF, prodF_smul, ← hEV]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 he
  have hcomp : weightedHomogeneousComponent (om P) (LamTot P) e = e := by
    rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 hwt), if_pos rfl]
  have hmem : e ∈ Submodule.span Kf {EV P} := by
    rw [← hcomp, ← hf, Finsupp.sum, map_sum]
    refine Submodule.sum_mem _ fun I _ => ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    by_cases hI : wtOf P (fun v s => rowWt (I v s).1) = LamTot P
    · have h3 := hwtI I
      rw [hI] at h3
      rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 h3), if_pos rfl]
      exact htop I hI
    · rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 (hwtI I)), if_neg (Ne.symm hI)]
      exact Submodule.zero_mem _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  exact ⟨c, hc.symm⟩

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G

section Scale

variable {σ K : Type*} [Field K]

theorem coeff_aeval_scale (c : σ → K) (f : MvPolynomial σ K) (m : σ →₀ ℕ) :
    coeff m (aeval (fun x => C (c x) * X x) f) = (m.prod fun x n => c x ^ n) * coeff m f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial d a =>
    rw [aeval_monomial, coeff_monomial]
    have h1 : (d.prod fun i k => (C (c i) * X i : MvPolynomial σ K) ^ k) = C (d.prod fun x n => c x ^ n) * monomial d 1 := by
      rw [monomial_eq, C_1, one_mul]
      simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
    rw [h1, algebraMap_eq, ← mul_assoc, ← map_mul, coeff_C_mul, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp
  | add f g hf hg => rw [map_add, coeff_add, coeff_add, hf, hg, mul_add]

end Scale

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf)

def Gtor (v0 : Fin P.nV) (a0 : Fin (P.m + 1)) : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf :=
  fun v _ => Matrix.diagonal fun a => if v = v0 ∧ a = a0 then (2 : Kf)⁻¹ else 1

theorem subst_Gtor (v0 : Fin P.nV) (a0 : Fin (P.m + 1)) :
    P.subst (Gtor P v0 a0) = aeval fun x => C (if x.1 = v0 ∧ x.2.2.1 = a0 then (2 : Kf)⁻¹ else 1) * X x := by
  classical
  refine MvPolynomial.algHom_ext fun x => ?_
  rw [Places.subst, aeval_X, aeval_X, Finset.sum_eq_single x.2.2.1]
  · simp [Gtor, Matrix.diagonal_apply_eq]
  · intro b _ hb
    rw [Gtor, Matrix.diagonal_apply_ne _ (Ne.symm hb), C_0, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem prod_tor (v0 : Fin P.nV) (a0 : Fin (P.m + 1))
    (m : (Σ v : Fin P.nV, Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) →₀ ℕ) :
    (m.prod fun x n => (if x.1 = v0 ∧ x.2.2.1 = a0 then (2 : Kf)⁻¹ else 1) ^ n) =
      (2 : Kf)⁻¹ ^ (Finsupp.weight (om P) m (v0, a0)) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finsupp.prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun x _ => ?_
  simp only [Pi.smul_apply, om, smul_eq_mul]
  by_cases h : x.1 = v0 ∧ x.2.2.1 = a0
  · have : (v0, a0) = (x.1, x.2.2.1) := Prod.ext h.1.symm h.2.symm
    rw [if_pos h, if_pos this, mul_one]
  · have : (v0, a0) ≠ (x.1, x.2.2.1) := fun e => h ⟨(congrArg Prod.fst e).symm, (congrArg Prod.snd e).symm⟩
    rw [if_neg h, if_neg this, one_pow, mul_zero, pow_zero]

theorem two_inv_pow_inj {a b : ℕ} (h : (2 : Kf)⁻¹ ^ a = (2 : Kf)⁻¹ ^ b) : a = b := by
  rw [inv_pow, inv_pow, inv_inj] at h
  have h2 : ((2 ^ a : ℕ) : Kf) = ((2 ^ b : ℕ) : Kf) := by push_cast; exact h
  exact Nat.pow_right_injective le_rfl (Nat.cast_injective h2)

theorem isWH_of_eigen (e E : P.Xsp) (hE0 : E ≠ 0) (hE : IsWeightedHomogeneous (om P) E (LamTot P))
    (t : Fin P.nV → Fin (P.m + 1) → Kf)
    (he : ∀ v0 a0, P.subst (Gtor P v0 a0) e = t v0 a0 • e) (hEt : ∀ v0 a0, P.subst (Gtor P v0 a0) E = t v0 a0 • E) :
    IsWeightedHomogeneous (om P) e (LamTot P) := by
  obtain ⟨mE, hmE⟩ := ne_zero_iff.mp hE0
  intro m hm
  funext y
  obtain ⟨v0, a0⟩ := y
  have h1 := congrArg (coeff m) (he v0 a0)
  have h2 := congrArg (coeff mE) (hEt v0 a0)
  rw [subst_Gtor, coeff_aeval_scale, prod_tor, coeff_smul, smul_eq_mul] at h1 h2
  have h3 : (2 : Kf)⁻¹ ^ (Finsupp.weight (om P) m (v0, a0)) = t v0 a0 := mul_right_cancel₀ hm h1
  have h4 : (2 : Kf)⁻¹ ^ (Finsupp.weight (om P) mE (v0, a0)) = t v0 a0 := mul_right_cancel₀ hmE h2
  rw [two_inv_pow_inj (h3.trans h4.symm), hE hmE]

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.MainNotions.G

variable {W Q : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q] [Algebra W Q] [IsFractionRing W Q]
  (ϖ : W) (hϖ : Irreducible ϖ)

local notation "π" => algebraMap W Q ϖ

include hϖ

theorem pi_ne : π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective W Q)).mpr hϖ.ne_zero

theorem exists_den (q : Q) : ∃ N : ℕ, ∀ M, N ≤ M → π ^ M * q ∈ (algebraMap W Q).range := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) q
  obtain ⟨N, hN⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero hb) hϖ
  obtain ⟨u, hu⟩ := hN
  refine ⟨N, fun M hM => ⟨ϖ ^ (M - N) * a * u, ?_⟩⟩
  have hb0 : algebraMap W Q b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W Q)).mpr (nonZeroDivisors.ne_zero hb)
  have h1 : algebraMap W Q b * algebraMap W Q u = π ^ N := by rw [← map_mul, hu, map_pow]
  rw [map_mul, map_mul, map_pow]
  have h2 : π ^ M = π ^ (M - N) * π ^ N := by rw [← pow_add, Nat.sub_add_cancel hM]
  rw [h2, ← h1]
  field_simp

theorem exists_den_fin {ι : Type} [Fintype ι] (q : ι → Q) : ∃ N : ℕ, ∀ i, π ^ N * q i ∈ (algebraMap W Q).range := by
  choose N hN using fun i => exists_den (Q := Q) ϖ hϖ (q i)
  exact ⟨∑ i, N i, fun i => hN i _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))⟩

theorem exists_gen_pow (I : Submodule W Q) (h0 : ∃ x ∈ I, x ≠ 0) (N : ℕ)
    (hN : ∀ x ∈ I, π ^ N * x ∈ (algebraMap W Q).range) :
    ∃ n : ℤ, π ^ n ∈ I ∧ ∀ x ∈ I, ∃ a : W, x = algebraMap W Q a * π ^ n := by
  have hp := pi_ne (Q := Q) ϖ hϖ
  let J : Ideal W :=
    { carrier := {a | ∃ x ∈ I, algebraMap W Q a = π ^ N * x}
      add_mem' := by
        rintro a b ⟨x, hx, h1⟩ ⟨y, hy, h2⟩
        exact ⟨x + y, I.add_mem hx hy, by rw [map_add, h1, h2, mul_add]⟩
      zero_mem' := ⟨0, I.zero_mem, by simp⟩
      smul_mem' := by
        rintro c a ⟨x, hx, h1⟩
        exact ⟨c • x, I.smul_mem c hx, by rw [smul_eq_mul, map_mul, h1, Algebra.smul_def]; ring⟩ }
  have hJ : J ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := h0
    obtain ⟨a, ha⟩ := hN x hx
    intro hb
    have : a ∈ J := ⟨x, hx, ha⟩
    rw [hb, Ideal.mem_bot] at this
    rw [this, map_zero] at ha
    exact (mul_ne_zero (pow_ne_zero _ hp) hx0) ha.symm
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hJ hϖ
  refine ⟨(m : ℤ) - N, ?_, fun x hx => ?_⟩
  · have : ϖ ^ m ∈ J := by rw [hm]; exact Ideal.mem_span_singleton_self _
    obtain ⟨x, hx, h1⟩ := this
    have : π ^ ((m : ℤ) - N) = x := by
      rw [zpow_sub₀ hp, zpow_natCast, zpow_natCast, ← map_pow, h1]
      field_simp
    rw [this]; exact hx
  · obtain ⟨a, ha⟩ := hN x hx
    have : a ∈ J := ⟨x, hx, ha⟩
    rw [hm, Ideal.mem_span_singleton] at this
    obtain ⟨b, rfl⟩ := this
    refine ⟨b, ?_⟩
    rw [zpow_sub₀ hp, zpow_natCast, zpow_natCast]
    rw [map_mul, map_pow] at ha
    field_simp
    rw [mul_comm x, ← ha]; ring

variable {k : ℕ}

def tailL (L : Submodule W (Fin k → Q)) (c : ℕ) : Submodule W (Fin k → Q) where
  carrier := {y | y ∈ L ∧ ∀ i : Fin k, i.val < c → y i = 0}
  add_mem' := by
    rintro a b ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨L.add_mem h1 h3, fun i hi => by rw [Pi.add_apply, h2 i hi, h4 i hi, add_zero]⟩
  zero_mem' := ⟨L.zero_mem, fun _ _ => rfl⟩
  smul_mem' := by
    rintro r a ⟨h1, h2⟩
    exact ⟨L.smul_mem r h1, fun i hi => by rw [Pi.smul_apply, h2 i hi, smul_zero]⟩

theorem hermite (L : Submodule W (Fin k → Q)) (hL : IsLattice W L) :
    ∃ (A : Matrix (Fin k) (Fin k) Q) (n : Fin k → ℤ), (∀ i j, i < j → A i j = 0) ∧ (∀ a, A a a = π ^ n a) ∧
      L = colSpan W A := by
  classical
  have hp := pi_ne (Q := Q) ϖ hϖ
  obtain ⟨g, hg, rfl⟩ := hL

  obtain ⟨N, hN⟩ := exists_den_fin (Q := Q) ϖ hϖ (fun x : Fin k × Fin k => g x.1 x.2)
  have hbd : ∀ y ∈ colSpan W g, ∀ i, π ^ N * y i ∈ (algebraMap W Q).range := by
    intro y hy i
    unfold colSpan at hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨c, rfl⟩ := hy; exact hN (i, c)
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ h1 h2 =>
      rw [Pi.add_apply, mul_add]; exact (algebraMap W Q).range.add_mem h1 h2
    | smul r y _ h1 =>
      rw [Pi.smul_apply, Algebra.smul_def, mul_left_comm]
      exact (algebraMap W Q).range.mul_mem ⟨r, rfl⟩ h1

  obtain ⟨N', hN'⟩ := exists_den_fin (Q := Q) ϖ hϖ (fun x : Fin k × Fin k => g⁻¹ x.1 x.2)
  have hunit : ∀ c : Fin k, (π ^ N') • (Pi.single c (1 : Q) : Fin k → Q) ∈ colSpan W g := by
    intro c
    choose a ha using fun j : Fin k => hN' (j, c)
    have : (π ^ N') • (Pi.single c (1 : Q) : Fin k → Q) = ∑ j, a j • (fun i => g i j) := by
      funext i
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, Algebra.smul_def, ha, smul_eq_mul]
      have h1 : (g * g⁻¹) i c = (1 : Matrix (Fin k) (Fin k) Q) i c := by rw [Matrix.mul_nonsing_inv g hg]
      rw [Matrix.mul_apply] at h1
      have h2 : ∑ j, π ^ N' * g⁻¹ j c * g i j = π ^ N' * ∑ j, g i j * g⁻¹ j c := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [h2, h1, Matrix.one_apply, Pi.single_apply]
      by_cases hic : i = c <;> simp [hic]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

  have hgen : ∀ c : Fin k, ∃ n : ℤ, (∃ x ∈ tailL (colSpan W g) c.val, x c = π ^ n) ∧
      ∀ y ∈ tailL (colSpan W g) c.val, ∃ a : W, y c = algebraMap W Q a * π ^ n := by
    intro c
    obtain ⟨n, h1, h2⟩ := exists_gen_pow (Q := Q) ϖ hϖ
      ((tailL (colSpan W g) c.val).map (LinearMap.proj (R := W) (φ := fun _ : Fin k => Q) c))
      ⟨π ^ N', ⟨_, ⟨hunit c, fun i hi => by
        rw [Pi.smul_apply, Pi.single_eq_of_ne (Fin.ne_of_lt hi), smul_zero]⟩, by simp⟩, pow_ne_zero _ hp⟩ N
      (by rintro _ ⟨y, hy, rfl⟩; exact hbd y hy.1 c)
    obtain ⟨x, hx, hxc⟩ := h1
    exact ⟨n, ⟨x, hx, hxc⟩, fun y hy => h2 _ ⟨y, hy, rfl⟩⟩
  choose n hx hy using hgen
  choose x hxm hxc using hx
  refine ⟨fun i c => x c i, n, fun i j hij => (hxm j).2 i hij, fun a => hxc a, ?_⟩
  apply le_antisymm
  · have key : ∀ d : ℕ, ∀ y ∈ colSpan W g, (∀ i : Fin k, i.val + d < k → y i = 0) →
        y ∈ colSpan W (fun i c => x c i) := by
      intro d
      induction d with
      | zero =>
        intro y _ h0
        have : y = 0 := funext fun i => h0 i (by simpa using i.2)
        rw [this]; exact Submodule.zero_mem _
      | succ d ih =>
        intro y hyL h0
        by_cases hd : d < k
        · let c : Fin k := ⟨k - (d + 1), by omega⟩
          have hyt : y ∈ tailL (colSpan W g) c.val := ⟨hyL, fun i hi => h0 i (by
            have : i.val < k - (d + 1) := hi
            omega)⟩
          obtain ⟨a, ha⟩ := hy c y hyt
          have h2 : y - a • x c ∈ colSpan W (fun i c => x c i) := by
            refine ih _ (Submodule.sub_mem _ hyL (Submodule.smul_mem _ _ (hxm c).1)) fun i hi => ?_
            rw [Pi.sub_apply, Pi.smul_apply, Algebra.smul_def]
            by_cases hic : i.val < c.val
            · rw [hyt.2 i hic, (hxm c).2 i hic, mul_zero, sub_zero]
            · have : i = c := Fin.ext (by
                have h3 : c.val = k - (d + 1) := rfl
                omega)
              rw [this, ha, hxc c, sub_self]
          have h3 : y = (y - a • x c) + a • x c := by abel
          rw [h3]
          exact Submodule.add_mem _ h2 (Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩))
        · exact ih y hyL fun i hi => absurd hi (by omega)
    exact fun y hyL => key k y hyL fun i hi => absurd hi (by omega)
  · unfold colSpan
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact (hxm c).1

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf)

def L0 : ∀ v, Submodule (P.W v) (Fin (P.m + 1) → P.Qq v) :=
  fun v => colSpan (P.W v) (1 : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v))

theorem mem_colSpan_one {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (x : Fin k → K) :
    x ∈ colSpan R (1 : Matrix (Fin k) (Fin k) K) ↔ ∀ a, x a ∈ (algebraMap R K).range :=
  Formalism.L2.G.Cmp.mem_stdL R x

theorem sigma_pow_int (v : Fin P.nV) (n : ℕ) (x : P.W v) :
    ∃ y : P.W v, ((P.σ v) ^ n) (algebraMap (P.W v) (P.Qq v) x) = algebraMap (P.W v) (P.Qq v) y := by
  induction n generalizing x with
  | zero => exact ⟨x, rfl⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih x
    obtain ⟨z, hz⟩ := (P.setting v).frob y
    refine ⟨y ^ p + (p : P.W v) * z, ?_⟩
    rw [pow_succ']
    show (P.σ v) (((P.σ v) ^ n) (algebraMap (P.W v) (P.Qq v) x)) = _
    rw [hy, hz]

theorem extension_standardLattice (v : Fin P.nV) (s : ℕ) :
    extO O (P.ι v) (P.σ v) s (L0 P v) = colSpan O (1 : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf) := by
  apply le_antisymm
  · unfold extO
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_colSpan_one]
    intro a
    obtain ⟨x, hx⟩ := (mem_colSpan_one y).mp hy a
    obtain ⟨z, hz⟩ := sigma_pow_int P v s x
    refine ⟨(P.j v) z, ?_⟩
    rw [twistVec, ← hx, hz, (P.setting v).ι_comp]
  · unfold colSpan
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe]
    have h2 : twistVec (P.ι v) (P.σ v) s (fun i => (1 : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) i c) ∈
        extO O (P.ι v) (P.σ v) s (L0 P v) :=
      Submodule.subset_span ⟨_, Submodule.subset_span ⟨c, rfl⟩, rfl⟩
    convert h2 using 1
    funext i
    simp only [twistVec, Matrix.one_apply]
    split_ifs <;> simp

def intP : Subring P.Xsp := (MvPolynomial.map (algebraMap O Kf)).range

theorem intP_smul (o : O) {f : P.Xsp} (hf : f ∈ intP P) : o • f ∈ intP P := by
  obtain ⟨g, rfl⟩ := hf
  exact ⟨o • g, by rw [map_smul', algebraMap_smul]⟩

theorem Dl0_int (v : Fin P.nV) (s : Fin (P.n' v)) (f : MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf)
    (hf : f ∈ Dl0 O P.m (lamAt (P.lam0 v) s) (extO O (P.ι v) (P.σ v) s.val (L0 P v))) :
    ∃ g : MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) O, MvPolynomial.map (algebraMap O Kf) g = f := by
  unfold Dl0 at hf
  rw [if_pos (lamAt_antitone' _ (P.dom v) s)] at hf
  simp only [Submodule.mem_iInf] at hf
  have h1 := hf 1 ⟨by simp, extension_standardLattice P v s.val⟩
  obtain ⟨x, hx, rfl⟩ := h1
  obtain ⟨w0, -, hw0⟩ := hx
  refine ⟨w0, ?_⟩
  simp only [Matrix.det_one, one_zpow, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, one_smul]
  have : rowAct Kf (1 : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf) x = x := by rw [rowAct_one']; rfl
  rw [← this]
  exact hw0

theorem htenW_int (v : Fin P.nV) (y : MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) Kf)
    (hy : y ∈ HtenW O (P.lam0 v) fun s => extO O (P.ι v) (P.σ v) s.val (L0 P v)) : P.vEmb v y ∈ intP P := by
  unfold HtenW tensorLat at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨G, hG, rfl⟩ := hy
    rw [map_prod]
    refine Subring.prod_mem _ fun s _ => ?_
    obtain ⟨g, hg⟩ := Dl0_int P v s (G s) (hG s)
    refine ⟨rename (fun y => (⟨v, (s, y)⟩ : Σ v : Fin P.nV, Fin (P.n' v) × _)) g, ?_⟩
    rw [map_rename, hg]
    unfold Places.vEmb blockEmb
    rw [rename_rename]; rfl
  | zero => rw [map_zero]; exact Subring.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Subring.add_mem _ ha hb
  | smul o a _ ha =>
    rw [← algebraMap_smul Kf o a, map_smul, algebraMap_smul]
    exact intP_smul P o ha

theorem htupW_int (f : P.Xsp) (hf : f ∈ P.HtupW (L0 P)) : f ∈ intP P := by
  unfold Places.HtupW Places.tenV at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    exact Subring.prod_mem _ fun v _ => htenW_int P v (F v) (hF v)
  | zero => exact Subring.zero_mem _
  | add a b _ _ ha hb => exact Subring.add_mem _ ha hb
  | smul o a _ ha => exact intP_smul P o ha

def idPt : (Σ v : Fin P.nV, Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) → Kf :=
  fun x => if x.2.2.1 = x.2.2.2 then 1 else 0

theorem eval_int (f : P.Xsp) (hf : f ∈ intP P) : eval (idPt P) f ∈ (algebraMap O Kf).range := by
  obtain ⟨g, rfl⟩ := hf
  have key : (eval (idPt P)).comp (MvPolynomial.map (algebraMap O Kf)) =
      (algebraMap O Kf).comp (eval fun x : (Σ v : Fin P.nV, Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) =>
        if x.2.2.1 = x.2.2.2 then (1 : O) else 0) := by
    refine MvPolynomial.ringHom_ext (fun a => by simp) (fun x => ?_)
    simp only [RingHom.comp_apply, map_X, eval_X, idPt]
    split_ifs <;> simp
  exact ⟨_, (RingHom.congr_fun key g).symm⟩

theorem eval_EV : eval (idPt P) (EV P) = 1 := by
  unfold EV prodF
  rw [map_prod]
  refine Finset.prod_eq_one fun v _ => ?_
  unfold Places.vEmb
  rw [eval_rename, map_prod]
  refine Finset.prod_eq_one fun s _ => ?_
  unfold blockEmb
  rw [eval_rename]
  convert sw_eval_hw Kf le_rfl (nuV P v s) using 2
  congr 1
  funext y
  simp [idPt, Formalism.GradedWeylDivisibility.idPoint, Fin.ext_iff]

theorem EV_ne : EV P ≠ 0 := by
  intro h
  have := eval_EV P
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem hw_map (ν : Fin (P.m + 1) → ℕ) :
    MvPolynomial.map (algebraMap O Kf) (hw O le_rfl ν) = hw Kf le_rfl ν := by
  unfold hw lpMinor
  simp only [map_prod, map_pow, RingHom.map_det]
  refine Finset.prod_congr rfl fun s _ => ?_
  congr 2
  ext a b
  simp [RingHom.mapMatrix_apply, map_X]

theorem EV_mem : EV P ∈ P.HtupW (L0 P) := by
  unfold Places.HtupW Places.tenV EV prodF
  refine Submodule.subset_span ⟨fun v => ∏ s, blockEmb Kf s (hw Kf le_rfl (nuV P v s)), fun v => ?_, rfl⟩
  unfold HtenW tensorLat
  refine Submodule.subset_span ⟨fun s => hw Kf le_rfl (nuV P v s), fun s => ?_, rfl⟩
  show hw Kf le_rfl (nuV P v s) ∈ Dl0 O P.m (lamAt (P.lam0 v) s) (extO O (P.ι v) (P.σ v) s.val (L0 P v))
  unfold Dl0
  rw [if_pos (lamAt_antitone' _ (P.dom v) s)]
  simp only [Submodule.mem_iInf]
  rintro g ⟨hg, hgΛ⟩
  have hinj : Function.Injective (algebraMap O Kf) := @IsFractionRing.injective O _ Kf _ _ (P.setting v).frac_O
  refine dl_indep hinj P.m _ 1 g (by simp) ((extension_standardLattice P v s.val).symm.trans hgΛ) ?_
  refine ⟨hw Kf le_rfl (nuV P v s), ⟨hw O le_rfl (nuV P v s), Submodule.subset_span ⟨[], rfl⟩, ?_⟩, ?_⟩
  · show MvPolynomial.map (algebraMap O Kf) _ = rowAct Kf 1 _
    rw [rowAct_one']; exact hw_map P _
  · simp

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf)

theorem subst_prodF (G : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf)
    (F : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf) :
    P.subst G (prodF P F) = prodF P fun v s => rowAct Kf (G v s) (F v s) := by
  unfold prodF
  rw [map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_prod, map_prod, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  have key : (P.subst G).comp ((P.vEmb v).comp (blockEmb Kf s)) =
      ((P.vEmb v).comp (blockEmb Kf s)).comp (rowAct Kf (G v s)) := by
    refine MvPolynomial.algHom_ext fun y => ?_
    simp [Places.subst, rowAct, Places.vEmb, blockEmb, map_sum, aeval_X]
  exact congrArg (fun φ => φ (F v s)) key

def IsZPow (b x : Kf) : Prop := ∃ z : ℤ, x = b ^ z

theorem IsZPow.one (b : Kf) : IsZPow b 1 := ⟨0, by simp⟩
theorem IsZPow.mul {b x y : Kf} (hb : b ≠ 0) (hx : IsZPow b x) (hy : IsZPow b y) : IsZPow b (x * y) := by
  obtain ⟨z, rfl⟩ := hx; obtain ⟨z', rfl⟩ := hy; exact ⟨z + z', by rw [zpow_add₀ hb]⟩
theorem IsZPow.zpow {b x : Kf} (hx : IsZPow b x) (n : ℤ) : IsZPow b (x ^ n) := by
  obtain ⟨z, rfl⟩ := hx; exact ⟨z * n, by rw [zpow_mul]⟩
theorem IsZPow.pow {b x : Kf} (hx : IsZPow b x) (n : ℕ) : IsZPow b (x ^ n) := by
  have := hx.zpow n; rwa [zpow_natCast] at this
theorem IsZPow.prod {b : Kf} (hb : b ≠ 0) {ι : Type*} (s : Finset ι) (f : ι → Kf) (h : ∀ i ∈ s, IsZPow b (f i)) :
    IsZPow b (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsZPow.one b
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul hb (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
theorem IsZPow.inv {b x : Kf} (hx : IsZPow b x) : IsZPow b x⁻¹ := by
  obtain ⟨z, rfl⟩ := hx; exact ⟨-z, by rw [zpow_neg]⟩

def LowT {k : ℕ} {R : Type*} [Zero R] (A : Matrix (Fin k) (Fin k) R) : Prop := ∀ i j, i < j → A i j = 0

theorem gPos_lowT (v : Fin P.nV) (s : Fin (P.n' v)) (A : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v))
    (hA : LowT A) : LowT (P.gPos v s A) := fun i j hij => by
  show P.ι v ((P.σ v ^ s.val) (A i j)) = 0
  rw [hA i j hij, map_zero, map_zero]

theorem gPos_diag (v : Fin P.nV) (s : Fin (P.n' v)) (A : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) (a : Fin (P.m + 1)) :
    P.gPos v s A a a = P.ι v ((P.σ v ^ s.val) (A a a)) := rfl

theorem subst_lowT (b : Kf) (hb : b ≠ 0) (A : ∀ v, Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) (hA : ∀ v, LowT (A v))
    (hd : ∀ v s a, IsZPow b (P.gPos v s (A v) a a)) :
    ∃ c : Kf, IsZPow b c ∧ P.subst (fun v s => P.gPos v s (A v)) (EV P) = c • EV P := by
  unfold EV
  rw [subst_prodF]
  simp_rw [rowAct_hw Kf le_rfl _ _ (gPos_lowT P _ _ _ (hA _))]
  refine ⟨_, ?_, prodF_smul P _ _⟩
  refine IsZPow.prod hb _ _ fun v _ => IsZPow.prod hb _ _ fun s _ => ?_
  unfold hwScal
  exact IsZPow.prod hb _ _ fun t _ => (IsZPow.prod hb _ _ fun a _ => hd v s _).pow _

theorem det_lowT {k : ℕ} {R : Type*} [CommRing R] (A : Matrix (Fin k) (Fin k) R) (hA : LowT A) :
    A.det = ∏ i, A i i :=
  Matrix.det_of_lowerTriangular A fun i j hij => hA i j hij

theorem gPos_inv_det (v : Fin P.nV) (s : Fin (P.n' v)) (A : GL (Fin (P.m + 1)) (P.Qq v)) :
    (P.gPos v s ((A⁻¹ : GL (Fin (P.m + 1)) (P.Qq v)) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v))).det =
      (P.gPos v s (A : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v))).det⁻¹ := by
  have h1 : P.gPos v s ((A⁻¹ : GL _ _) : Matrix _ _ _) * P.gPos v s (A : Matrix _ _ _) = 1 := by
    rw [← jd_gPos_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, jd_gPos_one]
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_one] at h2
  exact eq_inv_of_mul_eq_one_left h2

theorem natAct_inv_lowT (b : Kf) (hb : b ≠ 0) (A : ∀ v, GL (Fin (P.m + 1)) (P.Qq v))
    (hA : ∀ v, LowT (A v : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)))
    (hd : ∀ v s a, IsZPow b (P.gPos v s (A v : Matrix _ _ _) a a)) :
    ∃ c : Kf, IsZPow b c ∧ P.natAct A⁻¹ (EV P) = c • EV P := by
  obtain ⟨c, hc, h1⟩ := subst_lowT P b hb (fun v => (A v : Matrix _ _ _)) hA hd
  refine ⟨(∏ v, ∏ s : Fin (P.n' v), (P.gPos v s ((A⁻¹ : ∀ v, GL (Fin (P.m + 1)) (P.Qq v)) v :
      Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v))).det ^ (-(lamAt (P.lam0 v) s (Fin.last P.m)))) * c,
    IsZPow.mul hb (IsZPow.prod hb _ _ fun v _ => IsZPow.prod hb _ _ fun s _ => ?_) hc, ?_⟩
  · rw [Pi.inv_apply, gPos_inv_det, det_lowT _ (gPos_lowT P v s _ (hA v))]
    exact ((IsZPow.prod hb _ _ fun a _ => hd v s a).inv).zpow _
  · unfold Places.natAct
    rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply]
    have : (fun v s => P.gPos v s (((A⁻¹ : ∀ v, GL _ _) v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v))) =
        fun v s => P.gPos v s (A v : Matrix _ _ _) := by
      funext v s; rw [Pi.inv_apply, inv_inv]
    rw [this, h1, smul_smul]

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf) (hp : (p : Kf) ≠ 0)

theorem natAct_inv_self (A : ∀ v, GL (Fin (P.m + 1)) (P.Qq v)) (x : P.Xsp) : P.natAct A⁻¹ (P.natAct A x) = x := by
  have := jd_natAct_mul P A⁻¹ A
  have h2 : (fun v => (A⁻¹) v * A v) = (fun _ => (1 : GL (Fin (P.m + 1)) _)) := by
    funext v; rw [Pi.inv_apply, inv_mul_cancel]
  rw [h2, jd_natAct_one] at this
  exact (LinearMap.congr_fun this x).symm


include hp in

def Γsub : Subgroup ((∀ v, GL (Fin (P.m + 1)) (P.Qq v)) × Oˣ) where
  carrier := {γ | ∃ z : ℤ, P.natAct γ.1 (EV P) = ((p : Kf) ^ z * algebraMap O Kf ((γ.2⁻¹ : Oˣ) : O)) • EV P}
  mul_mem' := by
    rintro ⟨A, u⟩ ⟨B, w⟩ ⟨z, hz⟩ ⟨z', hz'⟩
    refine ⟨z + z', ?_⟩
    show P.natAct (fun v => A v * B v) (EV P) = _
    rw [jd_natAct_mul, LinearMap.comp_apply]
    simp only at hz hz'
    rw [hz', LinearMap.map_smul, hz, smul_smul]
    congr 1
    simp only [Prod.snd_mul, mul_inv_rev, Units.val_mul, map_mul, zpow_add₀ hp]
    ring
  one_mem' := ⟨0, by
    show P.natAct (fun _ => 1) (EV P) = _
    rw [jd_natAct_one]; simp⟩
  inv_mem' := by
    rintro ⟨A, u⟩ ⟨z, hz⟩
    simp only at hz
    refine ⟨-z, ?_⟩
    have hu : algebraMap O Kf ((u⁻¹ : Oˣ) : O) * algebraMap O Kf (u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hc : (p : Kf) ^ z * algebraMap O Kf ((u⁻¹ : Oˣ) : O) ≠ 0 := by
      refine mul_ne_zero (zpow_ne_zero _ hp) fun h => ?_
      rw [h, zero_mul] at hu; exact zero_ne_one hu
    show P.natAct A⁻¹ (EV P) = _
    have h1 : EV P = P.natAct A (((p : Kf) ^ z * algebraMap O Kf ((u⁻¹ : Oˣ) : O))⁻¹ • EV P) := by
      rw [LinearMap.map_smul, hz, smul_smul, inv_mul_cancel₀ hc, one_smul]
    conv_lhs => rw [h1, natAct_inv_self]
    congr 1
    simp only [Prod.snd_inv, inv_inv, zpow_neg]
    rw [mul_inv, inv_eq_of_mul_eq_one_right hu]

include hp in

def levB : Level P where
  Γ := Γsub P hp
  act v := (Pi.evalMonoidHom (fun v => GL (Fin (P.m + 1)) (P.Qq v)) v).comp ((MonoidHom.fst _ _).comp (Γsub P hp).subtype)
  χ := (MonoidHom.snd _ _).comp (Γsub P hp).subtype

theorem levB_actX (γ : ↥(Γsub P hp)) : (levB P hp).actX γ = P.natAct γ.1.1 := rfl

theorem levB_chi (γ : ↥(Γsub P hp)) : ((levB P hp).χ γ : O) = (γ.1.2 : O) := rfl

theorem levB_EV (γ : ↥(Γsub P hp)) : ∃ z : ℤ, ((levB P hp).χ γ : O) • (levB P hp).actX γ (EV P) = (p : Kf) ^ z • EV P := by
  obtain ⟨z, hz⟩ := γ.2
  refine ⟨z, ?_⟩
  rw [levB_actX, hz, levB_chi, ← algebraMap_smul Kf, smul_smul]
  congr 1
  rw [mul_comm, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]

def gatU : GAtP p where
  O := O
  Kf := Kf
  P := P
  comp := Unit
  lev := fun _ => levB P hp
  e := 0

abbrev standardTuple : P.Tup := L0 P

theorem standardTuple_isLattice : P.IsLatTup (standardTuple P) := fun v => ⟨1, by simp, rfl⟩

theorem stab_EV (v0 : Fin P.nV) (γ : (levB P hp).Γ) (hγ : (levB P hp).smul γ (standardTuple P) = standardTuple P) :
    ((levB P hp).χ γ : O) • (levB P hp).actX γ (EV P) = EV P := by
  have hmem : ∀ g : (levB P hp).Γ, (levB P hp).smul g (standardTuple P) = standardTuple P →
      ∃ z : ℤ, ((levB P hp).χ g : O) • (levB P hp).actX g (EV P) = (p : Kf) ^ z • EV P ∧
        (p : Kf) ^ z ∈ (algebraMap O Kf).range := by
    intro g hg
    obtain ⟨z, hz⟩ := levB_EV P hp g
    refine ⟨z, hz, ?_⟩
    have h1 := Formalism.L2.G.Cmp.equivSys_HtupW (gatU P hp) () g (standardTuple P) (standardTuple_isLattice P) (EV P) (EV_mem P)
    have h1' : ((levB P hp).χ g : O) • (levB P hp).actX g (EV P) ∈ P.HtupW (standardTuple P) := by
      have : (gatU P hp).P.HtupW ((gatU P hp).lev () |>.smul g (standardTuple P)) = P.HtupW (standardTuple P) := by
        show P.HtupW ((levB P hp).smul g (standardTuple P)) = _
        rw [hg]
      rw [← this]; exact h1
    rw [hz] at h1'
    have h2 := eval_int P _ (htupW_int P _ h1')
    rwa [smul_eval, eval_EV, mul_one] at h2
  obtain ⟨z, hz, ha⟩ := hmem γ hγ
  have hγ' : (levB P hp).smul γ⁻¹ (standardTuple P) = L0 P := by
    conv_lhs => rw [← hγ, ← jd_smul_mul, inv_mul_cancel, jd_smul_one]
  obtain ⟨z', hz', hb⟩ := hmem γ⁻¹ hγ'
  have e1 : ((levB P hp).χ γ⁻¹ : O) • (levB P hp).actX γ⁻¹ (((levB P hp).χ γ : O) • (levB P hp).actX γ (EV P)) =
      EV P := by
    rw [LinearMap.map_smul_of_tower, smul_comm, ← LinearMap.comp_apply, ← jd_actX_mul, inv_mul_cancel, jd_actX_one,
      LinearMap.id_apply, smul_smul, ← Units.val_mul, ← map_mul]
    simp
  rw [hz, LinearMap.map_smul_of_tower, smul_comm, hz', smul_smul] at e1
  have e2 := congrArg (eval (idPt P)) e1
  rw [smul_eval, eval_EV, mul_one] at e2
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  have hpn : ¬ IsUnit (p : (gatU P hp).O) := ja_p_nonunit (gatU P hp) v0
  haveI := (P.setting v0).frac_O
  have hab : a * b = 1 := IsFractionRing.injective O Kf (by rw [map_mul, ha, hb, e2, map_one])
  have hzero : z = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨n, hn'⟩ : ∃ n : ℕ, -z = (n : ℤ) + 1 := ⟨(-z - 1).toNat, by omega⟩
      have h3 : (p : Kf) ^ z' = (p : Kf) ^ ((n : ℤ) + 1) := by
        rw [← hn', zpow_neg]; exact eq_inv_of_mul_eq_one_right e2
      rw [zpow_add_one₀ hp, zpow_natCast, ← pow_succ] at h3
      have hb' : b = (p : O) ^ (n + 1) := IsFractionRing.injective O Kf (by rw [hb, h3, map_pow, map_natCast])
      have hub : IsUnit b := IsUnit.of_mul_eq_one a (by rw [mul_comm]; exact hab)
      rw [hb'] at hub
      exact hpn ((isUnit_pow_iff (by omega)).mp hub)
    · obtain ⟨n, hn'⟩ : ∃ n : ℕ, z = (n : ℤ) + 1 := ⟨(z - 1).toNat, by omega⟩
      have h3 : (p : Kf) ^ z = (p : Kf) ^ (n + 1) := by rw [hn', zpow_add_one₀ hp, zpow_natCast, ← pow_succ]
      have ha' : a = (p : O) ^ (n + 1) := IsFractionRing.injective O Kf (by rw [ha, h3, map_pow, map_natCast])
      have hua : IsUnit a := IsUnit.of_mul_eq_one b hab
      rw [ha'] at hua
      exact hpn ((isUnit_pow_iff (by omega)).mp hua)
  rw [hz, hzero, zpow_zero, one_smul]

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf) (hp : (p : Kf) ≠ 0)

theorem isUnit_two_W (v : Fin P.nV) : IsUnit (2 : P.W v) := by
  have hirr := (P.setting v).p_unif
  by_contra h
  have hmax : (2 : P.W v) ∈ IsLocalRing.maximalIdeal (P.W v) := (IsLocalRing.mem_maximalIdeal _).mpr h
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hirr, Ideal.mem_span_singleton] at hmax
  obtain ⟨y, hy⟩ := hmax
  have hodd : Odd p := (P.setting v).prime.odd_of_ne_two (by have := (P.setting v).five_le; omega)
  obtain ⟨k, hk⟩ := hodd
  have h1 : (1 : P.W v) = (p : P.W v) * (1 - y * k) := by
    have h0 : ((p : ℕ) : P.W v) = ((2 * k + 1 : ℕ) : P.W v) := congrArg _ hk
    have : ((p : ℕ) : P.W v) = 2 * k + 1 := by rw [h0]; push_cast; ring
    calc (1 : P.W v) = (p : P.W v) - 2 * k := by rw [this]; ring
      _ = _ := by rw [hy]; ring
  exact hirr.not_isUnit (IsUnit.of_mul_eq_one _ h1.symm)

theorem alg_units_zpow (u : Oˣ) (z : ℤ) : algebraMap O Kf ((u ^ z : Oˣ) : O) = (algebraMap O Kf (u : O)) ^ z := by
  have h1 : algebraMap O Kf ((u ^ z : Oˣ) : O) = ((Units.map (algebraMap O Kf).toMonoidHom (u ^ z) : Kfˣ) : Kf) := rfl
  rw [h1, map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

def dT (v0 : Fin P.nV) (a0 : Fin (P.m + 1)) (v : Fin P.nV) : Fin (P.m + 1) → P.Qq v :=
  fun a => if v = v0 ∧ a = a0 then 2 else 1

theorem two_ne (v : Fin P.nV) : (2 : P.Qq v) ≠ 0 := by
  haveI := (P.setting v).frac_alt
  have := (isUnit_two_W P v).map (algebraMap (P.W v) (P.Qq v))
  rw [map_ofNat] at this
  exact this.ne_zero

theorem dT_ne (v0 a0 v) (a : Fin (P.m + 1)) : dT P v0 a0 v a ≠ 0 := by
  unfold dT; split_ifs
  · exact two_ne P v
  · exact one_ne_zero

def torM (v0 : Fin P.nV) (a0 : Fin (P.m + 1)) (v : Fin P.nV) : GL (Fin (P.m + 1)) (P.Qq v) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal (dT P v0 a0 v))
    (by rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun a _ => dT_ne P v0 a0 v a)

theorem torM_inv (v0 a0 v) : (((torM P v0 a0 v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v)) : Matrix _ _ _) =
    Matrix.diagonal fun a => (dT P v0 a0 v a)⁻¹ := by
  rw [Matrix.coe_units_inv]
  refine Matrix.inv_eq_left_inv ?_
  show Matrix.diagonal _ * Matrix.diagonal (dT P v0 a0 v) = 1
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext a; exact inv_mul_cancel₀ (dT_ne P v0 a0 v a)

theorem gPos_diagonal (v : Fin P.nV) (s : Fin (P.n' v)) (e : Fin (P.m + 1) → P.Qq v) :
    P.gPos v s (Matrix.diagonal e) = Matrix.diagonal fun a => P.ι v ((P.σ v ^ s.val) (e a)) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Places.gPos]
  · simp [Places.gPos, Matrix.diagonal_apply_ne _ h]

theorem natAct_tor (v0 a0) : ∃ c : Kf, IsZPow 2 c ∧ P.natAct (torM P v0 a0) = c • (P.subst (Gtor P v0 a0)).toLinearMap := by
  refine ⟨∏ v, ∏ s : Fin (P.n' v), (P.gPos v s (torM P v0 a0 v : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v))).det ^
      (-(lamAt (P.lam0 v) s (Fin.last P.m))), IsZPow.prod two_ne_zero _ _ fun v _ => IsZPow.prod two_ne_zero _ _ fun s _ => ?_, ?_⟩
  · refine IsZPow.zpow ?_ _
    show IsZPow 2 (P.gPos v s (Matrix.diagonal (dT P v0 a0 v))).det
    rw [gPos_diagonal, Matrix.det_diagonal]
    refine IsZPow.prod two_ne_zero _ _ fun a _ => ?_
    unfold dT; split_ifs
    · exact ⟨1, by rw [zpow_one, map_ofNat, map_ofNat]⟩
    · exact ⟨0, by rw [zpow_zero, map_one, map_one]⟩
  · unfold Places.natAct
    congr 2
    congr 1
    funext v s
    rw [torM_inv, gPos_diagonal]
    unfold Gtor dT
    congr 1; funext a
    split_ifs
    · rw [map_inv₀, map_inv₀, map_ofNat, map_ofNat]
    · rw [inv_one, map_one, map_one]

theorem EV_isWH : IsWeightedHomogeneous (om P) (EV P) (LamTot P) := by
  refine prodF_isWH P _ _ fun v s => ?_
  have h := hwRowWeight Kf (P.m + 1) (P.m + 1) le_rfl (nuV P v s) (nuV_anti P v s)
  have : rowNu (r := P.m + 1) (nuV P v s) = nuV P v s := by funext a; unfold rowNu; rw [dif_pos a.2]
  rwa [this] at h

theorem subst_Gtor_EV (v0 a0) :
    P.subst (Gtor P v0 a0) (EV P) = ((2 : Kf)⁻¹ ^ (LamTot P (v0, a0))) • EV P := by
  ext m
  rw [subst_Gtor, coeff_aeval_scale, prod_tor, coeff_smul, smul_eq_mul]
  by_cases hm : coeff m (EV P) = 0
  · rw [hm, mul_zero, mul_zero]
  · rw [EV_isWH P hm]

theorem tor_mem (v0 : Fin P.nV) (a0 : Fin (P.m + 1)) :
    ∃ u : Oˣ, (torM P v0 a0, u) ∈ Γsub P hp ∧
      P.natAct (torM P v0 a0) (EV P) = algebraMap O Kf ((u⁻¹ : Oˣ) : O) • EV P := by
  obtain ⟨c, ⟨N, rfl⟩, hc⟩ := natAct_tor P v0 a0
  have h2O : IsUnit (2 : O) := by
    have := (isUnit_two_W P v0).map (P.j v0); rwa [map_ofNat] at this
  obtain ⟨M, hM⟩ : ∃ M : ℤ, (2 : Kf) ^ N * (2 : Kf)⁻¹ ^ (LamTot P (v0, a0)) = (2 : Kf) ^ M :=
    ⟨N - LamTot P (v0, a0), by rw [zpow_sub₀ two_ne_zero, zpow_natCast, div_eq_mul_inv, inv_pow]⟩
  refine ⟨h2O.unit ^ (-M), ?_, ?_⟩ <;>
  · have : P.natAct (torM P v0 a0) (EV P) = algebraMap O Kf ((((h2O.unit ^ (-M))⁻¹ : Oˣ)) : O) • EV P := by
      rw [hc, LinearMap.smul_apply, AlgHom.toLinearMap_apply, subst_Gtor_EV, smul_smul, hM, zpow_neg, inv_inv,
        alg_units_zpow, IsUnit.unit_spec, map_ofNat]
    first
    | exact ⟨0, by rw [this, zpow_zero, one_mul]⟩
    | exact this

theorem tor_stab (v0 a0) (u : Oˣ) (hu : (torM P v0 a0, u) ∈ Γsub P hp) :
    (levB P hp).smul ⟨(torM P v0 a0, u), hu⟩ (standardTuple P) = standardTuple P := by
  funext v
  show Formalism.L2.G.Cmp.gMap (P.W v) (torM P v0 a0 v) (Formalism.L2.G.Cmp.stdL (P.W v)) = Formalism.L2.G.Cmp.stdL (P.W v)
  haveI := (P.setting v).frac_alt
  refine (Formalism.L2.G.Cmp.stabStd_iff (P.W v) _).mpr ⟨fun a b => ?_, fun a b => ?_⟩
  · show Matrix.diagonal (dT P v0 a0 v) a b ∈ _
    by_cases h : a = b
    · subst h; rw [Matrix.diagonal_apply_eq]; unfold dT; split_ifs
      · exact ⟨2, map_ofNat _ 2⟩
      · exact ⟨1, map_one _⟩
    · rw [Matrix.diagonal_apply_ne _ h]; exact Subring.zero_mem _
  · rw [torM_inv]
    by_cases h : a = b
    · subst h; rw [Matrix.diagonal_apply_eq]; unfold dT; split_ifs
      · refine ⟨((isUnit_two_W P v).unit⁻¹ : (P.W v)ˣ), ?_⟩
        have h1 := congrArg (algebraMap (P.W v) (P.Qq v)) ((isUnit_two_W P v).unit.inv_mul)
        rw [map_mul, IsUnit.unit_spec, map_ofNat, map_one] at h1
        exact eq_inv_of_mul_eq_one_left h1
      · exact ⟨1, by simp⟩
    · rw [Matrix.diagonal_apply_ne _ h]; exact Subring.zero_mem _

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf) (hp : (p : Kf) ≠ 0)

theorem exists_trans (L : P.Tup) (hL : P.IsLatTup L) : ∃ γ : ↥(Γsub P hp), (levB P hp).smul γ (standardTuple P) = L := by
  classical
  have key : ∀ v, ∃ A : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v), ∃ n : Fin (P.m + 1) → ℤ,
      LowT A ∧ (∀ a, A a a = (p : P.Qq v) ^ (n a)) ∧ L v = colSpan (P.W v) A := by
    intro v
    haveI := (P.setting v).frac_alt
    obtain ⟨A, n, h1, h2, h3⟩ := hermite (Q := P.Qq v) (p : P.W v) (P.setting v).p_unif (L v) (hL v)
    exact ⟨A, n, h1, fun a => by rw [h2 a, map_natCast], h3⟩
  choose A n hlow hdiag hLA using key
  have hp0 : ∀ v, (p : P.Qq v) ≠ 0 := fun v => by
    haveI := (P.setting v).frac_alt
    rw [← map_natCast (algebraMap (P.W v) (P.Qq v))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (P.setting v).p_unif.ne_zero
  have hdet : ∀ v, (A v).det ≠ 0 := by
    intro v; rw [det_lowT _ (hlow v)]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => by rw [hdiag]; exact zpow_ne_zero _ (hp0 v)
  let Ag : ∀ v, GL (Fin (P.m + 1)) (P.Qq v) := fun v => Matrix.GeneralLinearGroup.mkOfDetNeZero (A v) (hdet v)
  obtain ⟨c, ⟨z, rfl⟩, hc⟩ := natAct_inv_lowT P (p : Kf) hp Ag hlow (fun v s a => ⟨n v a, by
    rw [gPos_diag]
    show P.ι v ((P.σ v ^ s.val) (A v a a)) = _
    rw [hdiag, map_zpow₀, map_zpow₀, map_natCast, map_natCast]⟩)
  have hmem : (Ag⁻¹, (1 : Oˣ)) ∈ Γsub P hp := ⟨z, by rw [hc]; simp⟩
  have hmem' : (Ag, (1 : Oˣ)) ∈ Γsub P hp := by
    have := (Γsub P hp).inv_mem hmem
    simpa using this
  refine ⟨⟨(Ag, 1), hmem'⟩, ?_⟩
  funext v
  show (L0 P v).map ((Matrix.mulVecLin (A v)).restrictScalars (P.W v)) = L v
  rw [hLA v]
  unfold L0
  rw [Formalism.MainNotions.G.Inhab.map_colSpan', Matrix.mul_one]

def gOf (L : P.Tup) (hL : P.IsLatTup L) : (levB P hp).Γ := (exists_trans P hp L hL).choose

theorem gOf_spec (L : P.Tup) (hL : P.IsLatTup L) : (levB P hp).smul (gOf P hp L hL) (standardTuple P) = L :=
  (exists_trans P hp L hL).choose_spec

variable (v0 : Fin P.nV)

include v0 in
theorem wd (g g' : (levB P hp).Γ) (h : (levB P hp).smul g (standardTuple P) = (levB P hp).smul g' (standardTuple P)) :
    ((levB P hp).χ g : O) • (levB P hp).actX g (EV P) = ((levB P hp).χ g' : O) • (levB P hp).actX g' (EV P) := by
  have hk : (levB P hp).smul (g'⁻¹ * g) (standardTuple P) = standardTuple P := by
    rw [jd_smul_mul, h, ← jd_smul_mul, inv_mul_cancel, jd_smul_one]
  have hs := stab_EV P hp v0 (g'⁻¹ * g) hk
  have hg : g = g' * (g'⁻¹ * g) := by group
  conv_lhs => rw [hg, map_mul, Units.val_mul, jd_actX_mul, LinearMap.comp_apply, mul_smul,
    ← LinearMap.map_smul_of_tower, hs]

open Classical in

def valE (L : P.Tup) : P.Xsp :=
  if hL : P.IsLatTup L then ((levB P hp).χ (gOf P hp L hL) : O) • (levB P hp).actX (gOf P hp L hL) (EV P) else 0

include v0 in
theorem value_standardTuple : valE P hp (standardTuple P) = EV P := by
  classical
  unfold valE
  rw [dif_pos (standardTuple_isLattice P)]
  have := wd P hp v0 (gOf P hp (standardTuple P) (standardTuple_isLattice P)) 1 (by rw [gOf_spec, jd_smul_one])
  rw [this, map_one, Units.val_one, one_smul, jd_actX_one, LinearMap.id_apply]

include v0 in
theorem valE_smul (γ : (levB P hp).Γ) (L : P.Tup) :
    valE P hp ((levB P hp).smul γ L) = ((levB P hp).χ γ : O) • (levB P hp).actX γ (valE P hp L) := by
  classical
  unfold valE
  by_cases hL : P.IsLatTup L
  · have hL' : P.IsLatTup ((levB P hp).smul γ L) := (Formalism.MainNotions.G.Inhab.isLatTup_smul_iff P (levB P hp) γ L).mpr hL
    rw [dif_pos hL', dif_pos hL]
    rw [wd P hp v0 (gOf P hp _ hL') (γ * gOf P hp L hL) (by rw [gOf_spec, jd_smul_mul, gOf_spec])]
    rw [map_mul, Units.val_mul, jd_actX_mul, LinearMap.comp_apply, mul_smul, LinearMap.map_smul_of_tower]
  · have hL' : ¬ P.IsLatTup ((levB P hp).smul γ L) := fun h =>
      hL ((Formalism.MainNotions.G.Inhab.isLatTup_smul_iff P (levB P hp) γ L).mp h)
    rw [dif_neg hL', dif_neg hL, map_zero, smul_zero]

theorem valE_mem (L : P.Tup) (hL : P.IsLatTup L) : valE P hp L ∈ P.HtupW L := by
  classical
  unfold valE
  rw [dif_pos hL]
  have h1 := Formalism.L2.G.Cmp.equivSys_HtupW (gatU P hp) () (gOf P hp L hL) (standardTuple P) (standardTuple_isLattice P) (EV P) (EV_mem P)
  have h2 : (gatU P hp).P.HtupW (((gatU P hp).lev ()).smul (gOf P hp L hL) (standardTuple P)) = P.HtupW L := by
    show P.HtupW ((levB P hp).smul (gOf P hp L hL) (standardTuple P)) = _
    rw [gOf_spec]
  rw [h2] at h1
  exact h1

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf) (hp : (p : Kf) ≠ 0) (C : Type) [Fintype C] [DecidableEq C]

abbrev gatC : GAtP p where
  O := O
  Kf := Kf
  P := P
  comp := C
  lev := fun _ => levB P hp
  e := 0

def Fb (c : C) : (gatC P hp C).Fn := fun (c' : C) (L : P.Tup) => if c' = c then valE P hp L else 0

variable (v0 : Fin P.nV)

include v0 in
theorem Fb_mem (c : C) : Fb P hp C c ∈ (gatC P hp C).M := by
  classical
  intro c' _
  refine (Formalism.MainNotions.G.Inhab.mem_funMod (levB P hp) P.HtupW (Fb P hp C c c')).mpr ⟨fun L hL => ?_, fun L hL => ?_,
    fun γ L => ?_⟩
  · unfold Fb; split_ifs
    · exact valE_mem P hp L hL
    · exact Submodule.zero_mem _
  · unfold Fb; split_ifs
    · unfold valE; rw [dif_neg hL]
    · rfl
  · unfold Fb; split_ifs
    · exact valE_smul P hp v0 γ L
    · rw [map_zero, smul_zero]

include v0 in

theorem value_standardTuple_integral (F : (gatC P hp C).Fn) (hF : F ∈ (gatC P hp C).M) (c : C) :
    ∃ o : O, F c (standardTuple P) = algebraMap O Kf o • EV P := by
  have hF' := (Formalism.MainNotions.G.Inhab.mem_funMod (levB P hp) P.HtupW (F c)).mp (hF c (Set.mem_univ c))
  set e : P.Xsp := F c (standardTuple P) with he
  have hmem : e ∈ P.HtupW (standardTuple P) := hF'.1 _ (standardTuple_isLattice P)
  choose cc hcz hc using fun v a => natAct_tor P v a
  choose u hu hnat using fun v a => tor_mem P hp v a
  have hc0 : ∀ v a, cc v a ≠ 0 := fun v a => by
    obtain ⟨z, hz⟩ := hcz v a; rw [hz]; exact zpow_ne_zero _ two_ne_zero
  have hwt : IsWeightedHomogeneous (om P) e (LamTot P) := by
    refine isWH_of_eigen P e (EV P) (EV_ne P) (EV_isWH P)
      (fun v a => (cc v a)⁻¹ * algebraMap O Kf (((u v a)⁻¹ : Oˣ) : O)) (fun v a => ?_) (fun v a => ?_)
    · have h1 := hF'.2.2 ⟨(torM P v a, u v a), hu v a⟩ (standardTuple P)
      rw [tor_stab P hp v a _ (hu v a)] at h1
      have h2 : P.natAct (torM P v a) e = algebraMap O Kf (((u v a)⁻¹ : Oˣ) : O) • e := by
        have h3 : e = ((u v a : O)) • P.natAct (torM P v a) e := h1
        conv_rhs => rw [h3]
        rw [← algebraMap_smul Kf ((u v a : Oˣ) : O) (P.natAct (torM P v a) e), smul_smul, ← map_mul, Units.inv_mul,
          map_one, one_smul]
      rw [hc, LinearMap.smul_apply, AlgHom.toLinearMap_apply] at h2
      rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ (hc0 v a), one_smul]
    · have h2 := hnat v a
      rw [hc, LinearMap.smul_apply, AlgHom.toLinearMap_apply] at h2
      rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ (hc0 v a), one_smul]
  have hlat : ∀ v (s : Fin (P.n' v)), IsLattice O (extO O (P.ι v) (P.σ v) s.val (standardTuple P v)) := fun v s => by
    show IsLattice O (extO O (P.ι v) (P.σ v) s.val (L0 P v))
    rw [extension_standardLattice]; exact ⟨1, by simp, rfl⟩
  obtain ⟨a, ha⟩ := mem_line P e (htupW_le P (standardTuple P) hlat hmem) hwt
  have hint := eval_int P _ (htupW_int P _ hmem)
  rw [ha, smul_eval, eval_EV, mul_one] at hint
  obtain ⟨o, ho⟩ := hint
  exact ⟨o, by rw [ha, ho]⟩

include v0 in
theorem M_eq : Submodule.span (gatC P hp C).O (Set.range (Fb P hp C)) = (gatC P hp C).M := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact Fb_mem P hp C v0 c
  · intro F hF
    choose o ho using value_standardTuple_integral P hp C v0 F hF
    have hFeq : F = ∑ c, o c • Fb P hp C c := by
      funext c' L
      rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single c']
      · have hF' := (Formalism.MainNotions.G.Inhab.mem_funMod (levB P hp) P.HtupW (F c')).mp (hF c' (Set.mem_univ c'))
        show F c' L = o c' • (if c' = c' then valE P hp L else 0)
        rw [if_pos rfl]
        unfold valE
        split_ifs with hL
        · have h1 := hF'.2.2 (gOf P hp L hL) (standardTuple P)
          rw [gOf_spec] at h1
          rw [h1, ho, LinearMap.map_smul_of_tower, smul_comm, ← algebraMap_smul Kf (o c')]
        · rw [hF'.2.1 L hL, smul_zero]
      · intro c _ hc
        show o c • (if c' = c then valE P hp L else 0) = 0
        rw [if_neg (Ne.symm hc), smul_zero]
      · intro h; exact absurd (Finset.mem_univ c') h
    rw [hFeq]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

include v0 in
theorem Fb_li : LinearIndependent Kf (Fb P hp C) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha c
  have h1 := congrFun (congrFun ha c) (standardTuple P)
  rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single c] at h1
  · change a c • (if c = c then valE P hp (standardTuple P) else 0) = 0 at h1
    rw [if_pos rfl, value_standardTuple P hp v0] at h1
    exact (smul_eq_zero.mp h1).resolve_right (EV_ne P)
  · intro c' _ hc'
    show a c' • (if c = c' then valE P hp (standardTuple P) else 0) = 0
    rw [if_neg (Ne.symm hc'), smul_zero]
  · intro h; exact absurd (Finset.mem_univ c) h

include v0 in
theorem gatC_d : (gatC P hp C).d = Fintype.card C := by
  unfold GAtP.d
  rw [← M_eq P hp C v0]
  haveI := (P.setting v0).frac_O
  have : FaithfulSMul (gatC P hp C).O (gatC P hp C).Kf :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective O Kf)
  exact finrank_span_eq_card ((Fb_li P hp C v0).restrict_scalars' (gatC P hp C).O)

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LevelValuationRings Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField Formalism.MainNotions.Inhab

theorem charZero_of_setting {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (h : HidaSetting p n' W Qq O Kf ι σ j w) : CharZero Kf := by
  haveI := h.frac_alt
  have hW : CharZero W := by
    rcases CharP.char_is_prime_or_zero W (ringChar W) with hl | hl
    · exfalso
      have hz : ((ringChar W : ℕ) : W) = 0 := CharP.cast_eq_zero W _
      by_cases he : ringChar W = p
      · rw [he] at hz; exact h.p_unif.ne_zero hz
      · have hc : IsCoprime ((ringChar W : ℕ) : ℤ) ((p : ℕ) : ℤ) :=
          Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hl h.prime).mpr he)
        have hc' := hc.map (Int.castRingHom W)
        simp only [map_natCast, hz] at hc'
        exact h.p_unif.not_isUnit (isCoprime_zero_left.mp hc')
    · haveI : CharP W 0 := by rw [← hl]; exact ringChar.charP W
      exact CharP.charP_to_charZero W
  have hQ : CharZero Qq := (RingHom.charZero_iff (IsFractionRing.injective W Qq)).mp hW
  exact (RingHom.charZero_iff ι.injective).mp hQ

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField Formalism.MainNotions.G

structure GatBasis (D : D7) where
  embW : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    D.what₂.LL →+* (D.gat u w hg).Kf
  embW_int : ∀ u w hg (x : D.what₂.LL), (0 : WithTop ℤ) ≤ D.what₂.places.val w x ↔
    embW u w hg x ∈ Set.range (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf)
  bas : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    ((D.fm u).lat 0).ι → (D.gat u w hg).Fn
  bas_li : ∀ u w hg, LinearIndependent (D.gat u w hg).Kf (bas u w hg)
  bas_span : ∀ u w hg, Submodule.span (D.gat u w hg).O (Set.range (bas u w hg)) = (D.gat u w hg).M

namespace GatBasis

variable {D : D7} (B : GatBasis D)

def cmp (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : ((D.fm u).lat 0).V →+ (D.gat u w hg).Fn where
  toFun x := ∑ a, B.embW u w hg (((D.fm u).lat 0).b.repr x a) • B.bas u w hg a
  map_zero' := by simp
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]

theorem cmp_apply (u w hg) (x : ((D.fm u).lat 0).V) :
    B.cmp u w hg x = ∑ a, B.embW u w hg (((D.fm u).lat 0).b.repr x a) • B.bas u w hg a := rfl

theorem cmp_smul (u w hg) (r : D.what₂.LL) (x : ((D.fm u).lat 0).V) :
    B.cmp u w hg (r • x) = B.embW u w hg r • B.cmp u w hg x := by
  rw [cmp_apply, cmp_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, mul_smul]

theorem cmp_basis (u w hg) (a : ((D.fm u).lat 0).ι) : B.cmp u w hg (((D.fm u).lat 0).b a) = B.bas u w hg a := by
  rw [cmp_apply, Finset.sum_eq_single a]
  · rw [Module.Basis.repr_self, Finsupp.single_eq_same, map_one, one_smul]
  · intro c _ hc
    rw [Module.Basis.repr_self, Finsupp.single_eq_of_ne hc, map_zero, zero_smul]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem int_mem (u w hg) (r : 𝓞 D.what₂.LL) :
    B.embW u w hg (r : D.what₂.LL) ∈ Set.range (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf) := by
  rw [← B.embW_int, D.val_nonneg_iff]
  exact (D.plEq w).valuation_le_one r

def toCmp (hstd : ∀ u, ((D.fm u).lat 0).L = Submodule.span (𝓞 D.what₂.LL) (Set.range ((D.fm u).lat 0).b)) :
    LatCmp D where
  embW := B.embW
  embW_int := B.embW_int
  cmp := B.cmp
  cmp_smul := B.cmp_smul
  cmp_li u w hg := by
    have : (fun a => B.cmp u w hg (((D.fm u).lat 0).b a)) = B.bas u w hg := funext (B.cmp_basis u w hg)
    rw [this]; exact B.bas_li u w hg
  cmp_M u w hg := by
    rw [← B.bas_span u w hg]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, hstd u] at hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, rfl⟩ := hy
        rw [B.cmp_basis]; exact Submodule.subset_span ⟨a, rfl⟩
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
      | smul r y _ hy =>
        obtain ⟨o, ho⟩ := B.int_mem u w hg r
        have h1 : r • y = (r : D.what₂.LL) • y := (algebraMap_smul D.what₂.LL r y).symm
        rw [h1, B.cmp_smul, ← ho, algebraMap_smul]
        exact Submodule.smul_mem _ o hy
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      refine Submodule.subset_span ⟨((D.fm u).lat 0).b a, ?_, B.cmp_basis u w hg a⟩
      rw [SetLike.mem_coe, hstd u]
      exact Submodule.subset_span ⟨a, rfl⟩

include B in

theorem d_eq (u w hg) (hinj : Function.Injective (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf)) :
    (D.gat u w hg).d = Fintype.card ((D.fm u).lat 0).ι := by
  unfold GAtP.d
  rw [← B.bas_span u w hg]
  refine finrank_span_eq_card ?_
  have : FaithfulSMul (D.gat u w hg).O (D.gat u w hg).Kf := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact (B.bas_li u w hg).restrict_scalars' (D.gat u w hg).O

end GatBasis

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LevelValuationRings Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField Formalism.MainNotions.Inhab

section One

variable {R : Ranks} {H : Host R} {p : ℕ}

theorem charZero_Kn (S : Served H p) :
    haveI : Fact p.Prime := ⟨S.prime⟩
    CharZero (Kn p (orderOf (gPsi S))) :=
  haveI : Fact p.Prime := ⟨S.prime⟩
  charZero_of_setting (hidaSettingOfEven p _ S.five_le (ord_spec S).2.1 (ord_spec S).2.2)

theorem p_ne_Kn (S : Served H p) :
    haveI : Fact p.Prime := ⟨S.prime⟩
    ((p : ℕ) : Kn p (orderOf (gPsi S))) ≠ 0 :=
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI := charZero_Kn S
  Nat.cast_ne_zero.mpr S.prime.ne_zero

theorem nOrb_pos (S : Served H p) : 0 < nOrb S := Nat.card_pos

def gatNZ (S : Served H p) (T : Set ↥(R.Psi)) (r : ℕ) (lam : ↥(R.Psi) → DomWeight (R.N 0))
    (comp : Type) [Fintype comp] (e : ℕ) : GAtP p :=
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI := charZero_Kn S
  { O := On p (orderOf (gPsi S))
    Kf := Kn p (orderOf (gPsi S))
    P := placesOf S T r lam
    comp := comp
    lev := fun _ => levB (placesOf S T r lam) (p_ne_Kn S)
    e := e }


theorem gatNZ_d (S : Served H p) (T : Set ↥(R.Psi)) (r : ℕ) (lam : ↥(R.Psi) → DomWeight (R.N 0))
    (comp : Type) [Fintype comp] [DecidableEq comp] (e : ℕ) : (gatNZ S T r lam comp e).d = Fintype.card comp := by
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI := charZero_Kn S
  exact gatC_d (placesOf S T r lam) (p_ne_Kn S) comp ⟨0, nOrb_pos S⟩

def FbNZ (S : Served H p) (T : Set ↥(R.Psi)) (r : ℕ) (lam : ↥(R.Psi) → DomWeight (R.N 0))
    (comp : Type) [Fintype comp] [DecidableEq comp] (e : ℕ) (c : comp) : (gatNZ S T r lam comp e).Fn :=
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI := charZero_Kn S
  Fb (placesOf S T r lam) (p_ne_Kn S) comp c

theorem FbNZ_li (S : Served H p) (T : Set ↥(R.Psi)) (r : ℕ) (lam : ↥(R.Psi) → DomWeight (R.N 0))
    (comp : Type) [Fintype comp] [DecidableEq comp] (e : ℕ) :
    LinearIndependent (gatNZ S T r lam comp e).Kf (FbNZ S T r lam comp e) := by
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI := charZero_Kn S
  exact Fb_li (placesOf S T r lam) (p_ne_Kn S) comp ⟨0, nOrb_pos S⟩

theorem FbNZ_span (S : Served H p) (T : Set ↥(R.Psi)) (r : ℕ) (lam : ↥(R.Psi) → DomWeight (R.N 0))
    (comp : Type) [Fintype comp] [DecidableEq comp] (e : ℕ) :
    Submodule.span (gatNZ S T r lam comp e).O (Set.range (FbNZ S T r lam comp e)) = (gatNZ S T r lam comp e).M := by
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI := charZero_Kn S
  exact M_eq (placesOf S T r lam) (p_ne_Kn S) comp ⟨0, nOrb_pos S⟩

end One

open Classical in

def withGatNZ (D : D7) (h1 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = Fintype.card ((D.mem u).C.cls 0))
    (rOf : D.what₂.Word → ℕ → ℕ) (eOf : ℕ → ℕ) (bs : D.what₂.Word → ℕ → Set ↥(D.R.Psi)) : D7 :=
  { D with
    gat := fun u w h => gatNZ (served_of h) (bs u (D.what₂.places.resChar w))
      (rOf u (D.what₂.places.resChar w)) (fun ψ => (D.fm u).lam 0 (D.eTau.symm ψ)) ((D.mem u).C.cls 0)
      (eOf (D.what₂.places.resChar w))
    gat_d := fun u _ _ => (gatNZ_d _ _ _ _ _ _).trans (h1 u).symm }

variable (D : D7) (h1 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = Fintype.card ((D.mem u).C.cls 0))
  (rOf : D.what₂.Word → ℕ → ℕ) (eOf : ℕ → ℕ) (bs : D.what₂.Word → ℕ → Set ↥(D.R.Psi))

def gatTiesNZ : GatTies (withGatNZ D h1 rOf eOf bs) where
  gat_k := fun _ _ _ => k_pos D.R
  gat_n := fun _ _ h _ P hP hL σ hσ => @orderOf_frobenius_image_eq _ D.host _ (served_of h) P hP hL σ hσ
  gat_pos := fun u w h => (posPsi (served_of h) (bs u (D.what₂.places.resChar w))).trans D.eTau.symm
  gat_step := fun u w h v s P hP hL σ hσ =>
    @position_succ_eq_mul_frobenius _ D.host _ (served_of h) (bs u (D.what₂.places.resChar w)) _ D.eTau v s P hP hL σ hσ
  gat_lam := fun _ _ _ _ _ _ => rfl


open Classical in

def gatBasisNZ
    (eι : ∀ u, ((D.fm u).lat 0).ι ≃ (D.mem u).C.cls 0)
    (embW : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      D.what₂.LL →+* ((withGatNZ D h1 rOf eOf bs).gat u w hg).Kf)
    (embW_int : ∀ u w hg (x : D.what₂.LL), (0 : WithTop ℤ) ≤ D.what₂.places.val w x ↔
      embW u w hg x ∈ Set.range (algebraMap ((withGatNZ D h1 rOf eOf bs).gat u w hg).O
        ((withGatNZ D h1 rOf eOf bs).gat u w hg).Kf)) :
    GatBasis (withGatNZ D h1 rOf eOf bs) where
  embW := embW
  embW_int := embW_int
  bas u w hg a := FbNZ (served_of hg) _ _ _ ((D.mem u).C.cls 0) _ (eι u a)
  bas_li u w hg := (FbNZ_li (served_of hg) _ _ _ ((D.mem u).C.cls 0) _).comp _ (eι u).injective
  bas_span u w hg := by
    refine Eq.trans ?_ (FbNZ_span (served_of hg) _ _ _ ((D.mem u).C.cls 0) _)
    congr 1
    ext x; constructor
    · rintro ⟨a, rfl⟩; exact ⟨eι u a, rfl⟩
    · rintro ⟨c, rfl⟩
      refine ⟨(eι u).symm c, ?_⟩
      simp only [Equiv.apply_symm_apply]
      congr

end Formalism.BasicNotions.Examples₂.NZ
end
end
