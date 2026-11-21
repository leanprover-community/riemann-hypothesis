import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDistributionInvariantRationalTargetStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilProduct

open GlobalTheory.FinWeilO GlobalTheory.FinWeil GlobalTheory.SplitScalar

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {χS χT : (AE D)ˣ →* Circle} {of oi : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem actO_mul (g g' : GA D S) (h h' : GA D T) (u : WO S T) :
    actO S T (g * g') (h * h') u = actO S T g h (actO S T g' h' u) := by
  unfold actO
  rw [_root_.mul_inv_rev, mt_mul, mt_mul]
  simp only [Matrix.mul_assoc]

theorem actO_one (u : WO S T) : actO S T 1 1 u = u := by
  unfold actO
  rw [inv_one, mt_one, mt_one, Matrix.one_mul, Matrix.mul_one]

theorem exists_parts (p : GA D S × GA D T) : ∃ a ∈ GinfC S, ∃ b ∈ GinfC T, ∃ k ∈ GfC S, ∃ l ∈ GfC T,
    p = (a, b) * (k, l) ∧ p = (k, l) * (a, b) := by
  obtain ⟨a, ha, k, hk, e1⟩ := (GlobalTheory.UnitarySplit.real_finite_split D S).1 p.1
  obtain ⟨b, hb, l, hl, e2⟩ := (GlobalTheory.UnitarySplit.real_finite_split D T).1 p.2
  refine ⟨a, ha, b, hb, k, hk, l, hl, Prod.ext e1 e2, Prod.ext ?_ ?_⟩
  · exact e1.trans ((GlobalTheory.UnitarySplit.real_finite_split D S).2.1 a ha k hk)
  · exact e2.trans ((GlobalTheory.UnitarySplit.real_finite_split D T).2.1 b hb l hl)

theorem fin_eq_smul (hψ : IsStdChar D ψ (-1)) (hf : IsFinWeil ψ S T ΛS ΛT χS χT of) {w : 𝓞 D.host.E} {lam : ℕ →* ℂ}
    (hlam : GlobalTheory.FinWeil.GoodNorm (sgO D) lam) {Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)}
    (h : IsLatRep hψ.1 ΛS ΛT w lam Om) (p : GA D S × GA D T) :
    ∃ c : ℂ, ∀ f : thetaSub ψ S T, of p f = c • (Om p f : WO S T → ℂ) := by
  obtain ⟨a, ha, b, hb, k, hk, l, hl, -, rfl⟩ := exists_parts p
  obtain ⟨om, hom⟩ := exists_extend (thetaSub ψ S T) Om
  have ho : ∀ p f (hf : IsThetaFunO ψ S T f), om p f = (Om p ⟨f, hf⟩ : WO S T → ℂ) := fun p f hf => hom p ⟨f, hf⟩
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.schurLemma_thetaFunctions_orientedPair D ψ hψ S T (of (k, l) * om (k⁻¹, l⁻¹))
    (fun f h1 => by
      rw [Module.End.mul_apply, ho _ f h1]
      exact hf.pres _ _ (Om _ ⟨f, h1⟩).2)
    (fun u f h1 => by
      obtain ⟨f', e1, e2⟩ := h.Heisenberg₂ hψ (inv_mem hk) (inv_mem hl) u ⟨f, h1⟩
      have e1' : (f' : WO S T → ℂ) = heisO ψ S T u f := e1
      rw [Module.End.mul_apply, Module.End.mul_apply, ← e1', hom, e2, hf.Heisenberg₂ k hk l hl _ _ (Om _ ⟨f, h1⟩).2,
        ← actO_mul, mul_inv_cancel, mul_inv_cancel, actO_one, ho _ f h1])
    (fun μ 𝓕 hμ h𝓕 f h1 => by
      rw [Module.End.mul_apply, ho _ f h1, hf.unit μ 𝓕 hμ h𝓕 _ _ (Om _ ⟨f, h1⟩).2]
      exact h.unit hlam μ 𝓕 hμ h𝓕 _ ⟨f, h1⟩)
  refine ⟨c, fun f => ?_⟩
  have e := hc _ (Om (k, l) f).2
  rw [Module.End.mul_apply, hom, ← Module.End.mul_apply, ← map_mul,
    show ((k⁻¹, l⁻¹) : GA D S × GA D T) * (k, l) = 1 from inv_mul_cancel ((k, l) : GA D S × GA D T), map_one,
    Module.End.one_apply] at e
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hf.triv a ha b hb _ f.2, h.real_triv ha hb, e]

theorem fin_inf_comm (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hf : IsFinWeil ψ S T ΛS ΛT χS χT of) (hi : IsInfWeil ψ θ S T oi) (p q : GA D S × GA D T) {f : WO S T → ℂ}
    (h1 : IsThetaFunO ψ S T f) : of p (oi q f) = oi q (of p f) := by
  obtain ⟨lam, hlam, -⟩ := GlobalTheory.FinWeil.exists_goodNorm D
  obtain ⟨w, Om, h⟩ := exists_isLatRep hψ hS hT hlam
  obtain ⟨c, hc⟩ := fin_eq_smul hψ hf hlam h p
  obtain ⟨a, ha, b, hb, k, hk, l, hl, rfl, -⟩ := exists_parts q
  let L : thetaSub ψ S T →ₗ[ℂ] thetaSub ψ S T := (oi (a, b)).restrict fun g hg => hi.pres _ g hg
  have hL : ∀ m, (L m : WO S T → ℂ) = oi (a, b) m := fun _ => rfl
  have e := congrArg Subtype.val (h.comm L (fun x v => Subtype.ext (by
    have e1 := congrArg XF.val (rhoF_real ha hb x)
    rw [coe_rhoF] at e1
    rw [hL, coe_opF, coe_opF, hL, map_smul, hi.Heisenberg₂ a ha b hb _ _ v.2, e1])) p ⟨f, h1⟩)
  rw [map_mul, Module.End.mul_apply, Module.End.mul_apply, hi.triv k hk l hl _ h1,
    hi.triv k hk l hl _ (hf.pres _ _ h1), hc ⟨f, h1⟩, map_smul, ← hL, ← e, ← hc]
  rfl

theorem eventually_smul (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hf : IsFinWeil ψ S T ΛS ΛT χS χT of) {f : WO S T → ℂ} (h1 : IsThetaFunO ψ S T f) :
    ∀ᶠ p in 𝓝 (1 : GA D S × GA D T), ∃ c : ℂ, of p f = c • f := by
  obtain ⟨lam, hlam, -⟩ := GlobalTheory.FinWeil.exists_goodNorm D
  obtain ⟨w, Om, h⟩ := exists_isLatRep hψ hS hT hlam
  filter_upwards [h.eventually_fix hS hT ⟨f, h1⟩] with p hp
  obtain ⟨c, hc⟩ := fin_eq_smul hψ hf hlam h p
  exact ⟨c, by rw [hc ⟨f, h1⟩, hp]⟩

theorem continuous_product (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hf : IsFinWeil ψ S T ΛS ΛT χS χT of) (hi : IsInfWeil ψ θ S T oi) {f : WO S T → ℂ}
    (h1 : IsThetaFunO ψ S T f) (u : WO S T) : Continuous fun p : GA D S × GA D T => of p (oi p f) u := by
  haveI : IsTopologicalGroup (GA D S) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig S.gram))
  haveI : IsTopologicalGroup (GA D T) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig T.gram))
  refine continuous_iff_continuousAt.2 fun q => ?_
  have h2 : Filter.Tendsto (fun p => p * q⁻¹) (𝓝 q) (𝓝 1) :=
    (continuous_id.mul continuous_const).tendsto' q 1 (mul_inv_cancel q)
  have h3 := hf.pres q f h1
  have h4 : ∀ᶠ p in 𝓝 q, ∃ c : ℂ, of p f = c • of q f := by
    filter_upwards [h2.eventually (eventually_smul hψ hS hT hf h3)] with p hp
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right] at hp
  by_cases h0 : of q f = 0
  · refine continuousAt_const.congr (f := fun _ => (0 : ℂ)) ?_
    filter_upwards [h4] with p hp
    obtain ⟨c, hc⟩ := hp
    rw [fin_inf_comm hψ hS hT hf hi p p h1, hc, h0, smul_zero, map_zero]
    rfl
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
    have hx' : of q f x ≠ 0 := hx
    refine (((hf.cont f h1 x).div_const (of q f x)).mul (hi.cont _ h3 u)).continuousAt.congr ?_
    filter_upwards [h4] with p hp
    obtain ⟨c, hc⟩ := hp
    show of p f x / of q f x * oi p (of q f) u = _
    rw [fin_inf_comm hψ hS hT hf hi p p h1, hc, map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_div_cancel_right₀ _ hx']

end GlobalTheory.WeilProduct

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DualSwap

section Alg

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def invT : GL n A →* GL n A where
  toFun g := ⟨((g⁻¹ : GL n A) : Matrix n n A)ᵀ, (g : Matrix n n A)ᵀ,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := Units.ext (by simp)
  map_mul' a b := Units.ext (by simp [Matrix.transpose_mul])

theorem invT_val (g : GL n A) : ((invT g : GL n A) : Matrix n n A) = ((g⁻¹ : GL n A) : Matrix n n A)ᵀ := rfl

theorem invT_inv_val (g : GL n A) : (((invT g)⁻¹ : GL n A) : Matrix n n A) = (g : Matrix n n A)ᵀ := rfl

theorem invT_invT (g : GL n A) : invT (invT g) = g := Units.ext rfl

theorem bc_invT {B : Type} [CommRing B] (φ : A →+* B) (g : GL n A) :
    Formalism.UG.bc φ (invT g) = invT (Formalism.UG.bc φ g) := Units.ext rfl

theorem continuous_invT [TopologicalSpace A] : Continuous (invT : GL n A → GL n A) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem invT_mem (σ : A →+* A) {J J' : Matrix n n A} (h : J'ᵀ * J = 1) {g : GL n A}
    (hg : g ∈ Formalism.UG.UJ σ J') : invT g ∈ Formalism.UG.UJ σ J := by
  have h' : J * J'ᵀ = 1 := mul_eq_one_comm.1 h
  have hg' : (g : Matrix n n A)ᵀ * J'ᵀ * (g : Matrix n n A).map σ = J'ᵀ := by
    have := congrArg Matrix.transpose (show Formalism.UG.cT σ (g : Matrix n n A) * J' * (g : Matrix n n A) = J' from hg)
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Formalism.UG.cT, Matrix.transpose_transpose, ← Matrix.mul_assoc] at this
    exact this
  show ((g⁻¹ : GL n A) : Matrix n n A).map σ * J * ((g⁻¹ : GL n A) : Matrix n n A)ᵀ = J
  have e1 : ((g⁻¹ : GL n A) : Matrix n n A)ᵀ * (g : Matrix n n A)ᵀ = 1 := (invT g).val_inv
  have e2 : ((g⁻¹ : GL n A) : Matrix n n A).map σ * (g : Matrix n n A).map σ = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one σ (map_zero σ) (map_one σ)]
  have e3 : ((g⁻¹ : GL n A) : Matrix n n A).map σ * J * ((g⁻¹ : GL n A) : Matrix n n A)ᵀ * J'ᵀ = 1 := by
    rw [← hg']
    calc _ = ((g⁻¹ : GL n A) : Matrix n n A).map σ * (J * (((g⁻¹ : GL n A) : Matrix n n A)ᵀ * (g : Matrix n n A)ᵀ) * J'ᵀ) *
          (g : Matrix n n A).map σ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e1, Matrix.mul_one, h', Matrix.mul_one, e2]
  calc _ = ((g⁻¹ : GL n A) : Matrix n n A).map σ * J * ((g⁻¹ : GL n A) : Matrix n n A)ᵀ * J'ᵀ * J := by
        rw [Matrix.mul_assoc _ J'ᵀ, h, Matrix.mul_one]
    _ = J := by rw [e3, Matrix.one_mul]

end Alg

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def formLat (G : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {y | ∃ x ∈ Λ, y = star x ᵥ* G}
  zero_mem' := ⟨0, Λ.zero_mem, by simp⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, Λ.add_mem hx hy, by rw [star_add, Matrix.add_vecMul]⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    refine ⟨(⟨star (c : E), Formalism.BasicNotions.Examples₂.star_isIntegral _ c.2⟩ : 𝓞 E) • x, Λ.smul_mem _ hx, ?_⟩
    change (c : E) • (star x ᵥ* G) = star (star (c : E) • x) ᵥ* G
    rw [star_smul, star_star, Matrix.smul_vecMul]

theorem formLat_isLattice {G : Matrix (Fin n) (Fin n) E} (hG : IsUnit G.det) {Λ : Submodule (𝓞 E) (Fin n → E)}
    (h : Submodule.IsLattice E Λ) : Submodule.IsLattice E (formLat G Λ) where
  fg := by
    obtain ⟨s, hs⟩ := h.fg
    classical
    refine ⟨s.image fun x => star x ᵥ* G, le_antisymm (Submodule.span_le.2 ?_) ?_⟩
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      exact ⟨x, hs ▸ Submodule.subset_span hx, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [← hs] at hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hx))
      | zero => simp
      | add x y _ _ hx hy => rw [star_add, Matrix.add_vecMul]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx =>
        have := Submodule.smul_mem _ (⟨star (c : E), Formalism.BasicNotions.Examples₂.star_isIntegral _ c.2⟩ : 𝓞 E) hx
        change star ((c : E) • x) ᵥ* G ∈ _
        rw [star_smul, Matrix.smul_vecMul]
        exact this
  span_eq_top := by
    rw [eq_top_iff]
    intro y _
    have hy : y = star (star (y ᵥ* G⁻¹)) ᵥ* G := by
      rw [star_star, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hG, Matrix.vecMul_one]
    have hx : star (y ᵥ* G⁻¹) ∈ Submodule.span E (Λ : Set (Fin n → E)) := h.span_eq_top ▸ Submodule.mem_top
    rw [hy]
    generalize star (y ᵥ* G⁻¹) = x at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [star_add, Matrix.add_vecMul]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      rw [star_smul, Matrix.smul_vecMul]
      exact Submodule.smul_mem _ _ hx

theorem form_dual {G : Matrix (Fin n) (Fin n) E} (hG : IsUnit G.det) (hh : Gᴴ = G) (x y : Fin n → E) :
    ∑ i, ∑ j, star ((star x ᵥ* G) i) * G⁻¹ᵀ i j * (star y ᵥ* G) j = star (∑ i, ∑ j, star (x i) * G i j * y j) := by
  have h1 : ∀ (M : Matrix (Fin n) (Fin n) E) (a b : Fin n → E), ∑ i, ∑ j, star (a i) * M i j * b j = star a ⬝ᵥ (M *ᵥ b) := by
    intro M a b
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [h1, h1, Matrix.mulVec_transpose, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hG, Matrix.vecMul_one,
    Matrix.star_vecMul, star_star, hh, ← star_dotProduct_star, star_star, dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.star_mulVec, hh]

theorem formLat_selfDual {G : Matrix (Fin n) (Fin n) E} (hG : IsUnit G.det) (hh : Gᴴ = G) {Λ : Submodule (𝓞 E) (Fin n → E)}
    (h : ∀ y, y ∈ Λ ↔ ∀ x ∈ Λ, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * G i j * y j) (y : Fin n → E) :
    y ∈ formLat G Λ ↔ ∀ x ∈ formLat G Λ, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * G⁻¹ᵀ i j * y j := by
  have hy : y = star (star (y ᵥ* G⁻¹)) ᵥ* G := by
    rw [star_star, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hG, Matrix.vecMul_one]
  constructor
  · rintro ⟨z, hz, rfl⟩ _ ⟨x, hx, rfl⟩
    obtain ⟨b, hb⟩ := (h z).1 hz x hx
    exact ⟨⟨star (b : E), Formalism.BasicNotions.Examples₂.star_isIntegral _ b.2⟩, by rw [form_dual hG hh, ← hb]; rfl⟩
  · intro H
    refine ⟨_, (h _).2 fun x hx => ?_, hy⟩
    obtain ⟨b, hb⟩ := H _ ⟨x, hx, rfl⟩
    rw [hy, form_dual hG hh] at hb
    exact ⟨⟨star (b : E), Formalism.BasicNotions.Examples₂.star_isIntegral _ b.2⟩, by
      change star (b : E) = _
      rw [hb, star_star]⟩

theorem toLin_apply (M : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    Matrix.toLinearMapₛₗ₂' E (starRingEnd E) (RingHom.id E) M x y = ∑ i, ∑ j, star (x i) * M i j * y j := by
  rw [Matrix.toLinearMapₛₗ₂'_apply]
  simp [starRingEnd_apply, mul_comm, mul_left_comm, mul_assoc]

end Lat

variable {D : D7}

theorem gram_herm (S : HSp D) : S.gramᴴ = S.gram :=
  Matrix.ext fun i j => GlobalTheory.LatVac.gram_star S j i

theorem gramInvT_star (S : HSp D) (i j : Fin S.rank) : star (S.gram⁻¹ᵀ i j) = S.gram⁻¹ᵀ j i := by
  have : (S.gram⁻¹)ᴴ = S.gram⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, gram_herm]
  exact congrFun (congrFun this i) j

@[reducible] def dualSp (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (hΛ : IsSelfDualC S Λ) : HSp D where
  V := Fin S.rank → D.host.E
  hT := Matrix.toLinearMapₛₗ₂' D.host.E (starRingEnd D.host.E) (RingHom.id D.host.E) S.gram⁻¹ᵀ
  herm := ⟨fun x y => by
    rw [toLin_apply, toLin_apply, starRingEnd_apply, star_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul', star_mul', star_star, gramInvT_star]; ring⟩
  nondeg := by
    have hd := GlobalTheory.LatVac.gram_det_isUnit S
    constructor
    · intro x hx
      have h1 : star x ᵥ* S.gram⁻¹ᵀ = 0 := by
        funext j
        have := hx (Pi.single j 1)
        rw [toLin_apply] at this
        simpa [Pi.single_apply, Matrix.vecMul, dotProduct] using this
      have h2 := congrArg (· ᵥ* S.gramᵀ) h1
      simp only [Matrix.vecMul_vecMul, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.transpose_one,
        Matrix.vecMul_one, Matrix.zero_vecMul] at h2
      exact star_eq_zero.1 h2
    · intro y hy
      have h1 : S.gram⁻¹ᵀ *ᵥ y = 0 := by
        funext j
        have := hy (Pi.single j 1)
        rw [toLin_apply] at this
        simpa [Pi.single_apply, Matrix.mulVec, dotProduct, apply_ite] using this
      have h2 := congrArg (S.gramᵀ *ᵥ ·) h1
      simp only [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hd, Matrix.transpose_one,
        Matrix.one_mulVec, Matrix.mulVec_zero] at h2
      exact h2
  rank := S.rank
  rank_eq := Module.finrank_fin_fun _
  frame := Pi.basisFun _ _
  sig := S.sig
  L0 := formLat S.gram Λ
  standardTuple_isLattice := formLat_isLattice (GlobalTheory.LatVac.gram_det_isUnit S) hΛ.1
  baseLattice_isUnimodular := by
    ext y
    rw [formLat_selfDual (GlobalTheory.LatVac.gram_det_isUnit S) (gram_herm S) hΛ.2]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one,
      LinearMap.restrictScalars_apply, toLin_apply]

variable (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (hΛ : IsSelfDualC S Λ)

theorem dualSp_gram : (dualSp S Λ hΛ).gram = S.gram⁻¹ᵀ := by
  refine Matrix.ext fun i j => ?_
  change Matrix.toLinearMapₛₗ₂' D.host.E (starRingEnd D.host.E) (RingHom.id D.host.E) S.gram⁻¹ᵀ
    (Pi.basisFun _ _ i) (Pi.basisFun _ _ j) = _
  rw [toLin_apply]
  simp [Pi.single_apply, apply_ite]

theorem dualSp_selfDual : IsSelfDualC (dualSp S Λ hΛ) (formLat S.gram Λ) := by
  refine ⟨formLat_isLattice (GlobalTheory.LatVac.gram_det_isUnit S) hΛ.1, fun y => ?_⟩
  rw [dualSp_gram]
  exact formLat_selfDual (GlobalTheory.LatVac.gram_det_isUnit S) (gram_herm S) hΛ.2 y

theorem gram_dual_mul : (dualSp S Λ hΛ).gramᵀ * S.gram = 1 := by
  rw [dualSp_gram, Matrix.transpose_transpose, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S)]

theorem gram_mul_dual : S.gramᵀ * (dualSp S Λ hΛ).gram = 1 := by
  rw [dualSp_gram, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S), Matrix.transpose_one]

theorem dualSp_gram_inv : (dualSp S Λ hΛ).gram⁻¹ = S.gramᵀ := Matrix.inv_eq_left_inv (gram_mul_dual S Λ hΛ)

def dualG : GA D (dualSp S Λ hΛ) →* GA D S :=
  (invT.comp (matHom (dualSp S Λ hΛ))).codRestrict (HR (AF D.host.F) D.sp.cm.sig S.gram) fun g =>
    invT_mem _ (J' := JR (AF D.host.F) (dualSp S Λ hΛ).gram) (by
      rw [JR, JR, ← Matrix.transpose_map, ← Matrix.map_mul, gram_dual_mul,
        Matrix.map_one _ (map_zero _) (map_one _)]) g.2

theorem matHom_dualG (g : GA D (dualSp S Λ hΛ)) : matHom S (dualG S Λ hΛ g) = invT (matHom (dualSp S Λ hΛ) g) := rfl

theorem mt_dualG (g : GA D (dualSp S Λ hΛ)) :
    Formalism.L2.Theta.mt S (dualG S Λ hΛ g) = (Formalism.L2.Theta.mt (dualSp S Λ hΛ) g⁻¹)ᵀ := rfl

theorem mt_dualG_inv (g : GA D (dualSp S Λ hΛ)) :
    Formalism.L2.Theta.mt S (dualG S Λ hΛ g)⁻¹ = (Formalism.L2.Theta.mt (dualSp S Λ hΛ) g)ᵀ := rfl

theorem continuous_dualG : Continuous (dualG S Λ hΛ) :=
  (continuous_invT.comp continuous_subtype_val).subtype_mk _

theorem dualG_mem_GfC {g : GA D (dualSp S Λ hΛ)} (hg : g ∈ GfC (dualSp S Λ hΛ)) : dualG S Λ hΛ g ∈ GfC S := by
  have h : infHom S (dualG S Λ hΛ g) = invT (infHom (dualSp S Λ hΛ) g) := Units.ext rfl
  rw [GfC, MonoidHom.mem_ker] at hg ⊢
  rw [h, hg, map_one]

theorem dualG_mem_GinfC {g : GA D (dualSp S Λ hΛ)} (hg : g ∈ GinfC (dualSp S Λ hΛ)) : dualG S Λ hΛ g ∈ GinfC S := by
  have h : finHom S (dualG S Λ hΛ g) = invT (finHom (dualSp S Λ hΛ) g) := Units.ext rfl
  rw [GinfC, MonoidHom.mem_ker] at hg ⊢
  rw [h, hg, map_one]

theorem exists_dualG_of_GQ {γ : GA D S} (hγ : γ ∈ GQ S) : ∃ γ' ∈ GQ (dualSp S Λ hΛ), dualG S Λ hΛ γ' = γ := by
  have hγ' : matHom S γ ∈ HFin (AF D.host.F) D.sp.cm.sig S.gram := hγ
  obtain ⟨g, hg, hgγ⟩ := hγ'
  have h1 : invT (matHom S γ) ∈ HR (AF D.host.F) D.sp.cm.sig (dualSp S Λ hΛ).gram :=
    invT_mem _ (J' := JR (AF D.host.F) S.gram) (by
      rw [JR, JR, ← Matrix.transpose_map, ← Matrix.map_mul, gram_mul_dual,
        Matrix.map_one _ (map_zero _) (map_one _)]) γ.2
  have h2 : invT (matHom S γ) ∈ HFin (AF D.host.F) D.sp.cm.sig (dualSp S Λ hΛ).gram :=
    ⟨invT g, invT_mem _ (gram_mul_dual S Λ hΛ) hg, by rw [bc_invT, hgγ]⟩
  refine ⟨⟨invT (matHom S γ), h1⟩, h2, Subtype.ext ?_⟩
  exact invT_invT (matHom S γ)

end GlobalTheory.DualSwap

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DualSwap

variable {D : D7}

def trF {m n : ℕ} : (Mx D m n → ℂ) ≃ₗ[ℂ] (Mx D n m → ℂ) where
  toFun f x := f xᵀ
  invFun f x := f xᵀ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem trF_trF {m n : ℕ} (f : Mx D m n → ℂ) : trF (trF f) = f := rfl

theorem sum_sum_sum_sum_comm {M : Type} [AddCommMonoid M] {m n : ℕ} (F : Fin m → Fin m → Fin n → Fin n → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ d, ∑ c, ∑ b, ∑ a, F a b c d := by
  calc _ = ∑ b, ∑ a, ∑ d, ∑ c, F a b c d := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ b, ∑ d, ∑ c, ∑ a, F a b c d := by
        refine Finset.sum_congr rfl fun _ _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

variable (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
  (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)

theorem hO_tr (x y : WO S T) : hO (dualSp T ΛT hT) (dualSp S ΛS hS) xᵀ yᵀ = hO S T x y := by
  unfold hO
  rw [dualSp_gram_inv, dualSp_gram, sum_sum_sum_sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  simp only [Matrix.transpose_apply]
  ring

theorem symplOH_tr (x y : WO S T) : symplOH (dualSp T ΛT hT) (dualSp S ΛS hS) xᵀ yᵀ = symplOH S T x y := by
  unfold symplOH symplO
  rw [hO_tr]

theorem trF_heis (w : WO (dualSp T ΛT hT) (dualSp S ΛS hS)) (f : WO (dualSp T ΛT hT) (dualSp S ΛS hS) → ℂ) :
    trF (heisO ψ (dualSp T ΛT hT) (dualSp S ΛS hS) w f) = heisO ψ S T wᵀ (trF f) := by
  funext x
  change ψ (symplOH (dualSp T ΛT hT) (dualSp S ΛS hS) xᵀ wᵀᵀ) * f (xᵀ + w) = ψ (symplOH S T x wᵀ) * f (xᵀ + w)
  rw [symplOH_tr]

theorem trF_heis' (w : WO S T) (f : WO S T → ℂ) :
    trF (heisO ψ S T w f) = heisO ψ (dualSp T ΛT hT) (dualSp S ΛS hS) wᵀ (trF f) := by
  funext x
  change ψ (symplOH S T xᵀ w) * f (xᵀ + w) = ψ (symplOH (dualSp T ΛT hT) (dualSp S ΛS hS) xᵀᵀ wᵀ) * f (xᵀ + w)
  rw [symplOH_tr]

def trA {m n : ℕ} : Mx D m n →+ Mx D n m where
  toFun x := xᵀ
  map_zero' := rfl
  map_add' _ _ := rfl

theorem continuous_tr {m n : ℕ} : Continuous (fun x : Mx D m n => (xᵀ : Mx D n m)) := continuous_id.matrix_transpose

theorem theta_trF {f : WO (dualSp T ΛT hT) (dualSp S ΛS hS) → ℂ} (h : IsThetaFunO ψ (dualSp T ΛT hT) (dualSp S ΛS hS) f) :
    IsThetaFunO ψ S T (trF f) where
  quasi γ w := by
    have := h.quasi γᵀ wᵀ
    rw [← symplOH_tr S T ΛS ΛT hS hT]
    exact this
  level := by
    obtain ⟨U, hU, hU'⟩ := h.level
    refine ⟨U.comap trA, hU.preimage continuous_tr, fun u hu hu' => ?_⟩
    have := congrArg trF (hU' uᵀ hu (congrArg Matrix.transpose hu'))
    rwa [trF_heis] at this
  cont := h.cont.comp continuous_tr
  smooth k L hL hL' w := h.smooth k (trA.comp L) (continuous_tr.comp hL) (fun t => congrArg Matrix.transpose (hL' t)) wᵀ

theorem theta_trF' {f : WO S T → ℂ} (h : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ (dualSp T ΛT hT) (dualSp S ΛS hS) (trF f) where
  quasi γ w := by
    have := h.quasi γᵀ wᵀ
    rw [← symplOH_tr S T ΛS ΛT hS hT] at this
    exact this
  level := by
    obtain ⟨U, hU, hU'⟩ := h.level
    refine ⟨U.comap trA, hU.preimage continuous_tr, fun u hu hu' => ?_⟩
    have := congrArg trF (hU' uᵀ hu (congrArg Matrix.transpose hu'))
    rwa [trF_heis' ψ S T ΛS ΛT hS hT] at this
  cont := h.cont.comp continuous_tr
  smooth k L hL hL' w := h.smooth k (trA.comp L) (continuous_tr.comp hL) (fun t => congrArg Matrix.transpose (hL' t)) wᵀ

theorem actO_tr (g : GA D (dualSp T ΛT hT)) (h : GA D (dualSp S ΛS hS)) (x : WO (dualSp T ΛT hT) (dualSp S ΛS hS)) :
    actO S T (dualG S ΛS hS h) (dualG T ΛT hT g) xᵀ = (actO (dualSp T ΛT hT) (dualSp S ΛS hS) g h x)ᵀ := by
  unfold actO
  rw [mt_dualG, mt_dualG_inv, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]

def swapOm (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) :
    GA D (dualSp T ΛT hT) × GA D (dualSp S ΛS hS) →* Module.End ℂ (WO (dualSp T ΛT hT) (dualSp S ΛS hS) → ℂ) where
  toFun p := (trF : (WO S T → ℂ) ≃ₗ[ℂ] _).toLinearMap ∘ₗ om (dualG S ΛS hS p.2, dualG T ΛT hT p.1) ∘ₗ
    (trF : _ ≃ₗ[ℂ] (WO S T → ℂ)).toLinearMap
  map_one' := by
    refine LinearMap.ext fun f => ?_
    have : ((dualG S ΛS hS 1, dualG T ΛT hT 1) : GA D S × GA D T) = 1 := by rw [map_one, map_one]; rfl
    change trF (om (dualG S ΛS hS 1, dualG T ΛT hT 1) (trF f)) = f
    rw [this, map_one]; rfl
  map_mul' p q := by
    refine LinearMap.ext fun f => ?_
    have : ((dualG S ΛS hS (p.2 * q.2), dualG T ΛT hT (p.1 * q.1)) : GA D S × GA D T) =
      (dualG S ΛS hS p.2, dualG T ΛT hT p.1) * (dualG S ΛS hS q.2, dualG T ΛT hT q.1) := by rw [map_mul, map_mul]; rfl
    change trF (om (dualG S ΛS hS (p.2 * q.2), dualG T ΛT hT (p.1 * q.1)) (trF f)) =
      trF (om (dualG S ΛS hS p.2, dualG T ΛT hT p.1) (om (dualG S ΛS hS q.2, dualG T ΛT hT q.1) (trF f)))
    rw [this, map_mul]; rfl

theorem swapOm_apply (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D (dualSp T ΛT hT))
    (h : GA D (dualSp S ΛS hS)) (f : WO (dualSp T ΛT hT) (dualSp S ΛS hS) → ℂ) :
    swapOm S T ΛS ΛT hS hT om (g, h) f = trF (om (dualG S ΛS hS h, dualG T ΛT hT g) (trF f)) := rfl

theorem swap_unitary {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (h : IsUnitaryOnTheta ψ S T om) :
    IsUnitaryOnTheta ψ (dualSp T ΛT hT) (dualSp S ΛS hS) (swapOm S T ΛS ΛT hS hT om) where
  pres p f hf := theta_trF' ψ S T ΛS ΛT hS hT (h.pres _ _ (theta_trF ψ S T ΛS ΛT hS hT hf))
  cont f hf w := (h.cont _ (theta_trF ψ S T ΛS ΛT hS hT hf) wᵀ).comp
    (((continuous_dualG S ΛS hS).comp continuous_snd).prodMk ((continuous_dualG T ΛT hT).comp continuous_fst))
  unit μ 𝓕 hμ h𝓕 p f hf := by
    have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
    have : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
    have : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
    have : IsTopologicalAddGroup (WO (dualSp T ΛT hT) (dualSp S ΛS hS)) := Pi.topologicalAddGroup
    have : BorelSpace (WO S T) := ⟨rfl⟩
    have : BorelSpace (WO (dualSp T ΛT hT) (dualSp S ΛS hS)) := ⟨rfl⟩
    let e : WO (dualSp T ΛT hT) (dualSp S ΛS hS) ≃ₜ+ WO S T :=
      { toFun := fun x => xᵀ, invFun := fun x => xᵀ, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
        map_add' := fun _ _ => rfl, continuous_toFun := continuous_tr, continuous_invFun := continuous_tr }
    let m : WO (dualSp T ΛT hT) (dualSp S ΛS hS) ≃ᵐ WO S T := e.toHomeomorph.toMeasurableEquiv
    have hH : (μ.map m).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
    have hp : MeasurePreserving m.symm (μ.map m) μ := (m.measurable.measurePreserving μ).symm m
    have hF : IsAddFundamentalDomain (ratL T S) (m.symm ⁻¹' 𝓕) (μ.map m) := by
      refine h𝓕.preimage_of_equiv hp.quasiMeasurePreserving
        (e := fun γ => (⟨γ.1ᵀ, by obtain ⟨γ, δ, rfl⟩ := γ; exact ⟨δᵀ, rfl⟩⟩ : ratL T S)) ?_ fun γ x => rfl
      constructor
      · intro a b hab
        exact Subtype.ext (congrArg Matrix.transpose (congrArg Subtype.val hab))
      · rintro ⟨_, δ, rfl⟩
        exact ⟨⟨_, δᵀ, rfl⟩, rfl⟩
    have key := h.unit (μ.map m) _ hH hF (dualG S ΛS hS p.2, dualG T ΛT hT p.1) _ (theta_trF ψ S T ΛS ΛT hS hT hf)
    have e1 := hp.setLIntegral_comp_preimage_emb m.symm.measurableEmbedding
      (fun w => ‖swapOm S T ΛS ΛT hS hT om p f w‖ₑ ^ 2) 𝓕
    have e2 := hp.setLIntegral_comp_preimage_emb m.symm.measurableEmbedding (fun w => ‖f w‖ₑ ^ 2) 𝓕
    exact e1.symm.trans (key.trans e2)

theorem supp_inv {A : Type} [CommRing A] {n : ℕ} (ε : A) (g : GL (Fin n) A)
    (h : ∀ i j, ε * ((g : Matrix (Fin n) (Fin n) A) - 1) i j = ((g : Matrix (Fin n) (Fin n) A) - 1) i j) (i j : Fin n) :
    ε * (((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)ᵀ - 1) i j =
      (((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)ᵀ - 1) i j := by
  have h1 : ε • ((g : Matrix (Fin n) (Fin n) A) - 1) = (g : Matrix (Fin n) (Fin n) A) - 1 := Matrix.ext h
  have h2 : ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1 =
      -(((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) * ((g : Matrix (Fin n) (Fin n) A) - 1)) := by
    rw [Matrix.mul_sub, Units.inv_mul, Matrix.mul_one, neg_sub]
  have h3 : ε • (((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1) =
      ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1 := by
    rw [h2, smul_neg, ← Matrix.mul_smul, h1]
  have h4 := congrArg Matrix.transpose h3
  rw [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_one] at h4
  exact congrFun (congrFun h4 i) j

theorem det_inv_at {A : Type} [CommRing A] {n : ℕ} {e : A} (he : e * e = e) (g : GL (Fin n) A) (x : Aˣ)
    (h : (x : A) = e * (g : Matrix (Fin n) (Fin n) A).det + (1 - e)) :
    ((x⁻¹ : Aˣ) : A) = e * (((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)ᵀ).det + (1 - e) := by
  have h1 : (g : Matrix (Fin n) (Fin n) A).det * ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [h, Matrix.det_transpose]
  generalize (g : Matrix (Fin n) (Fin n) A).det = a at h1
  generalize ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A).det = b at h1
  linear_combination (e * e) * h1 + (2 - a - b) * he

theorem mem_latO_tr (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (u : WO (dualSp T ΛT hT) (dualSp S ΛS hS)) :
    u ∈ latO (dualSp T ΛT hT) (dualSp S ΛS hS) (formLat T.gram ΛT) (formLat S.gram ΛS) P ↔
      (uᵀ : WO S T) ∈ latO S T ΛS ΛT P := by
  have key : ∀ (t : Fin T.rank → D.host.E) (j : Fin T.rank),
      ∑ k, star ((star t ᵥ* T.gram) k) * (dualSp T ΛT hT).gram k j = t j := by
    intro t j
    have : star (star t ᵥ* T.gram) ᵥ* (dualSp T ΛT hT).gram = t := by
      rw [dualSp_gram, Matrix.vecMul_transpose, Matrix.star_vecMul, star_star, gram_herm, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit T), Matrix.one_mulVec]
    exact congrFun this j
  constructor
  · intro hu
    induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hP, a, ha, _, ⟨t, ht, rfl⟩, _, ⟨s, hs, rfl⟩, rfl⟩ := hw
      refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, Matrix.ext fun i j => ?_⟩
      simp only [Matrix.transpose_apply, Matrix.of_apply]
      rw [key, mul_right_comm]
      rfl
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  · intro hu
    have : ∀ w ∈ latO S T ΛS ΛT P,
        (wᵀ : WO (dualSp T ΛT hT) (dualSp S ΛS hS)) ∈
          latO (dualSp T ΛT hT) (dualSp S ΛS hS) (formLat T.gram ΛT) (formLat S.gram ΛS) P := by
      intro w hw
      induction hw using AddSubgroup.closure_induction with
      | mem w hw =>
        obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
        refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, _, ⟨t, ht, rfl⟩, _, ⟨s, hs, rfl⟩, Matrix.ext fun i j => ?_⟩
        simp only [Matrix.transpose_apply, Matrix.of_apply]
        rw [key, mul_right_comm]
        rfl
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | neg x _ hx => exact neg_mem hx
    exact this _ hu

theorem swap_fin {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (h : IsFinWeil ψ S T ΛS ΛT χS χT om) :
    IsFinWeil ψ (dualSp T ΛT hT) (dualSp S ΛS hS) (formLat T.gram ΛT) (formLat S.gram ΛS) χT χS
      (swapOm S T ΛS ΛT hS hT om) where
  toIsUnitaryOnTheta := swap_unitary ψ S T ΛS ΛT hS hT h.toIsUnitaryOnTheta
  triv g hg k hk f hf := by
    rw [swapOm_apply, h.triv _ (dualG_mem_GinfC S ΛS hS hk) _ (dualG_mem_GinfC T ΛT hT hg) _
      (theta_trF ψ S T ΛS ΛT hS hT hf), trF_trF]
  Heisenberg₂ g hg k hk w f hf := by
    rw [swapOm_apply, swapOm_apply, trF_heis, h.Heisenberg₂ _ (dualG_mem_GfC S ΛS hS hk) _ (dualG_mem_GfC T ΛT hT hg) _ _
      (theta_trF ψ S T ΛS ΛT hS hT hf), trF_heis' ψ S T ΛS ΛT hS hT, actO_tr, Matrix.transpose_transpose]
  split e he g k hg hk x y hx hy := by
    obtain ⟨r, hr, H⟩ := h.split e he (dualG S ΛS hS k) (dualG T ΛT hT g)
      (supp_inv _ (matHom (dualSp S ΛS hS) k) hk) (supp_inv _ (matHom (dualSp T ΛT hT) g) hg) y⁻¹ x⁻¹
      (det_inv_at he.1 (matHom (dualSp S ΛS hS) k) y hy) (det_inv_at he.1 (matHom (dualSp T ΛT hT) g) x hx)
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    have := H (ℓ ∘ₗ (trF : (WO S T → ℂ) ≃ₗ[ℂ] _).toLinearMap) (fun u hu f hf => by
      change ℓ (trF (heisO ψ S T u f)) = ℓ (trF f)
      rw [trF_heis' ψ S T ΛS ΛT hS hT]
      exact hℓ _ (fun i j => hu j i) _ (theta_trF' ψ S T ΛS ΛT hS hT hf)) _ (theta_trF ψ S T ΛS ΛT hS hT hf)
    have e1 : splitFacO χS χT y⁻¹ x⁻¹ = splitFacO χT χS x y := by
      rw [splitFacO, splitFacO, map_inv, map_inv, inv_inv, mul_comm]
    rw [e1] at this
    exact this
  inert v ε hv g k hg hk hL f hf hfix := by
    have := h.inert v ε hv (dualG S ΛS hS k) (dualG T ΛT hT g)
      (supp_inv _ (matHom (dualSp S ΛS hS) k) hk) (supp_inv _ (matHom (dualSp T ΛT hT) g) hg)
      (fun u => by
        have h1 := hL uᵀ
        rw [mem_latO_tr, mem_latO_tr, ← actO_tr] at h1
        exact h1)
      _ (theta_trF ψ S T ΛS ΛT hS hT hf) (fun u hu => by
        have h1 := congrArg trF (hfix uᵀ ((mem_latO_tr S T ΛS ΛT hS hT _ _).2 hu))
        rw [trF_heis] at h1
        exact h1)
    rw [swapOm_apply, this, trF_trF]

theorem cartan_tr {k : ℕ} {G G' s : Matrix (Fin k) (Fin k) ℂ} (hG : G'ᵀ * G = 1) (h : IsCartanInv G' s) :
    IsCartanInv G sᵀ := by
  obtain ⟨h1, h2, h3⟩ := h
  have hG' : G * G'ᵀ = 1 := mul_eq_one_comm.1 hG
  have e1 : sᵀ * sᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  have e2 : sᵀᴴ * sᵀᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
  have e3 : sᵀ * G'ᵀ * sᵀᴴ = G'ᵀ := by
    have := congrArg Matrix.transpose h2
    rw [Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.mul_assoc] at this
    exact this
  refine ⟨e1, ?_, ?_⟩
  · have e4 : sᵀᴴ * G * sᵀ * G'ᵀ = 1 := by
      rw [← e3]
      calc _ = sᵀᴴ * (G * (sᵀ * sᵀ) * G'ᵀ) * sᵀᴴ := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [e1, Matrix.mul_one, hG', Matrix.mul_one, e2]
    calc _ = sᵀᴴ * G * sᵀ * G'ᵀ * G := by rw [Matrix.mul_assoc _ G'ᵀ, hG, Matrix.mul_one]
      _ = G := by rw [e4, Matrix.one_mul]
  · have e5 : ((G' * s)ᵀ)⁻¹ = G * sᵀ := by
      refine Matrix.inv_eq_left_inv ?_
      rw [Matrix.transpose_mul]
      calc _ = G * (sᵀ * sᵀ) * G'ᵀ := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [e1, Matrix.mul_one, hG']
    rw [← e5]
    exact h3.transpose.inv

theorem detPlus_tr {m n : ℕ} (sS a : Matrix (Fin n) (Fin n) ℂ) (sT b : Matrix (Fin m) (Fin m) ℂ) :
    detPlus sTᵀ sSᵀ bᵀ aᵀ = detPlus sS sT a b := by
  unfold detPlus
  have hk : ∀ (x : Matrix (Fin n) (Fin n) ℂ) (y : Matrix (Fin m) (Fin m) ℂ),
      Matrix.kroneckerMap (· * ·) x y =
        (Matrix.kroneckerMap (· * ·) y x).submatrix (Equiv.prodComm (Fin n) (Fin m)) (Equiv.prodComm (Fin n) (Fin m)) :=
    fun x y => Matrix.ext fun _ _ => mul_comm _ _
  rw [← Matrix.det_submatrix_equiv_self (Equiv.prodComm (Fin n) (Fin m)) (_ + _), hk sSᵀ, hk aᵀ,
    ← Matrix.submatrix_one_equiv (Equiv.prodComm (Fin n) (Fin m))]
  congr 1
  exact congrArg₂ (· + ·) (congrArg ((1 / 2 : ℂ) • ·) (Matrix.submatrix_mul_equiv
    (1 + Matrix.kroneckerMap (· * ·) sT sSᵀ) (Matrix.kroneckerMap (· * ·) b aᵀ) _ (Equiv.prodComm (Fin n) (Fin m)) _)) rfl

theorem lineAt_tr {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    lineAt θ τ zᵀ t = (lineAt θ τ z t)ᵀ := by
  have h1 : IsLineAt θ τ z (lineAt θ τ z) :=
    Classical.epsilon_spec ((GlobalTheory.RealLineAt.lineAt_exists_unique D).1 θ hθ m n τ z)
  have h2 : IsLineAt θ τ zᵀ (lineAt θ τ zᵀ) :=
    Classical.epsilon_spec ((GlobalTheory.RealLineAt.lineAt_exists_unique D).1 θ hθ n m τ zᵀ)
  have h3 : IsLineAt θ τ zᵀ (trA.comp (lineAt θ τ z)) := by
    refine ⟨continuous_tr.comp h1.1, fun t => congrArg Matrix.transpose (h1.2.1 t), fun t τ' => ?_⟩
    have := congrArg Matrix.transpose (h1.2.2 t τ')
    refine Eq.trans this ?_
    split_ifs <;> rfl
  rw [(GlobalTheory.RealLineAt.lineAt_exists_unique D).2 θ hθ n m τ zᵀ _ _ h2 h3]
  rfl

theorem dRho_tr {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (f : WO (dualSp T ΛT hT) (dualSp S ΛS hS) → ℂ) :
    dRho (heisO ψ S T) θ τ z (trF f) = trF (dRho (heisO ψ (dualSp T ΛT hT) (dualSp S ΛS hS)) θ τ zᵀ f) := by
  funext x
  change deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (trF f) x) 0 =
    deriv (fun t : ℝ => trF (heisO ψ (dualSp T ΛT hT) (dualSp S ΛS hS) (lineAt θ τ zᵀ t) f) x) 0
  congr 1
  funext t
  rw [trF_heis, lineAt_tr hθ, Matrix.transpose_transpose]

theorem swap_inf {θ : InfFam D} (hθ : IsInfFam θ) {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (h : IsInfWeil ψ θ S T om) :
    IsInfWeil ψ θ (dualSp T ΛT hT) (dualSp S ΛS hS) (swapOm S T ΛS ΛT hS hT om) where
  toIsUnitaryOnTheta := swap_unitary ψ S T ΛS ΛT hS hT h.toIsUnitaryOnTheta
  triv g hg k hk f hf := by
    rw [swapOm_apply, h.triv _ (dualG_mem_GfC S ΛS hS hk) _ (dualG_mem_GfC T ΛT hT hg) _
      (theta_trF ψ S T ΛS ΛT hS hT hf), trF_trF]
  Heisenberg₂ g hg k hk w f hf := by
    rw [swapOm_apply, swapOm_apply, trF_heis, h.Heisenberg₂ _ (dualG_mem_GinfC S ΛS hS hk) _ (dualG_mem_GinfC T ΛT hT hg) _ _
      (theta_trF ψ S T ΛS ΛT hS hT hf), trF_heis' ψ S T ΛS ΛT hS hT, actO_tr, Matrix.transpose_transpose]
  vac sT sS hsT hsS g hg k hk cg ck f hf hv := by
    have gS : ∀ τ, (gramAt D (dualSp S ΛS hS) τ)ᵀ * gramAt D S τ = 1 := fun τ => by
      rw [gramAt, gramAt, ← Matrix.transpose_map, ← Matrix.map_mul, gram_dual_mul,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have gT : ∀ τ, (gramAt D (dualSp T ΛT hT) τ)ᵀ * gramAt D T τ = 1 := fun τ => by
      rw [gramAt, gramAt, ← Matrix.transpose_map, ← Matrix.map_mul, gram_dual_mul,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have comm : ∀ (V : HSp D) (τ : D.what₂.Tau) (s : Matrix (Fin V.rank) (Fin V.rank) ℂ) (a : GA D V),
        s * compAt θ τ (Formalism.L2.Theta.mt V a) = compAt θ τ (Formalism.L2.Theta.mt V a) * s →
        sᵀ * (compAt θ τ (Formalism.L2.Theta.mt V a⁻¹))ᵀ = (compAt θ τ (Formalism.L2.Theta.mt V a⁻¹))ᵀ * sᵀ := by
      intro V τ s a ha
      let u : GL (Fin V.rank) ℂ := Formalism.UG.bc ((θ τ).comp (infPart D)) (matHom V a)
      have hc : Commute s (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) := ha
      have hc' : s * ((u⁻¹ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) = _ := hc.units_inv_right
      rw [← Matrix.transpose_mul, ← Matrix.transpose_mul]
      exact congrArg Matrix.transpose hc'.symm
    have := h.vac (fun τ => (sS τ)ᵀ) (fun τ => (sT τ)ᵀ) (fun τ => cartan_tr (gS τ) (hsS τ))
      (fun τ => cartan_tr (gT τ) (hsT τ)) _ (dualG_mem_GinfC S ΛS hS hk) _ (dualG_mem_GinfC T ΛT hT hg)
      (fun τ => comm (dualSp S ΛS hS) τ (sS τ) k (ck τ)) (fun τ => comm (dualSp T ΛT hT) τ (sT τ) g (cg τ))
      _ (theta_trF ψ S T ΛS ΛT hS hT hf) (fun τ z => by
        have h1 := congrArg trF (hv τ zᵀ)
        have h2 : (cplxO (sS τ)ᵀ (sT τ)ᵀ z)ᵀ = cplxO (sT τ) (sS τ) zᵀ := by
          rw [cplxO, cplxO, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
            Matrix.transpose_transpose, Matrix.mul_assoc]
        rw [annih, map_add, map_smul, map_zero] at h1
        rw [annih, dRho_tr ψ S T ΛS ΛT hS hT hθ, dRho_tr ψ S T ΛS ΛT hS hT hθ, h2]
        exact h1)
    rw [swapOm_apply, this, map_smul, trF_trF]
    congr 1
    exact Finset.prod_congr rfl fun τ _ => detPlus_tr (sT τ) _ (sS τ) _

theorem automorphy_source : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ η, IsEtaTilde D η → ∀ (of oi : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsFinWeil ψ S T ΛS ΛT (η ^ S.rank) (η ^ T.rank) of → IsInfWeil ψ θ S T oi → ∀ γ ∈ GQ S, ∀ f, IsThetaFunO ψ S T f → of (γ, 1) (oi (γ, 1) f) 0 = f 0 := by
  intro D ψ hψ S T θ hθ ΛS ΛT hS hT η hη of oi hf hi γ hγ f hth
  obtain ⟨γ', hγ', rfl⟩ := exists_dualG_of_GQ S ΛS hS hγ
  have := GlobalTheory.T.thetaDistribution_invariant_rationalTarget D ψ hψ (dualSp T ΛT hT) (dualSp S ΛS hS) θ hθ _ _ (dualSp_selfDual T ΛT hT)
    (dualSp_selfDual S ΛS hS) η hη _ _ (swap_fin ψ S T ΛS ΛT hS hT hf) (swap_inf ψ S T ΛS ΛT hS hT hθ hi) γ' hγ' _
    (theta_trF' ψ S T ΛS ΛT hS hT hth)
  rw [swapOm_apply, swapOm_apply, map_one] at this
  exact this

end GlobalTheory.DualSwap

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaDistribution_automorphy_source_group : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ η, IsEtaTilde D η → ∀ (of oi : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsFinWeil ψ S T ΛS ΛT (η ^ S.rank) (η ^ T.rank) of → IsInfWeil ψ θ S T oi → ∀ γ ∈ GQ S, ∀ f, IsThetaFunO ψ S T f → of (γ, 1) (oi (γ, 1) f) 0 = f 0 := by
  first | exact @GlobalTheory.DualSwap.automorphy_source | exact GlobalTheory.DualSwap.automorphy_source | (intros; apply GlobalTheory.DualSwap.automorphy_source <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilProduct

open GlobalTheory.FinWeilO

variable {D : D7}

theorem isHeckeChar_pow {η : (AE D)ˣ →* Circle} (h : IsHeckeChar D η) (n : ℕ) : IsHeckeChar D (η ^ n) :=
  ⟨h.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.2 x, one_pow]⟩

theorem resEta_pow {η : (AE D)ˣ →* Circle} (h : ResEta D η 1) (n : ℕ) : ResEta D (η ^ n) n :=
  ⟨h.1, fun e he a => by rw [MonoidHom.pow_apply, h.2 e he a, pow_one]⟩

theorem mem_GfC_of_supp {a : AE D} (ha : infPart D a = 0) {V : HSp D} {g : GA D V}
    (hg : ∀ i j, a * (mt V g - 1) i j = (mt V g - 1) i j) : g ∈ GfC V := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPart D ((mt V g - 1) i j) = 0 := by
    rw [← hg i j, RingHom.map_mul, ha, zero_mul]
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  show infPart D (mt V g i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one]
  · rw [RingHom.map_zero]

theorem infPart_placeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
  obtain ⟨α, rfl, -⟩ := h
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 0 α ⊗ₜ 1) = 0
  rw [Algebra.TensorProduct.map_tmul, show fstA D.host.F (pairA D.host.F 0 α) = 0 from rfl, TensorProduct.zero_tmul]

theorem mem_GfC_of_suppAt {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V} (hg : SuppAt e V g) : g ∈ GfC V := by
  obtain ⟨-, -, v, ε, h1, h2⟩ := he
  exact mem_GfC_of_supp (h2 ▸ infPart_placeIdem h1) hg

theorem exists_weilDatum_etaTilde : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ η, IsEtaTilde D η → ∃ om, IsWeilDatumO ψ S T (η ^ S.rank) (η ^ T.rank) om ∧ (∀ v ε, NonSplitAt D v ε → FixesVacAt ψ S T ΛS ΛT om v ε) ∧ VacCharPlus ψ θ S T om := by
  intro D ψ hψ S T θ hθ ΛS ΛT hS hT η hη
  obtain ⟨of, hf⟩ := exists_isFinWeil D ψ hψ S T ΛS ΛT hS hT _ _ (isHeckeChar_pow hη.1 S.rank)
    (isHeckeChar_pow hη.1 T.rank) (resEta_pow hη.2.2.1 _) (resEta_pow hη.2.2.1 _)
  obtain ⟨oi, hi⟩ := GlobalTheory.RealWeil.exists_isInfWeil D ψ hψ θ hθ S T
  have hcomm := fun p q f h1 => fin_inf_comm hψ hS hT hf hi p q (f := f) h1
  obtain ⟨om, hom⟩ := exists_extend (thetaSub ψ S T)
    ({ toFun := fun p => (of p * oi p).restrict fun f h1 => hf.pres p _ (hi.pres p f h1)
       map_one' := LinearMap.ext fun f => Subtype.ext (by
         show of 1 (oi 1 f) = f
         rw [map_one, map_one]; rfl)
       map_mul' := fun p q => LinearMap.ext fun f => Subtype.ext (by
         show of (p * q) (oi (p * q) f) = of p (oi p (of q (oi q f)))
         rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hcomm q p _ (hi.pres q _ f.2)]) } :
      GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T))
  have ho : ∀ p f, IsThetaFunO ψ S T f → om p f = of p (oi p f) := fun p f h1 => hom p ⟨f, h1⟩
  have hp : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om p f) := fun p f h1 => by
    rw [ho p f h1]
    exact hf.pres p _ (hi.pres p f h1)
  have hfin : ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ f, IsThetaFunO ψ S T f → om (g, h) f = of (g, h) f := fun g hg h hh f h1 => by
    rw [ho _ f h1, hi.triv g hg h hh f h1]
  have hinf : ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, ∀ f, IsThetaFunO ψ S T f → om (g, h) f = oi (g, h) f :=
    fun g hg h hh f h1 => by rw [ho _ f h1, hf.triv g hg h hh _ (hi.pres _ f h1)]
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  refine ⟨om, ⟨hψ, isHeckeChar_pow hη.1 _, isHeckeChar_pow hη.1 _, resEta_pow hη.2.2.1 _, resEta_pow hη.2.2.1 _, hp,
    fun g h u f h1 => ?_, fun γ hγ γ' hγ' f h1 => ?_, fun f h1 u => ?_, fun μ 𝓕 hμ h𝓕 p f h1 => ?_,
    fun e he g h hg hh x y hx hy => ?_⟩, fun v ε hv g h hg hh hst f h1 hfix => ?_,
    fun sS sT cS cT g hg h hh kS kT f h1 hv => ?_⟩
  · obtain ⟨a, ha, b, hb, k, hk, l, hl, e, -⟩ := exists_parts (g, h)
    obtain ⟨rfl, rfl⟩ : g = a * k ∧ h = b * l := Prod.ext_iff.1 e
    rw [actO_mul, e, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfin k hk l hl _ (hth u f h1),
      hf.Heisenberg₂ k hk l hl u f h1, hfin k hk l hl f h1, hinf a ha b hb _ (hth _ _ (hf.pres _ f h1)),
      hi.Heisenberg₂ a ha b hb _ _ (hf.pres _ f h1), hinf a ha b hb _ (hf.pres _ f h1)]
  · rw [show ((γ, γ') : GA D S × GA D T) = (γ, 1) * (1, γ') by simp, map_mul, Module.End.mul_apply,
      ho _ _ (hp _ f h1), GlobalTheory.T.thetaDistribution_automorphy_source_group D ψ hψ S T θ hθ ΛS ΛT hS hT η hη of oi hf hi γ hγ _ (hp _ f h1), ho _ f h1]
    exact GlobalTheory.T.thetaDistribution_invariant_rationalTarget D ψ hψ S T θ hθ ΛS ΛT hS hT η hη of oi hf hi γ' hγ' f h1
  · simp only [ho _ f h1]
    exact continuous_product hψ hS hT hf hi h1 u
  · rw [ho p f h1, hf.unit μ 𝓕 hμ h𝓕 p _ (hi.pres p f h1), hi.unit μ 𝓕 hμ h𝓕 p f h1]
  · obtain ⟨r, hr, h2⟩ := hf.split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ f h1 => ?_⟩
    rw [hfin g (mem_GfC_of_suppAt he hg) h (mem_GfC_of_suppAt he hh) f h1]
    exact h2 ℓ hℓ f h1
  · rw [hfin g (mem_GfC_of_supp (infPart_placeIdem hv.1) hg) h (mem_GfC_of_supp (infPart_placeIdem hv.1) hh) f h1]
    exact hf.inert v ε hv g h hg hh hst f h1 hfix
  · rw [hinf g hg h hh f h1]
    exact hi.vac sS sT cS cT g hg h hh kS kT f h1 hv

end GlobalTheory.WeilProduct

end
end
