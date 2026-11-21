import Formalism.LocalToGlobal.GlobalTheory.GL4.PLinks
import Formalism.GL3MeanSquares.HookFormulaTorsion.FibreCardinalityOfModuliMap
import Formalism.LocalToGlobal.GlobalTheory.GL4.PFrGen
import Formalism.GL3MeanSquares.HookFormulaTorsion.HadamardUnitDiagonalDetLeOne

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions NumberField Formalism.MainNotions.flipTwoThree

section Frames

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def mulDual (S : HSpace E) (M : ℕ) (L : Submodule (𝓞 E) S.V) : AddSubgroup S.V :=
  (dualSub S L).map (DistribSMul.toAddMonoidHom S.V (M : E))

def IsoLat (S : HSpace E) (L L' : Submodule (𝓞 E) S.V) : Prop :=
  ∃ γ : S.V ≃ₗ[E] S.V, (∀ x y, S.hT (γ x) (γ y) = S.hT x y) ∧ ∀ x, x ∈ L ↔ γ x ∈ L'

theorem mem_dualSub (S : HSpace E) (L : Submodule (𝓞 E) S.V) (x : S.V) :
    x ∈ dualSub S L ↔ ∀ y ∈ L, S.hT y x ∈ (algebraMap (𝓞 E) E).range := Iff.rfl

theorem dual_map_of_isom (S : HSpace E) {L L' : Submodule (𝓞 E) S.V} (γ : S.V ≃ₗ[E] S.V)
    (hγ : ∀ x y, S.hT (γ x) (γ y) = S.hT x y) (hL : ∀ x, x ∈ L ↔ γ x ∈ L') {x : S.V}
    (hx : x ∈ dualSub S L) : γ x ∈ dualSub S L' := by
  rw [mem_dualSub] at hx ⊢
  intro y hy
  have h1 : γ.symm y ∈ L := (hL _).2 (by simpa using hy)
  have h2 := hx _ h1
  rwa [← hγ, LinearEquiv.apply_symm_apply] at h2

theorem isom_symm (S : HSpace E) (γ : S.V ≃ₗ[E] S.V) (hγ : ∀ x y, S.hT (γ x) (γ y) = S.hT x y) :
    ∀ x y, S.hT (γ.symm x) (γ.symm y) = S.hT x y := by
  intro x y
  rw [← hγ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem card_le_of_frames (S : HSpace E) (M n : ℕ) {ι : Type} [Fintype ι]
    (L : ι → Submodule (𝓞 E) S.V) (e : ι → Fin n → S.V)
    (he : ∀ c a, e c a ∈ dualSub S (L c))
    (hsep : ∀ c c', SameCls S M (L c) (L c') (e c) (e c') → c = c')
    (R : Finset ι) (hR : ∀ c, ∃ r ∈ R, IsoLat S (L c) (L r)) (Q : ℕ)
    (hQ : ∀ r ∈ R, (mulDual S M (L r)).relIndex (dualSub S (L r)) ≠ 0 ∧
      (mulDual S M (L r)).relIndex (dualSub S (L r)) ≤ Q) :
    Fintype.card ι ≤ R.card * Q ^ n := by
  classical
  choose ρ hρR hρ using hR
  choose γ hγi hγL using hρ
  have hfib : ∀ r ∈ R, (Finset.univ.filter (fun c => ρ c = r)).card ≤ Q ^ n := by
    intro r hr
    obtain ⟨h0, hle⟩ := hQ r hr
    set K := dualSub S (L r) with hK
    set H := (mulDual S M (L r)).addSubgroupOf K with hH
    have : H.FiniteIndex := ⟨h0⟩
    have : Finite (K ⧸ H) := AddSubgroup.finite_quotient_of_finiteIndex
    have hm : ∀ (c : {c // ρ c = r}) (a : Fin n), γ c.1 (e c.1 a) ∈ K := fun c a => by
      have := dual_map_of_isom S (γ c.1) (hγi c.1) (hγL c.1) (he c.1 a)
      rw [c.2] at this
      exact this
    let g : {c // ρ c = r} → (Fin n → K ⧸ H) := fun c a => ((⟨γ c.1 (e c.1 a), hm c a⟩ : K) : K ⧸ H)
    have hg : Function.Injective g := by
      intro c c' hcc
      apply Subtype.ext
      apply hsep c.1 c'.1
      refine ⟨(γ c.1).trans (γ c'.1).symm, fun x y => ?_, fun x => ?_, fun a => ?_⟩
      · simp only [LinearEquiv.trans_apply]
        rw [isom_symm S _ (hγi c'.1), hγi c.1]
      · rw [hγL c.1 x, hγL c'.1 (((γ c.1).trans (γ c'.1).symm) x), LinearEquiv.trans_apply,
          LinearEquiv.apply_symm_apply, c.2, c'.2]
      · have h1 := congrFun hcc a
        simp only [g] at h1
        rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
        obtain ⟨z0, hz0, hz⟩ := AddSubgroup.mem_map.1 h1
        simp only [DistribSMul.toAddMonoidHom_apply, AddSubgroup.coe_add, AddSubgroup.coe_neg] at hz
        have hLs : ∀ x, x ∈ L r ↔ (γ c'.1).symm x ∈ L c'.1 := fun x => by
          rw [hγL c'.1 ((γ c'.1).symm x), LinearEquiv.apply_symm_apply, c'.2]
        refine ⟨(γ c'.1).symm (-z0), dual_map_of_isom S (γ c'.1).symm (isom_symm S _ (hγi c'.1)) hLs
          (neg_mem hz0), ?_⟩
        have h2 : (M : E) • (-z0) = γ c.1 (e c.1 a) - γ c'.1 (e c'.1 a) := by
          rw [smul_neg, hz]
          abel
        rw [← LinearEquiv.map_smul, h2, map_sub, LinearEquiv.symm_apply_apply,
          LinearEquiv.trans_apply]
    have hc := Nat.card_le_card_of_injective g hg
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at hc
    have hKH : Nat.card (K ⧸ H) ≤ Q := hle
    have hpow : Nat.card (K ⧸ H) ^ n ≤ Q ^ n := Nat.pow_le_pow_left hKH n
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
    exact hc.trans hpow
  calc Fintype.card ι = (Finset.univ : Finset ι).card := Finset.card_univ.symm
    _ = ∑ r ∈ R, (Finset.univ.filter (fun c => ρ c = r)).card :=
        Finset.card_eq_sum_card_fiberwise (fun c _ => hρR c)
    _ ≤ ∑ _r ∈ R, Q ^ n := Finset.sum_le_sum hfib
    _ = R.card * Q ^ n := by rw [Finset.sum_const, smul_eq_mul]

end Frames

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions NumberField Formalism.MainNotions.flipTwoThree

section Count

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def msLat (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * (2 * D.R.f * Real.log (C₀ * (C₀ * D.R.f * (n : ℝ) ^ 2 * D.host.v ^ 2 * (Tu D u : ℝ) ^ 2))) +
    4 * D.R.f * n * ((n : ℝ) + 1) * (Real.log (C₀ * D.R.f * (n : ℝ) ^ 2 * D.host.v ^ 2 * (Tu D u : ℝ) ^ 2) / 2)

theorem msBound_eq (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (n : ℕ) :
    msBound D u C₀ n = msLat D u C₀ n +
      2 * D.R.f * (n : ℝ) ^ 2 * (Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1)) := rfl

def IsoCount (D : D7) (C₀ : ℝ) : Prop :=
  ∀ u : D.what₂.Word,
    (∀ i ≤ D.R.m, ∀ (ι : Type) [Fintype ι] (L : ι → Submodule (𝓞 D.host.E) (D.sp.X i).V),
      (∀ c, Submodule.IsLattice D.host.E (L c) ∧ LatT (D.sp.X i) (Tu D u ^ (2 * D.R.f)) (L c)) →
      ∃ R : Finset ι, (∀ c, ∃ r ∈ R, IsoLat (D.sp.X i) (L c) (L r)) ∧
        Real.log R.card ≤ msLat D u C₀ (D.R.N i)) ∧
    ∀ (ι : Type) [Fintype ι] (L : ι → Submodule (𝓞 D.host.E) D.sp.X'.V),
      (∀ c, Submodule.IsLattice D.host.E (L c) ∧ LatT D.sp.X' 1 (L c)) →
      ∃ R : Finset ι, (∀ c, ∃ r ∈ R, IsoLat D.sp.X' (L c) (L r)) ∧
        Real.log R.card ≤ msLat D u C₀ (D.R.N D.R.m - 1)

def DualIdx (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (M : ℕ), 0 < M →
    (∀ i ≤ D.R.m, ∀ L : Submodule (𝓞 D.host.E) (D.sp.X i).V, Submodule.IsLattice D.host.E L →
      LatT (D.sp.X i) (Tu D u ^ (2 * D.R.f)) L →
      (mulDual (D.sp.X i) M L).relIndex (dualSub (D.sp.X i) L) = M ^ (2 * D.R.f * D.R.N i)) ∧
    ∀ L : Submodule (𝓞 D.host.E) D.sp.X'.V, Submodule.IsLattice D.host.E L → LatT D.sp.X' 1 L →
      (mulDual D.sp.X' M L).relIndex (dualSub D.sp.X' L) = M ^ (2 * D.R.f * (D.R.N D.R.m - 1))

theorem two_le_rdE' (D : D7) : 2 ≤ D.host.rdE := by
  have h := (Formalism.BasicNotions.factRd D.R D.host).2.2
  have hf : (2 : ℝ) ≤ D.R.f := by
    have : 2 ≤ D.R.f := Nat.le_mul_of_pos_right 2 D.R.ord_pos
    exact_mod_cast this
  have h0 : 0 ≤ D.host.rdE := by
    refine le_trans ?_ (Formalism.BasicNotions.factRd D.R D.host).1
    positivity
  nlinarith

theorem one_le_hostv (D : D7) : 1 ≤ D.host.v := by
  have := two_le_rdE' D
  show 1 ≤ D.host.rdE / 2
  linarith

theorem one_le_f (D : D7) : 1 ≤ D.R.f := by
  exact Nat.mul_pos two_pos D.R.ord_pos

theorem msLat_nonneg (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (hC : 1 ≤ C₀) (n : ℕ) : 0 ≤ msLat D u C₀ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [msLat]
  have hv : 1 ≤ D.host.v := one_le_hostv D
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast one_le_f D
  have hT : (1 : ℝ) ≤ (Tu D u : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.one_lt.le
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 ≤ C₀ * D.R.f * (n : ℝ) ^ 2 * D.host.v ^ 2 * (Tu D u : ℝ) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hC hf) (one_le_pow₀ hn1)) (one_le_pow₀ hv)) (one_le_pow₀ hT)
  have h2 : 1 ≤ C₀ * (C₀ * D.R.f * (n : ℝ) ^ 2 * D.host.v ^ 2 * (Tu D u : ℝ) ^ 2) :=
    one_le_mul_of_one_le_of_one_le hC h1
  have l1 := Real.log_nonneg h1
  have l2 := Real.log_nonneg h2
  unfold msLat
  exact add_nonneg (mul_nonneg (by positivity) (mul_nonneg (by positivity) l2))
    (mul_nonneg (by positivity) (div_nonneg l1 (by norm_num)))

theorem log_card_le {K Rc Q n : ℕ} (hK : K ≤ Rc * Q ^ n) (hQ : 1 ≤ Q) (B : ℝ) (hR : Real.log Rc ≤ B)
    (hB : 0 ≤ B + n * Real.log Q) : Real.log K ≤ B + n * Real.log Q := by
  rcases Nat.eq_zero_or_pos K with h | h
  · rw [h, Nat.cast_zero, Real.log_zero]; exact hB
  have hRc : 0 < Rc := by
    rcases Nat.eq_zero_or_pos Rc with h' | h'
    · rw [h', zero_mul] at hK; omega
    · exact h'
  have hK' : (K : ℝ) ≤ (Rc : ℝ) * (Q : ℝ) ^ n := by exact_mod_cast hK
  have hpos : (0 : ℝ) < K := by exact_mod_cast h
  have hRc' : (0 : ℝ) < Rc := by exact_mod_cast hRc
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  calc Real.log K ≤ Real.log ((Rc : ℝ) * (Q : ℝ) ^ n) := Real.log_le_log hpos hK'
    _ = Real.log Rc + n * Real.log Q := by
        rw [Real.log_mul hRc'.ne' (pow_pos hQ' n).ne', Real.log_pow]
    _ ≤ B + n * Real.log Q := by linarith

theorem msCount_of (D : D7) (C₀ : ℝ) (hC : 1 ≤ C₀) (hI : IsoCount D C₀) (hQ : DualIdx D) : MsCount D C₀ := by
  intro u hT
  have hM0 : 0 < Tu D u * D.host.g 0 * D.host.g 1 := by
    have := (D.mem u).A.T_prime.pos; have := (D.host.g_prime 0).pos; have := (D.host.g_prime 1).pos
    positivity
  have hlogM : Real.log ((Tu D u * D.host.g 0 * D.host.g 1 : ℕ) : ℝ) =
      Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1) := by
    have := (D.mem u).A.T_prime.pos; have := (D.host.g_prime 0).pos; have := (D.host.g_prime 1).pos
    push_cast
    rw [mul_assoc, Real.log_mul (by positivity) (by positivity)]
  have hlg : 0 ≤ Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1) := by
    rw [← hlogM]; exact Real.log_nonneg (by exact_mod_cast hM0)
  have key : ∀ (n K Rc : ℕ), K ≤ Rc * ((Tu D u * D.host.g 0 * D.host.g 1) ^ (2 * D.R.f * n)) ^ n →
      Real.log Rc ≤ msLat D u C₀ n → Real.log K ≤ msBound D u C₀ n := by
    intro n K Rc hK hR
    have hQ1 : 1 ≤ (Tu D u * D.host.g 0 * D.host.g 1) ^ (2 * D.R.f * n) := Nat.one_le_pow _ _ hM0
    have hlogQ : (n : ℝ) * Real.log (((Tu D u * D.host.g 0 * D.host.g 1) ^ (2 * D.R.f * n) : ℕ) : ℝ) =
        2 * D.R.f * (n : ℝ) ^ 2 * (Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1)) := by
      rw [Nat.cast_pow, Real.log_pow, hlogM]; push_cast; ring
    have hB := log_card_le hK hQ1 _ hR (by
      rw [hlogQ]; exact add_nonneg (msLat_nonneg D u C₀ hC n) (mul_nonneg (by positivity) hlg))
    rw [hlogQ] at hB
    rw [msBound_eq]; exact hB
  refine ⟨fun i hi => ?_, ?_⟩
  · obtain ⟨hLat, e, he, hsep⟩ := hT.1 i hi
    obtain ⟨R, hR, hlog⟩ := (hI u).1 i hi _ (D.clsLat u i) (fun c => ⟨D.clsLat_lat u i c, hLat c⟩)
    refine key _ _ R.card ?_ hlog
    refine card_le_of_frames (D.sp.X i) _ (D.R.N i) (D.clsLat u i) e he hsep R hR _ (fun r _ => ?_)
    rw [(hQ u _ hM0).1 i hi _ (D.clsLat_lat u i r) (hLat r)]
    exact ⟨pow_ne_zero _ hM0.ne', le_rfl⟩
  · obtain ⟨LP, hLP, e, he, hsep⟩ := hT.2
    obtain ⟨R, hR, hlog⟩ := (hI u).2 _ LP hLP
    refine key _ _ R.card ?_ hlog
    refine card_le_of_frames D.sp.X' _ _ LP e he hsep R hR _ (fun r _ => ?_)
    rw [(hQ u _ hM0).2 _ (hLP r).1 (hLP r).2]
    exact ⟨pow_ne_zero _ hM0.ne', le_rfl⟩

end Count

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions NumberField Formalism.MainNotions.flipTwoThree

section DualIndex

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem mulDual_eq_nsmul (S : HSpace E) (M : ℕ) (L : Submodule (𝓞 E) S.V) :
    mulDual S M L = (dualSub S L).map (nsmulAddMonoidHom (α := S.V) M) := by
  unfold mulDual
  congr 1
  ext v
  simp [Nat.cast_smul_eq_nsmul]

abbrev qModule (S : HSpace E) : Module ℚ S.V := Module.compHom S.V (algebraMap ℚ E)

theorem qsmul_def (S : HSpace E) (q : ℚ) (v : S.V) :
    letI := qModule S; q • v = (algebraMap ℚ E q) • v := rfl

theorem span_rat_eq_top (S : HSpace E) (L : Submodule (𝓞 E) S.V) [hL : Submodule.IsLattice E L] :
    letI := qModule S; Submodule.span ℚ (L : Set S.V) = ⊤ := by
  let _ := qModule S
  set W := Submodule.span ℚ (L : Set S.V) with hW
  have key : ∀ (e : E) (v : S.V), v ∈ W → e • v ∈ W := by
    intro e v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy0, hy⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) e)).exists_integral_multiple
      set a : 𝓞 E := ⟨y • e, hy⟩ with ha
      have hax : a • x ∈ L := L.smul_mem a hx
      have h1 : e • x = (((y : ℚ)⁻¹ : ℚ)) • (a • x) := by
        rw [qsmul_def, ← algebraMap_smul E a x, smul_smul]
        congr 1
        have hy' : (y : E) ≠ 0 := by exact_mod_cast hy0
        simp only [ha, zsmul_eq_mul, map_inv₀, map_intCast]
        field_simp
        rfl
      rw [h1]
      exact W.smul_mem _ (Submodule.subset_span hax)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact W.add_mem hx hy
    | smul q x _ hx =>
      have : e • (q • x) = q • (e • x) := by
        rw [qsmul_def, qsmul_def, smul_smul, smul_smul, mul_comm]
      rw [this]; exact W.smul_mem q hx
  let W' : Submodule E S.V :=
    { carrier := W
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := fun e v hv => key e v hv }
  have hle : Submodule.span E (L : Set S.V) ≤ W' := Submodule.span_le.2 fun x hx => Submodule.subset_span hx
  rw [hL.span_eq_top] at hle
  exact eq_top_iff.2 fun v _ => (hle (Submodule.mem_top : v ∈ (⊤ : Submodule E S.V)))

theorem relIndex_mulDual (S : HSpace E) (L : Submodule (𝓞 E) S.V) [hL : Submodule.IsLattice E L]
    (q : ℕ) (hq : LatT S q L) (hq0 : q ≠ 0) (M : ℕ) :
    (mulDual S M L).relIndex (dualSub S L) = M ^ (Module.finrank ℚ E * S.rank) := by
  let _ := qModule S
  have _tow : IsScalarTower ℚ E S.V := ⟨fun x y z => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  have _fin : Module.Finite ℚ S.V := Module.Finite.trans E S.V
  set A := dualSub S L with hA
  have hLA : L.restrictScalars ℤ ≤ A.toIntSubmodule := fun x hx => hq.1 x hx
  have hLfg : (L.restrictScalars ℤ).FG := hL.fg.restrictScalars
  have _hLl : Submodule.IsLattice ℚ (L.restrictScalars ℤ) :=
    ⟨hLfg, by
      have h := span_rat_eq_top S L
      simpa using h⟩

  let φ : S.V →ₗ[ℤ] S.V := (q : ℤ) • LinearMap.id
  have hφ : Function.Injective φ := by
    intro v w hvw
    have h1 : (q : ℤ) • (v - w) = 0 := by
      simp only [φ, LinearMap.smul_apply, LinearMap.id_apply] at hvw
      rw [smul_sub, hvw, sub_self]
    have h2 : ((q : E)) • (v - w) = 0 := by
      rw [← h1, ← Int.cast_smul_eq_zsmul E]; simp
    rcases smul_eq_zero.1 h2 with h | h
    · exact absurd h (by exact_mod_cast hq0)
    · exact sub_eq_zero.1 h
  have hmap : A.toIntSubmodule.map φ ≤ L.restrictScalars ℤ := by
    rintro _ ⟨a, ha, rfl⟩
    have h := AddSubgroup.nsmul_relIndex_mem L.toAddSubgroup (show a ∈ A from ha)
    rw [hq.2] at h
    simpa [φ, natCast_zsmul] using h
  have hAfg : A.toIntSubmodule.FG :=
    Submodule.fg_of_fg_map_injective φ hφ (Submodule.FG.of_le hLfg hmap)
  have _hAl : Submodule.IsLattice ℚ A.toIntSubmodule :=
    Submodule.IsLattice.of_le_of_isLattice_of_fg ℚ hLA hAfg
  have hrank : Module.finrank ℤ A.toIntSubmodule = Module.finrank ℚ E * S.rank := by
    apply Module.finrank_eq_of_rank_eq
    rw [Submodule.IsLattice.rank' ℚ A.toIntSubmodule, ← Module.finrank_eq_rank ℚ S.V,
      ← Module.finrank_mul_finrank ℚ E S.V, S.rank_eq]
  rw [mulDual_eq_nsmul, AddSubgroup.relIndex_map_nsmul]
  rw [← hrank]
  rfl

end DualIndex

section DualIdxRecord

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem dual_index (D : D7) : DualIdx D := by
  intro u M _
  refine ⟨fun i hi L hL hT => ?_, fun L hL hT => ?_⟩
  · rw [relIndex_mulDual (D.sp.X i) L _ hT (pow_ne_zero _ (D.mem u).A.T_prime.ne_zero) M,
      Formalism.MainNotions.flipTwoThree.b_finrank_host, D.sp.X_rank i hi]
  · have hN : D.R.N D.R.m - 1 = D.R.rankX' := by
      have := Formalism.BasicNotions.factXm D.R
      omega
    rw [relIndex_mulDual D.sp.X' L 1 hT one_ne_zero M, Formalism.MainNotions.flipTwoThree.b_finrank_host, D.sp.X'_rank, hN]

theorem msCount_of_isoCount (D : D7) (C₀ : ℝ) (hC : 1 ≤ C₀) (hI : IsoCount D C₀) : MsCount D C₀ :=
  msCount_of D C₀ hC hI (dual_index D)

end DualIdxRecord

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions NumberField Formalism.MainNotions.flipTwoThree

section Keys

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def keyOf (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V) (L : Submodule (𝓞 E) S.V) :
    Matrix (Fin S.rank) (Fin S.rank) E × Submodule (𝓞 E) (Fin S.rank → E) :=
  (fun i j => S.hT (b i) (b j), L.map ((b.equivFun : S.V →ₗ[E] (Fin S.rank → E)).restrictScalars (𝓞 E)))

theorem equivFun_equiv (S : HSpace E) (b b' : Module.Basis (Fin S.rank) E S.V) (x : S.V) :
    b'.equivFun (b.equiv b' (Equiv.refl _) x) = b.equivFun x := by
  have h : (b'.equivFun.toLinearMap ∘ₗ (b.equiv b' (Equiv.refl _)).toLinearMap) = b.equivFun.toLinearMap := by
    refine b.ext fun i => ?_
    simp [Module.Basis.equiv_apply]
  exact LinearMap.congr_fun h x

theorem isoLat_of_key (S : HSpace E) (b b' : Module.Basis (Fin S.rank) E S.V) (L L' : Submodule (𝓞 E) S.V)
    (h : keyOf S b L = keyOf S b' L') : IsoLat S L L' := by
  obtain ⟨hG, hC⟩ := Prod.ext_iff.1 h
  set γ := b.equiv b' (Equiv.refl _) with hγ
  refine ⟨γ, fun x y => ?_, fun x => ?_⟩
  · have hB : (S.hT.compl₂ γ.toLinearMap).comp γ.toLinearMap = S.hT := by
      refine LinearMap.ext_basis b b fun i j => ?_
      have := congrFun (congrFun hG i) j
      simp only [keyOf] at this
      simp only [LinearMap.comp_apply, LinearMap.compl₂_apply, LinearEquiv.coe_coe, hγ,
        Module.Basis.equiv_apply, Equiv.refl_apply]
      exact this.symm
    have := LinearMap.congr_fun₂ hB x y
    simpa using this
  · have hfun := equivFun_equiv S b b' x
    constructor
    · intro hx
      have hm : b.equivFun x ∈ (keyOf S b L).2 := Submodule.mem_map_of_mem (f := _) hx
      rw [h] at hm
      obtain ⟨x', hx', hxe⟩ := Submodule.mem_map.1 hm
      have : x' = γ x := b'.equivFun.injective (by rw [hfun]; exact hxe)
      rw [← this]; exact hx'
    · intro hx
      have hm : b'.equivFun (γ x) ∈ (keyOf S b' L').2 := Submodule.mem_map_of_mem (f := _) hx
      rw [← h, hfun] at hm
      obtain ⟨x', hx', hxe⟩ := Submodule.mem_map.1 hm
      have : x' = x := b.equivFun.injective hxe
      rw [← this]; exact hx'

def KeyBound (S : HSpace E) (q : ℕ) (B : ℝ) : Prop :=
  ∃ K : Finset (Matrix (Fin S.rank) (Fin S.rank) E × Submodule (𝓞 E) (Fin S.rank → E)),
    Real.log K.card ≤ B ∧
    ∀ L : Submodule (𝓞 E) S.V, Submodule.IsLattice E L → LatT S q L →
      ∃ b : Module.Basis (Fin S.rank) E S.V, keyOf S b L ∈ K

theorem iso_reps_of_keyBound (S : HSpace E) (q : ℕ) (B : ℝ) (hK : KeyBound S q B) {ι : Type} [Fintype ι]
    (L : ι → Submodule (𝓞 E) S.V) (hL : ∀ c, Submodule.IsLattice E (L c) ∧ LatT S q (L c)) :
    ∃ R : Finset ι, (∀ c, ∃ r ∈ R, IsoLat S (L c) (L r)) ∧ Real.log R.card ≤ B := by
  classical
  obtain ⟨K, hKB, hKL⟩ := hK
  have hB : 0 ≤ B := le_trans (Real.log_natCast_nonneg _) hKB
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨∅, fun c => (IsEmpty.false c).elim, by simpa using hB⟩
  choose b hb using fun c => hKL (L c) (hL c).1 (hL c).2
  let k : ι → _ := fun c => keyOf S (b c) (L c)
  refine ⟨(Finset.univ.image k).image (Function.invFun k), fun c => ?_, ?_⟩
  · refine ⟨Function.invFun k (k c), Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ c)), ?_⟩
    exact isoLat_of_key S (b c) (b _) (L c) (L _) (Function.invFun_eq (f := k) ⟨c, rfl⟩).symm
  · have h1 : ((Finset.univ.image k).image (Function.invFun k)).card ≤ K.card := by
      refine le_trans Finset.card_image_le (Finset.card_le_card ?_)
      intro κ hκ
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hκ
      exact hb c
    rcases Nat.eq_zero_or_pos ((Finset.univ.image k).image (Function.invFun k)).card with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact hB
    · refine le_trans (Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast h1)) hKB

end Keys

section KeysRecord

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isoCount_of_keys (D : D7) (C₀ : ℝ)
    (h : ∀ u : D.what₂.Word,
      (∀ i ≤ D.R.m, KeyBound (D.sp.X i) (Tu D u ^ (2 * D.R.f)) (msLat D u C₀ (D.R.N i))) ∧
      KeyBound D.sp.X' 1 (msLat D u C₀ (D.R.N D.R.m - 1))) : IsoCount D C₀ := by
  intro u
  exact ⟨fun i hi ι _ L hL => iso_reps_of_keyBound _ _ _ ((h u).1 i hi) L hL,
    fun ι _ L hL => iso_reps_of_keyBound _ _ _ (h u).2 L hL⟩

theorem msCount_of_keys (D : D7) (C₀ : ℝ) (hC : 1 ≤ C₀)
    (h : ∀ u : D.what₂.Word,
      (∀ i ≤ D.R.m, KeyBound (D.sp.X i) (Tu D u ^ (2 * D.R.f)) (msLat D u C₀ (D.R.N i))) ∧
      KeyBound D.sp.X' 1 (msLat D u C₀ (D.R.N D.R.m - 1))) : MsCount D C₀ :=
  msCount_of_isoCount D C₀ hC (isoCount_of_keys D C₀ h)

end KeysRecord

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions NumberField Formalism.MainNotions.flipTwoThree

section Gram

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def meanAbs (z : E) : ℝ := (∑ φ : E →+* ℂ, ‖φ z‖) / (Module.finrank ℚ E : ℝ)

def ShortFrame (S : HSpace E) (q : ℕ) (ρ : ℝ) : Prop :=
  ∀ L : Submodule (𝓞 E) S.V, Submodule.IsLattice E L → LatT S q L →
    ∃ b : Module.Basis (Fin S.rank) E S.V, (∀ c, b c ∈ L) ∧ ∀ c, meanAbs (S.hT (b c) (b c)) ≤ ρ

def CSAt (S : HSpace E) : Prop :=
  ∀ (φ : E →+* ℂ) (x y : S.V), ‖φ (S.hT x y)‖ ^ 2 ≤ ‖φ (S.hT x x)‖ * ‖φ (S.hT y y)‖

def CoordCount (S : HSpace E) (q : ℕ) (ρ B2 : ℝ) : Prop :=
  ∃ C : Matrix (Fin S.rank) (Fin S.rank) E → Finset (Submodule (𝓞 E) (Fin S.rank → E)),
    (∀ G, ((C G).card : ℝ) ≤ Real.exp B2) ∧
    ∀ (L : Submodule (𝓞 E) S.V) (b : Module.Basis (Fin S.rank) E S.V), Submodule.IsLattice E L → LatT S q L →
      (∀ c, b c ∈ L) → (∀ c, meanAbs (S.hT (b c) (b c)) ≤ ρ) → (keyOf S b L).2 ∈ C (keyOf S b L).1

theorem meanAbs_entry (S : HSpace E) (hCS : CSAt S) {ρ : ℝ} {x y : S.V} (hx : meanAbs (S.hT x x) ≤ ρ)
    (hy : meanAbs (S.hT y y) ≤ ρ) : meanAbs (S.hT x y) ≤ ρ := by
  have hpt : ∀ φ : E →+* ℂ, ‖φ (S.hT x y)‖ ≤ (‖φ (S.hT x x)‖ + ‖φ (S.hT y y)‖) / 2 := by
    intro φ
    have h := hCS φ x y
    nlinarith [sq_nonneg (‖φ (S.hT x x)‖ - ‖φ (S.hT y y)‖), norm_nonneg (φ (S.hT x y)),
      norm_nonneg (φ (S.hT x x)), norm_nonneg (φ (S.hT y y))]
  unfold meanAbs at *
  have hd : (0 : ℝ) < (Module.finrank ℚ E : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  rw [div_le_iff₀ hd] at hx hy ⊢
  have hs := Finset.sum_le_sum fun φ (_ : φ ∈ (Finset.univ : Finset (E →+* ℂ))) => hpt φ
  rw [← Finset.sum_div, Finset.sum_add_distrib] at hs
  linarith

theorem keyBound_of (S : HSpace E) (q : ℕ) (ρ B2 : ℝ) (hρ : 0 ≤ ρ) (hB2 : 0 ≤ B2)
    (hS : ShortFrame S q ρ) (hCS : CSAt S) (hC : CoordCount S q ρ B2) :
    KeyBound S q ((S.rank : ℝ) ^ 2 * (Module.finrank ℚ E : ℝ) * Real.log (2 * ρ + 1) + B2) := by
  classical
  obtain ⟨hfin, hcard⟩ := Formalism.HermitianLattices.ExplicitEstimates.mean_count_of_moduli_space E ρ hρ
  obtain ⟨C, hCc, hCm⟩ := hC
  set Z : Finset E := hfin.toFinset.image (fun x : 𝓞 E => (x : E)) with hZ
  have hZc : (Z.card : ℝ) ≤ (2 * ρ + 1) ^ Module.finrank ℚ E := by
    refine le_trans ?_ hcard
    have : Z.card ≤ hfin.toFinset.card := Finset.card_image_le
    rw [← Set.ncard_eq_toFinset_card _ hfin] at this
    exact_mod_cast this
  let G : Finset (Matrix (Fin S.rank) (Fin S.rank) E) := Fintype.piFinset fun _ => Fintype.piFinset fun _ => Z
  have hGc : (G.card : ℝ) ≤ ((2 * ρ + 1) ^ Module.finrank ℚ E) ^ (S.rank * S.rank) := by
    have : G.card = (Z.card ^ S.rank) ^ S.rank := by
      show (Fintype.piFinset fun _ => Fintype.piFinset fun _ => Z : Finset (Fin S.rank → Fin S.rank → E)).card = _
      rw [Fintype.card_piFinset]
      simp [Fintype.card_piFinset, Finset.prod_const]
    rw [this, pow_mul]
    push_cast
    exact pow_le_pow_left₀ (pow_nonneg (by positivity) _) (pow_le_pow_left₀ (by positivity) hZc S.rank) S.rank
  let K := G.biUnion fun g => (C g).image fun c => (g, c)
  refine ⟨K, ?_, fun L hL hq => ?_⟩
  · have hK : (K.card : ℝ) ≤ G.card * Real.exp B2 := by
      have h1 : K.card ≤ ∑ g ∈ G, ((C g).image fun c => (g, c)).card := Finset.card_biUnion_le
      have h3 : K.card ≤ ∑ g ∈ G, (C g).card := h1.trans (Finset.sum_le_sum fun g _ => Finset.card_image_le)
      have h2 : (K.card : ℝ) ≤ ∑ g ∈ G, ((C g).card : ℝ) := by exact_mod_cast h3
      refine le_trans h2 ?_
      refine le_trans (Finset.sum_le_sum fun g _ => hCc g) ?_
      rw [Finset.sum_const, nsmul_eq_mul]
    have hlog : 0 ≤ Real.log (2 * ρ + 1) := Real.log_nonneg (by linarith)
    rcases Nat.eq_zero_or_pos K.card with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]; positivity
    have hGpos : (0 : ℝ) < G.card := by
      have : (0 : ℝ) < G.card * Real.exp B2 := lt_of_lt_of_le (by exact_mod_cast h0) hK
      exact pos_of_mul_pos_left this (Real.exp_pos _).le
    calc Real.log K.card ≤ Real.log (G.card * Real.exp B2) := Real.log_le_log (by exact_mod_cast h0) hK
      _ = Real.log G.card + B2 := by rw [Real.log_mul hGpos.ne' (Real.exp_pos _).ne', Real.log_exp]
      _ ≤ Real.log (((2 * ρ + 1) ^ Module.finrank ℚ E) ^ (S.rank * S.rank)) + B2 := by
          gcongr
      _ = (S.rank : ℝ) ^ 2 * (Module.finrank ℚ E : ℝ) * Real.log (2 * ρ + 1) + B2 := by
          rw [Real.log_pow, Real.log_pow]; push_cast; ring
  · obtain ⟨b, hbL, hbs⟩ := hS L hL hq
    refine ⟨b, Finset.mem_biUnion.2 ⟨(keyOf S b L).1, ?_, Finset.mem_image.2 ⟨(keyOf S b L).2,
      hCm L b hL hq hbL hbs, rfl⟩⟩⟩
    have key : ∀ i j, (keyOf S b L).1 i j ∈ Z := by
      intro i j
      have hmem := (mem_dualSub S L (b j)).1 (hq.1 _ (hbL j)) (b i) (hbL i)
      obtain ⟨z, hz⟩ := hmem
      have hzm : z ∈ hfin.toFinset := by
        rw [Set.Finite.mem_toFinset]
        show meanAbs (z : E) ≤ ρ
        have : (z : E) = S.hT (b i) (b j) := hz
        rw [this]
        exact meanAbs_entry S hCS (hbs i) (hbs j)
      exact Finset.mem_image.2 ⟨z, hzm, hz⟩
    exact Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.2 fun j => key i j

end Gram

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions NumberField Formalism.MainNotions.flipTwoThree

section Short

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem keyBound_mono (S : HSpace E) (q : ℕ) {B B' : ℝ} (h : KeyBound S q B) (hB : B ≤ B') : KeyBound S q B' := by
  obtain ⟨K, hK, hL⟩ := h
  exact ⟨K, hK.trans hB, hL⟩

end Short

section ShortRecord

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def radiusSq (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (n : ℕ) : ℝ :=
  C₀ * D.R.f * (n : ℝ) ^ 2 * D.host.v ^ 2 * (Tu D u : ℝ) ^ 2

def msRho (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (n : ℕ) : ℝ := radiusSq D u C₀ n

def coordinateLogBound (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (n : ℕ) : ℝ :=
  4 * D.R.f * n * ((n : ℝ) + 1) * (Real.log (radiusSq D u C₀ n) / 2)

def ShortAt (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (S : HSpace D.host.E) (q n : ℕ) : Prop :=
  ShortFrame S q (msRho D u C₀ n) ∧ CSAt S ∧ CoordCount S q (msRho D u C₀ n) (coordinateLogBound D u C₀ n)

theorem one_le_radius_sq (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (hC : 1 ≤ C₀) (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ radiusSq D u C₀ n := by
  have hv : 1 ≤ D.host.v := one_le_hostv D
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast one_le_f D
  have hT : (1 : ℝ) ≤ (Tu D u : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.one_lt.le
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hC hf) (one_le_pow₀ hn1)) (one_le_pow₀ hv)) (one_le_pow₀ hT)

theorem keyBound_of_shortAt (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (hC : 3 ≤ C₀) (S : HSpace D.host.E) (q n : ℕ)
    (hn : 1 ≤ n) (hr : S.rank = n) (h : ShortAt D u C₀ S q n) : KeyBound S q (msLat D u C₀ n) := by
  obtain ⟨hS, hCS, hCC⟩ := h
  have h1 := one_le_radius_sq D u C₀ (by linarith) n hn
  have hρ : 0 ≤ msRho D u C₀ n := by
    unfold msRho
    linarith
  have hB2 : 0 ≤ coordinateLogBound D u C₀ n := by
    unfold coordinateLogBound
    have := Real.log_nonneg h1
    positivity
  refine keyBound_mono S q (keyBound_of S q _ _ hρ hB2 hS hCS hCC) ?_
  rw [hr, Formalism.MainNotions.flipTwoThree.b_finrank_host]
  have hle : Real.log (2 * msRho D u C₀ n + 1) ≤ Real.log (C₀ * radiusSq D u C₀ n) := by
    unfold msRho
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * ((2 * D.R.f : ℕ) : ℝ) := by positivity
  have key := mul_le_mul_of_nonneg_left hle hn2
  unfold msLat coordinateLogBound
  unfold radiusSq at key ⊢
  push_cast at key ⊢
  linarith [key]

theorem msCount_of_short (D : D7) (C₀ : ℝ) (hC : 3 ≤ C₀)
    (h : ∀ u : D.what₂.Word,
      (∀ i ≤ D.R.m, ShortAt D u C₀ (D.sp.X i) (Tu D u ^ (2 * D.R.f)) (D.R.N i)) ∧
      ShortAt D u C₀ D.sp.X' 1 (D.R.N D.R.m - 1)) : MsCount D C₀ := by
  refine msCount_of_keys D C₀ (by linarith) fun u => ⟨fun i hi => ?_, ?_⟩
  · refine keyBound_of_shortAt D u C₀ hC _ _ _ ?_ (D.sp.X_rank i hi) ((h u).1 i hi)
    have := D.R.k_ge
    unfold Ranks.N
    omega
  · have hN : D.R.N D.R.m - 1 = D.R.rankX' := by
      have := Formalism.BasicNotions.factXm D.R
      omega
    refine keyBound_of_shortAt D u C₀ hC _ _ _ ?_ (by rw [D.sp.X'_rank, hN]) (h u).2
    rw [hN]
    unfold Ranks.rankX' Ranks.r
    have := D.R.k_ge
    omega

end ShortRecord

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Matrix

section CSMat

variable {ι : Type} [Fintype ι]

theorem cs_dot (u v : ι → ℂ) : ‖star u ⬝ᵥ v‖ ^ 2 ≤ ‖star u ⬝ᵥ u‖ * ‖star v ⬝ᵥ v‖ := by
  have hgen : ∀ a b : ι → ℂ, star a ⬝ᵥ b =
      inner ℂ (WithLp.toLp 2 a : EuclideanSpace ℂ ι) (WithLp.toLp 2 b : EuclideanSpace ℂ ι) := by
    intro a b
    simp [PiLp.inner_apply, dotProduct, mul_comm]
  rw [hgen u v, hgen u u, hgen v v, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  set x : EuclideanSpace ℂ ι := WithLp.toLp 2 u
  set y : EuclideanSpace ℂ ι := WithLp.toLp 2 v
  have h := norm_inner_le_norm (𝕜 := ℂ) x y
  simp only [norm_pow, RCLike.norm_ofReal, abs_norm, Complex.norm_real, norm_norm]
  calc _ ≤ (‖x‖ * ‖y‖) ^ 2 := by gcongr
    _ = _ := by ring

theorem cs_factor (Q : Matrix ι ι ℂ) (s : ℂ) (hs : ‖s‖ = 1) (a b : ι → ℂ) :
    ‖star a ⬝ᵥ (s • (Qᴴ * Q)) *ᵥ b‖ ^ 2 ≤
      ‖star a ⬝ᵥ (s • (Qᴴ * Q)) *ᵥ a‖ * ‖star b ⬝ᵥ (s • (Qᴴ * Q)) *ᵥ b‖ := by
  have key : ∀ x y : ι → ℂ,
      star x ⬝ᵥ (s • (Qᴴ * Q)) *ᵥ y = s * (star (Q *ᵥ x) ⬝ᵥ (Q *ᵥ y)) := by
    intro x y
    rw [smul_mulVec, dotProduct_smul, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec,
      smul_eq_mul]
  simp only [key, norm_mul, hs, one_mul]
  exact cs_dot _ _

end CSMat

theorem cT_eq_conjTranspose {m p : Type} (M : Matrix m p ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [Formalism.UG.cT, conjTranspose_apply]

theorem factor_of_sig {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (p q : ℕ) (h : Formalism.UG.HasSignature G p q)
    (hpq : q = 0 ∨ p = 0) :
    ∃ (e : Fin n ≃ Fin p ⊕ Fin q) (Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (s : ℂ),
      ‖s‖ = 1 ∧ G.reindex e e = s • (Qᴴ * Q) := by
  obtain ⟨e, P, hP⟩ := h
  rw [cT_eq_conjTranspose] at hP
  have h1 : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *
      ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ = 1 := by
    rw [← conjTranspose_mul, h1, conjTranspose_one]
  have hM : G.reindex e e = ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ *
      Formalism.UG.Jpq p q * ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := by
    rw [← hP]
    calc G.reindex e e = (((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ *
          (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ) * G.reindex e e *
          ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *
            ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) := by
          rw [h2, h1, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  rcases hpq with rfl | rfl
  · refine ⟨e, ((P⁻¹ : GL (Fin p ⊕ Fin 0) ℂ) : Matrix (Fin p ⊕ Fin 0) (Fin p ⊕ Fin 0) ℂ), 1, by simp, ?_⟩
    have hJ : Formalism.UG.Jpq p 0 = 1 := by
      ext (i | i) (j | j)
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
      · exact i.elim0
      · exact i.elim0
    rw [hM, hJ, Matrix.mul_one, one_smul]
  · refine ⟨e, ((P⁻¹ : GL (Fin 0 ⊕ Fin q) ℂ) : Matrix (Fin 0 ⊕ Fin q) (Fin 0 ⊕ Fin q) ℂ), -1, by simp, ?_⟩
    have hJ : Formalism.UG.Jpq 0 q = -1 := by
      ext (i | i) (j | j)
      · exact i.elim0
      · exact i.elim0
      · exact j.elim0
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
    rw [hM, hJ, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, neg_one_smul]

section CSSpace

open Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem hT_expand (S : HSpace E) (x y : S.V) :
    S.hT x y = ∑ i, ∑ j, star (S.frame.repr x i) * (S.gram i j * S.frame.repr y j) := by
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
    smul_eq_mul, starRingEnd_apply, HSpace.gram, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem phi_hT (S : HSpace E) (φ : E →+* ℂ) (hstar : ∀ a, φ (star a) = star (φ a)) (x y : S.V) :
    φ (S.hT x y) = star (fun i => φ (S.frame.repr x i)) ⬝ᵥ (S.gram.map φ) *ᵥ (fun j => φ (S.frame.repr y j)) := by
  rw [hT_expand]
  simp only [dotProduct, mulVec, Matrix.map_apply, Pi.star_apply, map_sum, map_mul, hstar,
    Finset.mul_sum]

theorem dot_reindex {m ι : Type} [Fintype m] [Fintype ι] (e : m ≃ ι) (G : Matrix m m ℂ) (a b : m → ℂ) :
    star (a ∘ e.symm) ⬝ᵥ (G.reindex e e) *ᵥ (b ∘ e.symm) = star a ⬝ᵥ G *ᵥ b := by
  rw [reindex_apply, submatrix_mulVec_equiv]
  have hb : (b ∘ e.symm) ∘ e.symm.symm = b := by
    funext x
    simp
  rw [hb]
  simp only [dotProduct, Function.comp_apply, Pi.star_apply]
  exact Equiv.sum_comp e.symm (fun i => star (a i) * (G *ᵥ b) i)

theorem csAt_of_definite (S : HSpace E) (hstar : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (hsig : S.SigOK)
    (hdef : S.IsDefinite) : CSAt S := by
  intro φ x y
  obtain ⟨e, Q, s, hs, hG⟩ := factor_of_sig (S.gram.map φ) (S.sig φ).1 (S.sig φ).2 (hsig φ)
    (by rcases hdef φ with h | h <;> simp [h])
  simp only [phi_hT S φ (hstar φ)]
  rw [← dot_reindex e, ← dot_reindex e, ← dot_reindex e, hG]
  exact cs_factor Q s hs _ _

theorem csAt_of_isomEmb (S S' : HSpace E) (ι : S.V →ₗ[E] S'.V) (hι : HSpace.IsIsomEmb S S' ι) (h : CSAt S') :
    CSAt S := by
  intro φ x y
  rw [← hι x y, ← hι x x, ← hι y y]
  exact h φ (ι x) (ι y)

end CSSpace

section CSRecord

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem host_star (D : D7) (φ : D.host.E →+* ℂ) (a : D.host.E) : φ (star a) = star (φ a) := by
  exact @NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ _ D.host.isCMField_hostE _ φ a

theorem csAt_X (D : D7) (i : ℕ) (hi : i ≤ D.R.m) : CSAt (D.sp.X i) :=
  csAt_of_definite (D.sp.X i) (host_star D) (D.sp.X_sig i) (D.sp.X_def i hi)

theorem csAt_X' (D : D7) : CSAt D.sp.X' :=
  csAt_of_isomEmb D.sp.X' (D.sp.X D.R.m) D.sp.iX' D.sp.iX'_isom (csAt_X D D.R.m le_rfl)

def FrameCoordAt (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (S : HSpace D.host.E) (q n : ℕ) : Prop :=
  ShortFrame S q (msRho D u C₀ n) ∧ CoordCount S q (msRho D u C₀ n) (coordinateLogBound D u C₀ n)

theorem msCount_of_frames (D : D7) (C₀ : ℝ) (hC : 3 ≤ C₀)
    (h : ∀ u : D.what₂.Word,
      (∀ i ≤ D.R.m, FrameCoordAt D u C₀ (D.sp.X i) (Tu D u ^ (2 * D.R.f)) (D.R.N i)) ∧
      FrameCoordAt D u C₀ D.sp.X' 1 (D.R.N D.R.m - 1)) : MsCount D C₀ :=
  msCount_of_short D C₀ hC fun u =>
    ⟨fun i hi => ⟨((h u).1 i hi).1, csAt_X D i hi, ((h u).1 i hi).2⟩, ⟨(h u).2.1, csAt_X' D, (h u).2.2⟩⟩


end CSRecord

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc

variable {E : Type} [Field E] [NumberField E]

def incl (n : ℕ) : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → E) := (Algebra.linearMap (𝓞 E) E).compLeft (Fin n)

theorem incl_apply (n : ℕ) (m : Fin n → 𝓞 E) (i : Fin n) : incl n m i = (m i : E) := rfl

theorem incl_injective (n : ℕ) : Function.Injective (incl (E := E) n) := by
  intro a b h
  funext i
  exact RingOfIntegers.coe_injective (congrFun h i)

def psi {n : ℕ} (G : Matrix (Fin n) (Fin n) E) : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → E) :=
  ((Matrix.mulVecLin G⁻¹).restrictScalars (𝓞 E)).comp (incl n)

theorem psi_apply {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (m : Fin n → 𝓞 E) : psi G m = G⁻¹ *ᵥ incl n m := rfl

theorem incl_mulVec {n : ℕ} (Gm : Matrix (Fin n) (Fin n) (𝓞 E)) (m : Fin n → 𝓞 E) :
    incl n (Gm *ᵥ m) = (Gm.map ((↑) : 𝓞 E → E)) *ᵥ incl n m := by
  funext i
  rw [incl_apply]
  exact (RingHom.map_mulVec (algebraMap (𝓞 E) E) Gm m i)

theorem psi_mulVec {n : ℕ} (Gm : Matrix (Fin n) (Fin n) (𝓞 E)) (hdet : (Gm.map ((↑) : 𝓞 E → E)).det ≠ 0)
    (m : Fin n → 𝓞 E) : psi (Gm.map ((↑) : 𝓞 E → E)) (Gm *ᵥ m) = incl n m := by
  rw [psi_apply, incl_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
    Matrix.one_mulVec]

theorem psi_injective {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (hdet : G.det ≠ 0) : Function.Injective (psi G) := by
  intro a b h
  apply incl_injective n
  have := congrArg (fun z ↦ G *ᵥ z) h
  simp only [psi_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet),
    Matrix.one_mulVec] at this
  exact this

theorem det_map_ne {n : ℕ} (Gm : Matrix (Fin n) (Fin n) (𝓞 E)) (hdet : (Gm.map ((↑) : 𝓞 E → E)).det ≠ 0) :
    Gm.det ≠ 0 := by
  intro h
  apply hdet
  rw [show (Gm.map ((↑) : 𝓞 E → E)) = (algebraMap (𝓞 E) E).mapMatrix Gm from rfl, ← RingHom.map_det, h, map_zero]

theorem card_quot {n : ℕ} (Gm : Matrix (Fin n) (Fin n) (𝓞 E)) (h : Gm.det ≠ 0) :
    Nat.card ((Fin n → 𝓞 E) ⧸ LinearMap.range (Matrix.mulVecLin Gm)) = (Algebra.norm ℤ Gm.det).natAbs := by
  have hinj : Function.Injective (Matrix.mulVecLin Gm) := fun a b hab ↦ by
    have : Gm *ᵥ (a - b) = 0 := by
      rw [Matrix.mulVec_sub]; exact sub_eq_zero.2 hab
    exact sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero h this)
  set N : Submodule ℤ (Fin n → 𝓞 E) := (LinearMap.range (Matrix.mulVecLin Gm)).restrictScalars ℤ with hN
  let e : (Fin n → 𝓞 E) ≃ₗ[ℤ] N := (LinearEquiv.ofInjective (Matrix.mulVecLin Gm) hinj).restrictScalars ℤ
  have key := Submodule.natAbs_det_equiv N e
  have hq : Nat.card ((Fin n → 𝓞 E) ⧸ N) = Nat.card ((Fin n → 𝓞 E) ⧸ LinearMap.range (Matrix.mulVecLin Gm)) :=
    Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ (LinearMap.range (Matrix.mulVecLin Gm))).toEquiv
  rw [← hq, ← key]
  have hmap : (N.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : (Fin n → 𝓞 E) →+ N)) =
      (Matrix.mulVecLin Gm).restrictScalars ℤ := by
    ext x
    rfl
  rw [hmap, LinearMap.det_restrictScalars, ← Matrix.toLin'_apply', LinearMap.det_toLin']

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc

variable {E : Type} [Field E] [NumberField E]

abbrev P0 (n : ℕ) : Submodule (𝓞 E) (Fin n → E) := LinearMap.range (incl (E := E) n)

def Between {n : ℕ} (G : Matrix (Fin n) (Fin n) E) : Set (Submodule (𝓞 E) (Fin n → E)) :=
  {C | P0 n ≤ C ∧ C ≤ LinearMap.range (psi G) ∧ C.FG}

theorem between_finite_card {n : ℕ} (Gm : Matrix (Fin n) (Fin n) (𝓞 E))
    (hdet : (Gm.map ((↑) : 𝓞 E → E)).det ≠ 0) :
    (Between (Gm.map ((↑) : 𝓞 E → E))).Finite ∧
    (Between (Gm.map ((↑) : 𝓞 E → E))).ncard ≤ (Algebra.norm ℤ Gm.det).natAbs ^ n := by
  classical
  set G := Gm.map ((↑) : 𝓞 E → E) with hG
  set Rg := LinearMap.range (Matrix.mulVecLin Gm) with hRg
  have hcard := card_quot Gm (det_map_ne Gm hdet)
  have hpos : (Algebra.norm ℤ Gm.det).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact (Algebra.norm_ne_zero_iff).2 (det_map_ne Gm hdet)
  have : Finite ((Fin n → 𝓞 E) ⧸ Rg) := Nat.finite_of_card_ne_zero (hcard ▸ hpos)
  let θ : Submodule (𝓞 E) ((Fin n → 𝓞 E) ⧸ Rg) → Submodule (𝓞 E) (Fin n → E) :=
    fun H ↦ (H.comap Rg.mkQ).map (psi G)
  let Gen : Set (Submodule (𝓞 E) ((Fin n → 𝓞 E) ⧸ Rg)) :=
    {H | ∃ s : Fin n → (Fin n → 𝓞 E) ⧸ Rg, Submodule.span (𝓞 E) (Set.range s) = H}
  have hsub : Between G ⊆ θ '' Gen := by
    rintro C ⟨h0, h1, hfg⟩
    have hRC : Rg ≤ C.comap (psi G) := by
      rintro _ ⟨m, rfl⟩
      show psi G (Gm *ᵥ m) ∈ C
      rw [psi_mulVec Gm hdet]
      exact h0 ⟨m, rfl⟩
    refine ⟨(C.comap (psi G)).map Rg.mkQ, ?_, ?_⟩
    · obtain ⟨b, hb, hgen⟩ := Fr.genMod_fg (E := E) (Nat.card ((Fin n → 𝓞 E) ⧸ Rg)) Nat.card_pos.ne' n C hfg
      have hb' : ∀ a, ∃ m, psi G m = b a := fun a ↦ h1 (hb a)
      choose mb hmb using hb'
      refine ⟨fun a ↦ Rg.mkQ (mb a), le_antisymm ?_ ?_⟩
      · rw [Submodule.span_le]
        rintro _ ⟨a, rfl⟩
        refine Submodule.mem_map_of_mem ?_
        show psi G (mb a) ∈ C
        rw [hmb]
        exact hb a
      · rintro _ ⟨m, hm, rfl⟩
        obtain ⟨c, z, hz, hx⟩ := hgen (psi G m) hm
        obtain ⟨mz, hmz⟩ := h1 hz
        have hN : (Nat.card ((Fin n → 𝓞 E) ⧸ Rg)) • Rg.mkQ mz = 0 := card_nsmul_eq_zero'
        have hm_eq : m = ∑ a, c a • mb a + (Nat.card ((Fin n → 𝓞 E) ⧸ Rg)) • mz := by
          apply psi_injective G hdet
          rw [map_add, map_sum, map_nsmul, hx, hmz, ← Nat.cast_smul_eq_nsmul E]
          congr 1
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [map_smul, hmb]
        rw [hm_eq, map_add, map_sum, map_nsmul, hN, add_zero]
        exact Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self a))
    · show (((C.comap (psi G)).map Rg.mkQ).comap Rg.mkQ).map (psi G) = C
      rw [Submodule.comap_map_mkQ, sup_eq_right.2 hRC, Submodule.map_comap_eq, inf_eq_right.2 h1]
  have hGfin : Gen.Finite := by
    refine (Set.finite_range fun s : Fin n → (Fin n → 𝓞 E) ⧸ Rg ↦ Submodule.span (𝓞 E) (Set.range s)).subset ?_
    rintro H ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  have hGcard : Gen.ncard ≤ Nat.card ((Fin n → 𝓞 E) ⧸ Rg) ^ n := by
    have := Formalism.HermitianLattices.LatticeEstimates.moduli_intermediate_bound (𝓞 E) ((Fin n → 𝓞 E) ⧸ Rg) n
    rw [← Nat.card_coe_set_eq]
    exact this
  refine ⟨(hGfin.image θ).subset hsub, ?_⟩
  calc (Between G).ncard ≤ (θ '' Gen).ncard := Set.ncard_le_ncard hsub (hGfin.image θ)
    _ ≤ Gen.ncard := Set.ncard_image_le hGfin
    _ ≤ _ := by rw [← hcard]; exact hGcard

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc

end
end

section
noncomputable section

open NumberField Matrix
open scoped ComplexOrder

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc

section Norm

variable {E : Type} [Field E] [NumberField E]

theorem natAbs_norm_eq_prod (x : 𝓞 E) :
    ((Algebra.norm ℤ x).natAbs : ℝ) = ∏ φ : E →+* ℂ, ‖φ (x : E)‖ := by
  have h1 : ((Algebra.norm ℤ x).natAbs : ℝ) = |((Algebra.norm ℚ (x : E) : ℚ) : ℝ)| := by
    rw [Nat.cast_natAbs, ← Algebra.coe_norm_int]
    push_cast
    rfl
  have h3 : ‖algebraMap ℚ ℂ (Algebra.norm ℚ (x : E))‖ = |((Algebra.norm ℚ (x : E) : ℚ) : ℝ)| := by
    simp
  rw [h1, ← h3, Algebra.norm_eq_prod_embeddings ℚ ℂ (x : E), norm_prod]
  exact Fintype.prod_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ (fun σ => rfl)

end Norm

section Had

variable {E : Type} [Field E] [NumberField E] [StarRing E]

open Formalism.BasicNotions

def GramFac (S : HSpace E) : Prop :=
  ∀ φ : E →+* ℂ, ∃ (m : Type) (_ : Fintype m) (ℓ : S.V → m → ℂ) (s : ℂ), ‖s‖ = 1 ∧
    ∀ x y, φ (S.hT x y) = s * (star (ℓ x) ⬝ᵥ ℓ y)

theorem gramFac_of_definite (S : HSpace E) (hstar : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a))
    (hsig : S.SigOK) (hdef : S.IsDefinite) : GramFac S := by
  intro φ
  obtain ⟨e, Q, s, hs1, hG⟩ := factor_of_sig (S.gram.map φ) _ _ (hsig φ)
    (by rcases hdef φ with h | h <;> simp [h])
  refine ⟨_, inferInstance, fun x ↦ Q *ᵥ ((fun i ↦ φ (S.frame.repr x i)) ∘ e.symm), s, hs1, fun x y ↦ ?_⟩
  rw [phi_hT S φ (hstar φ), ← dot_reindex e, hG, Matrix.smul_mulVec, dotProduct_smul, ← Matrix.mulVec_mulVec,
    dotProduct_mulVec, star_mulVec, smul_eq_mul]

theorem gramFac_of_isomEmb (S S' : HSpace E) (ι : S.V →ₗ[E] S'.V) (hι : HSpace.IsIsomEmb S S' ι)
    (h : GramFac S') : GramFac S := by
  intro φ
  obtain ⟨m, hm, ℓ, s, hs, h'⟩ := h φ
  exact ⟨m, hm, ℓ ∘ ι, s, hs, fun x y => by rw [← hι x y]; exact h' _ _⟩

theorem norm_eq_re_of_nonneg {z : ℂ} (h : 0 ≤ z) : ‖z‖ = z.re := by
  obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 h
  have hz : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [← h2])
  conv_lhs => rw [hz]
  exact Complex.norm_of_nonneg h1

theorem had_gram (S : HSpace E) (hF : GramFac S) (φ : E →+* ℂ) {k : ℕ} (x : Fin k → S.V)
    (M : Matrix (Fin k) (Fin k) E) (hM : ∀ i j, M i j = S.hT (x i) (x j)) :
    ‖φ M.det‖ ≤ ∏ c, ‖φ (S.hT (x c) (x c))‖ := by
  classical
  obtain ⟨m, hm, ℓ, s, hs, hℓ⟩ := hF φ
  let A : Matrix m (Fin k) ℂ := Matrix.of fun a i ↦ ℓ (x i) a
  have hAA : ∀ i j, (Aᴴ * A) i j = star (ℓ (x i)) ⬝ᵥ ℓ (x j) := by
    intro i j
    simp [A, Matrix.mul_apply, dotProduct, Matrix.conjTranspose_apply]
  have hB : M.map φ = s • (Aᴴ * A) := by
    ext i j
    rw [Matrix.map_apply, hM, hℓ, Matrix.smul_apply, hAA, smul_eq_mul]
  have hP := posSemidef_conjTranspose_mul_self A
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hB, Matrix.det_smul, norm_mul, norm_pow, hs, one_pow, one_mul,
    norm_eq_re_of_nonneg hP.det_nonneg]
  refine le_trans (Formalism.HermitianLattices.LatticeEstimates.hadamard_inequality_bound k _ hP) (le_of_eq (Finset.prod_congr rfl fun c _ ↦ ?_))
  rw [hℓ, norm_mul, hs, one_mul, ← hAA, norm_eq_re_of_nonneg hP.diag_nonneg]

theorem prod_le_of_mean (S : HSpace E) {k : ℕ} (x : Fin k → S.V) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hx : ∀ c, meanAbs (S.hT (x c) (x c)) ≤ ρ) :
    ∏ φ : E →+* ℂ, ∏ c, ‖φ (S.hT (x c) (x c))‖ ≤ ρ ^ (Module.finrank ℚ E * k) := by
  have hcard := NumberField.Embeddings.card E ℂ
  have hd : (0 : ℝ) < Fintype.card (E →+* ℂ) := by exact_mod_cast Fintype.card_pos
  have key : ∀ c, ∏ φ : E →+* ℂ, ‖φ (S.hT (x c) (x c))‖ ≤ ρ ^ Module.finrank ℚ E := by
    intro c
    have hg := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1 : ℝ))
      (fun φ : E →+* ℂ => ‖φ (S.hT (x c) (x c))‖) (by simp) (by simpa using hd)
      (fun _ _ => norm_nonneg _)
    simp only [Real.rpow_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      one_mul] at hg
    have hmean : (∑ φ : E →+* ℂ, ‖φ (S.hT (x c) (x c))‖) / (Fintype.card (E →+* ℂ) : ℝ) ≤ ρ := by
      have := hx c
      simp only [meanAbs] at this
      rwa [hcard]
    have hP : 0 ≤ ∏ φ : E →+* ℂ, ‖φ (S.hT (x c) (x c))‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
    rw [← hcard]
    calc ∏ φ : E →+* ℂ, ‖φ (S.hT (x c) (x c))‖
        = ((∏ φ : E →+* ℂ, ‖φ (S.hT (x c) (x c))‖) ^ ((Fintype.card (E →+* ℂ) : ℝ)⁻¹)) ^
            Fintype.card (E →+* ℂ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hP, inv_mul_cancel₀ hd.ne', Real.rpow_one]
      _ ≤ ρ ^ Fintype.card (E →+* ℂ) := pow_le_pow_left₀ (Real.rpow_nonneg hP _) (hg.trans hmean) _
  rw [Finset.prod_comm]
  calc ∏ c, ∏ φ : E →+* ℂ, ‖φ (S.hT (x c) (x c))‖ ≤ ∏ _c : Fin k, ρ ^ Module.finrank ℚ E :=
        Finset.prod_le_prod (fun c _ => Finset.prod_nonneg fun _ _ => norm_nonneg _) (fun c _ => key c)
    _ = ρ ^ (Module.finrank ℚ E * k) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

end Had

section Coord

variable {E : Type} [Field E] [NumberField E] [StarRing E]

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

theorem hT_equivFun_symm (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V) (i : Fin S.rank)
    (z : Fin S.rank → E) :
    S.hT (b i) (b.equivFun.symm z) = ((fun i j ↦ S.hT (b i) (b j) : Matrix (Fin S.rank) (Fin S.rank) E) *ᵥ z) i := by
  rw [Module.Basis.equivFun_symm_apply, map_sum]
  simp only [map_smul, smul_eq_mul, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem gram_det_ne (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V) :
    Matrix.det (fun i j ↦ S.hT (b i) (b j) : Matrix (Fin S.rank) (Fin S.rank) E) ≠ 0 := by
  intro hdet
  obtain ⟨z, hz, hGz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hy0 : b.equivFun.symm z ≠ 0 := by
    intro h
    apply hz
    have := b.equivFun.apply_symm_apply z
    rw [h, map_zero] at this
    exact this.symm
  apply hy0
  apply S.nondeg.2
  intro x
  rw [← b.sum_repr x, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hT_equivFun_symm, hGz]
  simp

theorem gram_int (S : HSpace E) (q : ℕ) (L : Submodule (𝓞 E) S.V) (b : Module.Basis (Fin S.rank) E S.V)
    (hq : LatT S q L) (hbL : ∀ c, b c ∈ L) (i j : Fin S.rank) :
    S.hT (b i) (b j) ∈ (algebraMap (𝓞 E) E).range :=
  hq.1 (b j) (hbL j) (b i) (hbL i)

theorem key_between (S : HSpace E) (q : ℕ) (L : Submodule (𝓞 E) S.V) (b : Module.Basis (Fin S.rank) E S.V)
    (hL : Submodule.IsLattice E L) (hq : LatT S q L) (hbL : ∀ c, b c ∈ L) :
    (keyOf S b L).2 ∈ Between (keyOf S b L).1 := by
  simp only [keyOf, Between, Set.mem_setOf_eq]
  have hG := gram_det_ne S b
  refine ⟨?_, ?_, hL.fg.map _⟩
  · rintro v ⟨w, rfl⟩
    refine ⟨b.equivFun.symm (incl S.rank w), ?_, b.equivFun.apply_symm_apply _⟩
    rw [Module.Basis.equivFun_symm_apply]
    refine Submodule.sum_mem _ fun c _ => ?_
    unfold incl
    simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply]
    rw [algebraMap_smul]
    exact L.smul_mem _ (hbL c)
  · rintro v ⟨x, hx, rfl⟩
    choose w hw using fun i => hq.1 x hx (b i) (hbL i)
    refine ⟨w, ?_⟩
    have hx' : incl S.rank w =
        (fun i j ↦ S.hT (b i) (b j) : Matrix (Fin S.rank) (Fin S.rank) E) *ᵥ b.equivFun x := by
      funext i
      unfold incl
      simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply]
      rw [hw i, ← hT_equivFun_symm S b i (b.equivFun x), LinearEquiv.symm_apply_apply]
    have key : ∀ (M : Matrix (Fin S.rank) (Fin S.rank) E), M.det ≠ 0 → ∀ v, M⁻¹ *ᵥ (M *ᵥ v) = v := by
      intro M hM v
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hM), Matrix.one_mulVec]
    unfold psi
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      LinearMap.compLeft_apply, Algebra.linearMap_apply, Matrix.mulVecLin_apply,
      LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply]
    rw [hx']
    exact key _ hG _

theorem coordCount_of (S : HSpace E) (q : ℕ) (ρ B2 : ℝ) (hρ : 0 ≤ ρ) (hF : GramFac S)
    (hB : ρ ^ (Module.finrank ℚ E * S.rank * S.rank) ≤ Real.exp B2) : CoordCount S q ρ B2 := by
  classical
  let Good : Matrix (Fin S.rank) (Fin S.rank) E → Submodule (𝓞 E) (Fin S.rank → E) → Prop := fun G C ↦
    ∃ (L : Submodule (𝓞 E) S.V) (b : Module.Basis (Fin S.rank) E S.V), Submodule.IsLattice E L ∧ LatT S q L ∧
      (∀ c, b c ∈ L) ∧ (∀ c, meanAbs (S.hT (b c) (b c)) ≤ ρ) ∧ keyOf S b L = (G, C)
  let St : Matrix (Fin S.rank) (Fin S.rank) E → Set (Submodule (𝓞 E) (Fin S.rank → E)) := fun G ↦ {C | Good G C}
  have hbound : ∀ (L : Submodule (𝓞 E) S.V) (b : Module.Basis (Fin S.rank) E S.V), Submodule.IsLattice E L →
      LatT S q L → (∀ c, b c ∈ L) → (∀ c, meanAbs (S.hT (b c) (b c)) ≤ ρ) →
      (St (keyOf S b L).1).Finite ∧ ((St (keyOf S b L).1).ncard : ℝ) ≤ Real.exp B2 := by
    intro L b hL hq hbL hbs
    set G : Matrix (Fin S.rank) (Fin S.rank) E := (keyOf S b L).1 with hG
    have hint := gram_int S q L b hq hbL
    choose Gm0 hGm using hint
    set Gm : Matrix (Fin S.rank) (Fin S.rank) (𝓞 E) := Matrix.of Gm0 with hGm0
    have hGmG : Gm.map ((↑) : 𝓞 E → E) = G := by
      ext i j
      exact hGm i j
    have hdet : (Gm.map ((↑) : 𝓞 E → E)).det ≠ 0 := by
      rw [hGmG]; exact gram_det_ne S b
    obtain ⟨hfin, hcard⟩ := between_finite_card Gm hdet
    rw [hGmG] at hfin hcard
    have hsub : St G ⊆ Between G := by
      rintro C ⟨L', b', hL', hq', hbL', _, hk⟩
      have := key_between S q L' b' hL' hq' hbL'
      rw [hk] at this
      exact this
    refine ⟨hfin.subset hsub, ?_⟩
    have h1 : ((St G).ncard : ℝ) ≤ ((Algebra.norm ℤ Gm.det).natAbs : ℝ) ^ S.rank := by
      exact_mod_cast (Set.ncard_le_ncard hsub hfin).trans hcard
    have hdetE : ((Gm.det : 𝓞 E) : E) = G.det := by
      rw [← hGmG]
      exact RingHom.map_det (algebraMap (𝓞 E) E) Gm
    have h2 : ((Algebra.norm ℤ Gm.det).natAbs : ℝ) ≤ ρ ^ (Module.finrank ℚ E * S.rank) := by
      rw [natAbs_norm_eq_prod, hdetE]
      refine le_trans (Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) fun φ _ ↦ had_gram S hF φ b G fun i j ↦ rfl) ?_
      exact prod_le_of_mean S b hρ hbs
    refine h1.trans (le_trans ?_ hB)
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) h2 _
  refine ⟨fun G ↦ if h : (St G).Finite ∧ ((St G).ncard : ℝ) ≤ Real.exp B2 then h.1.toFinset else ∅, ?_, ?_⟩
  · intro G
    dsimp only
    split_ifs with h
    · rw [← Set.ncard_eq_toFinset_card _ h.1]
      exact h.2
    · simp [(Real.exp_pos B2).le]
  · intro L b hL hq hbL hbs
    have hgood : (keyOf S b L).2 ∈ St (keyOf S b L).1 := ⟨L, b, hL, hq, hbL, hbs, rfl⟩
    dsimp only
    rw [dif_pos (hbound L b hL hq hbL hbs), Set.Finite.mem_toFinset]
    exact hgood

end Coord

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc

end
end

section
noncomputable section

open NumberField

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree Cc

section CoordRecord

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gramFac_X (D : D7) (i : ℕ) (hi : i ≤ D.R.m) : GramFac (D.sp.X i) :=
  gramFac_of_definite _ (host_star D) (D.sp.X_sig i) (D.sp.X_def i hi)

theorem gramFac_X' (D : D7) : GramFac D.sp.X' :=
  gramFac_of_isomEmb _ _ D.sp.iX' D.sp.iX'_isom (gramFac_X D D.R.m le_rfl)

theorem coordCount_rec (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (hC : 1 ≤ C₀) (S : HSpace D.host.E) (q n : ℕ)
    (hn : 1 ≤ n) (hr : S.rank = n) (hF : GramFac S) :
    CoordCount S q (msRho D u C₀ n) (coordinateLogBound D u C₀ n) := by
  have h1 := one_le_radius_sq D u C₀ hC n hn
  have hl := Real.log_nonneg h1
  refine coordCount_of S q _ _ (by unfold msRho; linarith) hF ?_
  rw [hr, Formalism.MainNotions.flipTwoThree.b_finrank_host]
  have hpos : 0 < msRho D u C₀ n ^ (2 * D.R.f * n * n) := pow_pos (by unfold msRho; linarith) _
  rw [← Real.log_le_iff_le_exp hpos, Real.log_pow]
  unfold msRho coordinateLogBound
  push_cast
  have hn' : (0 : ℝ) ≤ n := by positivity
  have hf : (0 : ℝ) ≤ D.R.f := by positivity
  have hp : 0 ≤ (D.R.f : ℝ) * n * Real.log (radiusSq D u C₀ n) := mul_nonneg (mul_nonneg hf hn') hl
  nlinarith [hp]

theorem coordCount_record (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (hC : 1 ≤ C₀) :
    (∀ i ≤ D.R.m, CoordCount (D.sp.X i) (Tu D u ^ (2 * D.R.f)) (msRho D u C₀ (D.R.N i)) (coordinateLogBound D u C₀ (D.R.N i))) ∧
    CoordCount D.sp.X' 1 (msRho D u C₀ (D.R.N D.R.m - 1)) (coordinateLogBound D u C₀ (D.R.N D.R.m - 1)) := by
  refine ⟨fun i hi ↦ coordCount_rec D u C₀ hC _ _ _ ?_ (D.sp.X_rank i hi) (gramFac_X D i hi), ?_⟩
  · have := D.R.k_ge
    unfold Ranks.N
    omega
  · have hN : D.R.N D.R.m - 1 = D.R.rankX' := by
      have := Formalism.BasicNotions.factXm D.R
      omega
    refine coordCount_rec D u C₀ hC _ _ _ ?_ (by rw [D.sp.X'_rank, hN]) (gramFac_X' D)
    rw [hN]
    unfold Ranks.rankX' Ranks.r
    have := D.R.k_ge
    omega

end CoordRecord

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
noncomputable section

open NumberField

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

section ShortSpan

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def ShortSpan (S : HSpace E) (q : ℕ) (ρ : ℝ) : Prop :=
  ∀ L : Submodule (𝓞 E) S.V, Submodule.IsLattice E L → LatT S q L →
    Submodule.span E {x | x ∈ L ∧ meanAbs (S.hT x x) ≤ ρ} = ⊤

theorem shortFrame_of_span (S : HSpace E) (q : ℕ) (ρ : ℝ) (h : ShortSpan S q ρ) : ShortFrame S q ρ := by
  intro L hL hq
  set s : Set S.V := {x | x ∈ L ∧ meanAbs (S.hT x x) ≤ ρ} with hs
  obtain ⟨t, hts, htsp, hti⟩ := exists_linearIndependent E s
  have htop : ⊤ ≤ Submodule.span E (Set.range ((↑) : t → S.V)) := by
    rw [Subtype.range_coe, htsp, hs, h L hL hq]
  let B : Module.Basis t E S.V := Module.Basis.mk hti htop
  let b : Module.Basis (Fin S.rank) E S.V := B.reindex (B.indexEquiv S.frame)
  have hb : ∀ c, b c ∈ s := fun c ↦ by
    simp only [b, Module.Basis.reindex_apply, B, Module.Basis.mk_apply]
    exact hts (Subtype.prop _)
  exact ⟨b, fun c ↦ (hb c).1, fun c ↦ (hb c).2⟩

end ShortSpan

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end
