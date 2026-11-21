import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SigOKOf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SigAtLeast
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondOnCommonRangeOfSecond
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCI
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianDecompositionInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeOfLevelClass

section
open Matrix NumberField
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.Glob.WLt

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cc_cc (t : E) : FD.cc (FD.cc t) = t := IsCMField.complexConj_apply_apply E t

theorem emb_cc (τ : E →+* ℂ) (t : E) : τ (FD.cc t) = conj (τ t) := IsCMField.complexEmbedding_complexConj E τ t

theorem exists_skew : ∃ θ : E, θ ≠ 0 ∧ FD.cc θ = -θ := by
  by_contra hne
  push Not at hne
  apply IsCMField.complexConj_ne_one E
  ext t
  by_contra ht
  have h1 : t - FD.cc t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  apply hne _ h1
  show IsCMField.complexConj E (t - FD.cc t) = -(t - FD.cc t)
  rw [map_sub]
  change FD.cc t - FD.cc (FD.cc t) = _
  rw [cc_cc]
  ring

theorem emb_real (τ : E →+* ℂ) {t : E} (ht : FD.cc t = t) : τ t = ((τ t).re : ℂ) := by
  have h := emb_cc τ t
  rw [ht] at h
  apply Complex.ext
  · simp
  · have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    simp only [Complex.ofReal_im]
    linarith

theorem iso_diag {r : ℕ} (g : Fin (r + 1) → E) (hr : 2 ≤ r) (hg : ∀ i, FD.cc (g i) = g i) (hg0 : ∀ i, g i ≠ 0)
    (hs : ∀ τ : E →+* ℂ, (∃ i, 0 < (τ (g i)).re) ∧ (∃ j, (τ (g j)).re < 0)) :
    ∃ z : Fin (r + 1) → E, z ≠ 0 ∧ z ⬝ᵥ diagonal g *ᵥ (FD.cc ∘ z) = 0 := by
  obtain ⟨θ, hθ0, hθ⟩ := exists_skew (E := E)
  have hF : ∀ t : E, IsCMField.complexConj E t = t ↔ ∃ s : maximalRealSubfield E, algebraMap (maximalRealSubfield E) E s = t :=
    fun t => (IsCMField.complexConj_eq_self_iff E t).trans ⟨fun h => ⟨⟨t, h⟩, rfl⟩, by rintro ⟨s, rfl⟩; exact s.2⟩
  have hne : ∀ (τ : E →+* ℂ) (i : Fin (r + 1)), (τ (g i)).re ≠ 0 := by
    intro τ i h
    have h1 := emb_real τ (hg i)
    rw [h, Complex.ofReal_zero] at h1
    exact hg0 i ((map_eq_zero τ).1 h1)
  obtain ⟨z, hz⟩ := GlobalTheory.HermGlobal.exists_represent (σ := IsCMField.complexConj E) (IsCMField.complexConj_apply_apply E) hF
    hθ0 hθ hr (g := fun i => g i.succ) (fun i => hg _) (fun i => hg0 _) (b := -g 0)
    (by show IsCMField.complexConj E (-g 0) = -g 0; rw [map_neg]; exact congrArg Neg.neg (hg 0))
    (neg_ne_zero.mpr (hg0 0)) (by
      intro τ _
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hs τ
      have hb : (τ (-g 0)).re = -(τ (g 0)).re := by simp
      rcases lt_or_gt_of_ne (hne τ 0) with h0 | h0
      ·
        have hi0 : i ≠ 0 := by rintro rfl; linarith
        obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi0
        exact ⟨i', by simp only [hb]; constructor <;> intro _ <;> linarith⟩
      · have hj0 : j ≠ 0 := by rintro rfl; linarith
        obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj0
        exact ⟨j', by simp only [hb]; constructor <;> intro h <;> linarith⟩)
  refine ⟨Fin.cons 1 z, fun h => one_ne_zero (congrFun h 0), ?_⟩
  have key : (Fin.cons 1 z : Fin (r + 1) → E) ⬝ᵥ diagonal g *ᵥ (FD.cc ∘ Fin.cons 1 z) =
      g 0 + z ⬝ᵥ diagonal (fun i => g i.succ) *ᵥ (FD.cc ∘ z) := by
    simp only [dotProduct, mulVec_diagonal, Fin.sum_univ_succ, Function.comp_apply, Fin.cons_zero, Fin.cons_succ]
    have : FD.cc (1 : E) = 1 := map_one (IsCMField.complexConj E)
    rw [this]
    ring
  rw [key]
  have hz' : z ⬝ᵥ diagonal (fun i => g i.succ) *ᵥ (FD.cc ∘ z) = -g 0 := hz
  rw [hz']
  ring

end PositivityTheory.Rg.Sw.Glob.WLt
end

section
open Matrix NumberField GlobalTheory.Inertia
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Rg.Sw.Glob.WLt

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev hf {n : Type} [Fintype n] (G : Matrix n n E) (x y : n → E) : E := x ⬝ᵥ G *ᵥ (FD.cc ∘ y)

theorem cc_mulVec {n m : Type} [Fintype n] [Fintype m] (P : Matrix n m E) (y : m → E) :
    FD.cc ∘ (P *ᵥ y) = P.map FD.cc *ᵥ (FD.cc ∘ y) := by
  funext i
  simp [mulVec, dotProduct, FD.cc, map_sum, map_mul]

theorem hf_congr {n m : Type} [Fintype n] [Fintype m] (G : Matrix n n E) (P : Matrix n m E) (x y : m → E) :
    hf (Pᵀ * G * P.map FD.cc) x y = hf G (P *ᵥ x) (P *ᵥ y) := by
  simp only [hf]
  rw [cc_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

theorem hf_submatrix {n m : Type} [Fintype n] [Fintype m] (G : Matrix n n E) (e : m ≃ n) (x y : m → E) :
    hf (G.submatrix e e) x y = hf G (x ∘ e.symm) (y ∘ e.symm) := by
  simp only [hf, submatrix_mulVec_equiv, Function.comp_def, Equiv.symm_symm]
  rw [dotProduct, dotProduct, ← Equiv.sum_comp e (fun i => x (e.symm i) * _)]
  simp

theorem hf_symm {n : Type} [Fintype n] {G : Matrix n n E} (hG : ∀ a b, FD.cc (G a b) = G b a) (x y : n → E) :
    hf G y x = FD.cc (hf G x y) := by
  have hc : ∀ s : Finset n, ∀ f : n → E, FD.cc (∑ i ∈ s, f i) = ∑ i ∈ s, FD.cc (f i) :=
    fun s f => map_sum (IsCMField.complexConj E) f s
  have hm : ∀ a b : E, FD.cc (a * b) = FD.cc a * FD.cc b := fun a b => map_mul (IsCMField.complexConj E) a b
  simp only [hf, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, hc, hm, cc_cc, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hf_add_left {n : Type} [Fintype n] (G : Matrix n n E) (x x' y : n → E) :
    hf G (x + x') y = hf G x y + hf G x' y := by simp [hf, add_dotProduct]

theorem hf_smul_left {n : Type} [Fintype n] (G : Matrix n n E) (a : E) (x y : n → E) :
    hf G (a • x) y = a * hf G x y := by simp [hf, smul_dotProduct]

theorem hf_add_right {n : Type} [Fintype n] (G : Matrix n n E) (x y y' : n → E) :
    hf G x (y + y') = hf G x y + hf G x y' := by
  have h : FD.cc ∘ (y + y') = FD.cc ∘ y + FD.cc ∘ y' :=
    funext fun i => map_add (IsCMField.complexConj E) (y i) (y' i)
  simp only [hf, h, mulVec_add, dotProduct_add]

theorem hf_smul_right {n : Type} [Fintype n] (G : Matrix n n E) (a : E) (x y : n → E) :
    hf G x (a • y) = FD.cc a * hf G x y := by
  have h : FD.cc ∘ (a • y) = FD.cc a • (FD.cc ∘ y) :=
    funext fun i => map_mul (IsCMField.complexConj E) a (y i)
  simp only [hf, h, mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem exists_isotropic_of_three_le_of_indefinite {m : ℕ} (G : Matrix (Fin m) (Fin m) E) (hG : ∀ a b, FD.cc (G a b) = G b a)
    (hd : G.det ≠ 0) (h3 : 3 ≤ m)
    (hs : ∀ τ : E →+* ℂ, 1 ≤ posIndex (G.map τ) ∧ 1 ≤ negIndex (G.map τ)) :
    ∃ z : Fin m → E, z ≠ 0 ∧ hf G z z = 0 := by
  obtain ⟨P, d, hP, hPd, hdr, hd0⟩ := GlobalTheory.HermDiag.exists_congr_diagonal_herm hG
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  have hsig : ∀ τ : E →+* ℂ, (∃ i, 0 < (τ (d i)).re) ∧ ∃ j, (τ (d j)).re < 0 := by
    intro τ
    obtain ⟨h1, h2⟩ := hs τ
    rw [posIndex_map_eq_card_of_congr_diagonal τ hP hPd] at h1
    have hPd' : Pᵀ * (-G) * P.map FD.cc = diagonal (-d) := by
      rw [Matrix.mul_neg, Matrix.neg_mul, hPd, diagonal_neg]
      rfl
    have hneg : (-G).map τ = -(G.map τ) := by
      ext i j
      simp
    have h2' : 1 ≤ posIndex ((-G).map τ) := by
      rwa [hneg, posIndex_neg]
    rw [posIndex_map_eq_card_of_congr_diagonal τ hP hPd'] at h2'
    obtain ⟨i, hi⟩ := Finset.card_pos.mp h1
    obtain ⟨j, hj⟩ := Finset.card_pos.mp h2'
    refine ⟨⟨i, by simpa using hi⟩, ⟨j, ?_⟩⟩
    simpa using hj
  obtain ⟨z, hz, hz0⟩ := iso_diag d (by omega) hdr (hd0 hd) hsig
  refine ⟨P *ᵥ z, fun h => hz (eq_zero_of_mulVec_eq_zero hP h), ?_⟩
  rw [← hf_congr, hPd]
  exact hz0

theorem iso_gen {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n E) (hG : ∀ a b, FD.cc (G a b) = G b a)
    (hd : G.det ≠ 0) (h3 : 3 ≤ Fintype.card n)
    (hs : ∀ τ : E →+* ℂ, 1 ≤ posIndex (G.map τ) ∧ 1 ≤ negIndex (G.map τ)) :
    ∃ z : n → E, z ≠ 0 ∧ hf G z z = 0 := by
  obtain ⟨e⟩ : Nonempty (Fin (Fintype.card n) ≃ n) := ⟨(Fintype.equivFin n).symm⟩
  obtain ⟨z, hz, hz0⟩ := exists_isotropic_of_three_le_of_indefinite (G.submatrix e e) (fun a b => hG _ _)
    (by rwa [det_submatrix_equiv_self]) h3
    (fun τ => by rw [← submatrix_map, posIndex_submatrix_equiv, negIndex_submatrix_equiv]; exact hs τ)
  refine ⟨z ∘ e.symm, ?_, ?_⟩
  · intro h
    apply hz
    funext i
    simpa using congrFun h (e i)
  · rw [← hf_submatrix]
    exact hz0

end PositivityTheory.Rg.Sw.Glob.WLt

end
end

section
open Matrix NumberField GlobalTheory.Inertia
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Rg.Sw.Glob.WLt

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def hyp : Matrix (Fin 2) (Fin 2) E := !![0, 1; 1, 0]

theorem cc_one : FD.cc (1 : E) = 1 := map_one (IsCMField.complexConj E)

theorem cc_zero : FD.cc (0 : E) = 0 := map_zero (IsCMField.complexConj E)

theorem cc_neg (t : E) : FD.cc (-t) = -FD.cc t := map_neg (IsCMField.complexConj E) t

theorem cc_div_two (t : E) : FD.cc (t / 2) = FD.cc t / 2 := by
  show IsCMField.complexConj E (t / 2) = _
  rw [map_div₀, map_ofNat]
  rfl

theorem exists_pair {n : Type} [Fintype n] [DecidableEq n] {G : Matrix n n E} (hG : ∀ a b, FD.cc (G a b) = G b a)
    (hd : G.det ≠ 0) {z : n → E} (hz0 : z ≠ 0) (hz : hf G z z = 0) :
    ∃ w : n → E, hf G z w = 1 ∧ hf G w w = 0 := by
  have hu : z ᵥ* G ≠ 0 := by
    intro h
    apply hz0
    have h1 := congrArg (· ᵥ* G⁻¹) h
    simp only [Matrix.vecMul_vecMul, Matrix.zero_vecMul] at h1
    rwa [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det G).1 ((Matrix.isUnit_iff_isUnit_det G).2 hd.isUnit)),
      Matrix.vecMul_one] at h1
  obtain ⟨b, hb⟩ : ∃ b, (z ᵥ* G) b ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext h)
  set c := (z ᵥ* G) b with hc
  let v : n → E := c⁻¹ • Pi.single b 1
  let w0 : n → E := FD.cc ∘ v
  have hw0 : hf G z w0 = 1 := by
    have e1 : FD.cc ∘ w0 = v := by ext i; exact cc_cc (v i)
    simp only [hf]
    rw [e1, Matrix.dotProduct_mulVec]
    simp only [v, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]
    exact inv_mul_cancel₀ hb
  set a := hf G w0 w0 with ha
  have haa : FD.cc a = a := by rw [ha, ← hf_symm hG]
  refine ⟨w0 + (-(a / 2)) • z, ?_, ?_⟩
  · rw [hf_add_right, hf_smul_right, hz, hw0]; ring
  · have hzw : hf G w0 z = 1 := by rw [hf_symm hG, hw0, cc_one]
    rw [hf_add_left, hf_add_right, hf_add_right, hf_smul_left, hf_smul_left, hf_smul_right, hf_smul_right, hz, hw0, hzw,
      cc_neg, cc_div_two, haa, ← ha]
    ring

set_option maxHeartbeats 1600000 in

theorem split {n : Type} [Fintype n] [DecidableEq n] {G : Matrix n n E} (hG : ∀ a b, FD.cc (G a b) = G b a)
    (hd : G.det ≠ 0) {z : n → E} (hz0 : z ≠ 0) (hz : hf G z z = 0) :
    ∃ (m : ℕ) (e : Fin 2 ⊕ Fin m ≃ n) (G2 : Matrix (Fin m) (Fin m) E) (P : Matrix n n E), P.det ≠ 0 ∧
      Pᵀ * G * P.map FD.cc = (fromBlocks hyp 0 0 G2).submatrix e.symm e.symm ∧ (∀ a b, FD.cc (G2 a b) = G2 b a) ∧
        G2.det ≠ 0 := by
  obtain ⟨w, hzw, hww⟩ := exists_pair hG hd hz0 hz
  have hwz : hf G w z = 1 := by rw [hf_symm hG, hzw, cc_one]
  let L : (n → E) →ₗ[E] (Fin 2 → E) :=
    { toFun := fun x => ![hf G x z, hf G x w]
      map_add' := fun x y => by ext i; fin_cases i <;> simp [hf_add_left]
      map_smul' := fun t x => by ext i; fin_cases i <;> simp [hf_smul_left] }
  have hLz : L z = ![0, 1] := by ext i; fin_cases i <;> simp [L, hz, hzw]
  have hLw : L w = ![1, 0] := by ext i; fin_cases i <;> simp [L, hwz, hww]
  have hLs : Function.Surjective L := by
    intro v
    refine ⟨v 0 • w + v 1 • z, ?_⟩
    rw [map_add, map_smul, map_smul, hLz, hLw]
    ext i; fin_cases i <;> simp
  set K := LinearMap.ker L
  have hrk : Module.finrank E K + 2 = Fintype.card n := by
    show Module.finrank E (LinearMap.ker L) + 2 = _
    have h := LinearMap.finrank_range_add_finrank_ker L
    rw [LinearMap.range_eq_top.mpr hLs, finrank_top, Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card] at h
    omega
  set m := Module.finrank E K
  let bK : Module.Basis (Fin m) E K := Module.finBasis E K
  have hK : ∀ i, hf G (bK i : n → E) z = 0 ∧ hf G (bK i : n → E) w = 0 := by
    intro i
    have h := (bK i).2
    rw [LinearMap.mem_ker] at h
    exact ⟨congrFun h 0, congrFun h 1⟩
  let cols : Fin 2 ⊕ Fin m → (n → E) := Sum.elim ![z, w] fun i => (bK i : n → E)
  have hcard : Fintype.card (Fin 2 ⊕ Fin m) = Fintype.card n := by simp; omega
  let e : Fin 2 ⊕ Fin m ≃ n := Fintype.equivOfCardEq hcard
  let G2 : Matrix (Fin m) (Fin m) E := fun i j => hf G (bK i : n → E) (bK j : n → E)
  let P : Matrix n n E := fun k j => cols (e.symm j) k
  have hentry : ∀ s t, hf G (cols s) (cols t) = fromBlocks hyp 0 0 G2 s t := by
    rintro (i | i) (j | j)
    · fin_cases i <;> fin_cases j <;> simp [cols, hyp, hz, hzw, hwz, hww]
    · fin_cases i
      · simp [cols]
        rw [hf_symm hG (bK j : n → E) z, (hK j).1, cc_zero]
      · simp [cols]
        rw [hf_symm hG (bK j : n → E) w, (hK j).2, cc_zero]
    · fin_cases j
      · simp [cols, (hK i).1]
      · simp [cols, (hK i).2]
    · rfl
  have hT : Pᵀ * G * P.map FD.cc = (fromBlocks hyp 0 0 G2).submatrix e.symm e.symm := by
    ext a b
    rw [GlobalTheory.HermDiag.transpose_mul_mul_map_apply]
    exact hentry (e.symm a) (e.symm b)
  have hlin : ∀ (γ : Fin 2 ⊕ Fin m → E) (y : n → E),
      hf G (∑ s, γ s • cols s) y = ∑ s, γ s * hf G (cols s) y := by
    intro γ y
    let Ly : (n → E) →ₗ[E] E :=
      { toFun := fun x => hf G x y
        map_add' := fun x x' => hf_add_left G x x' y
        map_smul' := fun t x => hf_smul_left G t x y }
    have h1 : hf G (∑ s, γ s • cols s) y = Ly (∑ s, γ s • cols s) := rfl
    rw [h1, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, smul_eq_mul]
    rfl
  have hP : P.det ≠ 0 := by
    have hinj : Function.Injective P.mulVec := by
      intro α β hαβ
      have h0 : P *ᵥ (α - β) = 0 := by rw [Matrix.mulVec_sub, hαβ, sub_self]
      set γ : n → E := α - β with hγ
      have hsum : ∑ s, γ (e s) • cols s = 0 := by
        rw [← h0]
        ext k
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, P]
        rw [← e.sum_comp]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [Equiv.symm_apply_apply]
        ring
      have hz1 : γ (e (Sum.inl 1)) = 0 := by
        have h := hlin (fun s => γ (e s)) z
        rw [hsum] at h
        have h' : ∑ s, γ (e s) * hf G (cols s) z = γ (e (Sum.inl 1)) := by
          have hc : ∀ s, hf G (cols s) z = fromBlocks hyp 0 0 G2 s (Sum.inl 0) := fun s => hentry s (Sum.inl 0)
          simp only [hc, Fintype.sum_sum_type, Fin.sum_univ_two, fromBlocks_apply₁₁, fromBlocks_apply₂₁, hyp]
          simp
        rw [← h', ← h]
        simp [hf]
      have hw1 : γ (e (Sum.inl 0)) = 0 := by
        have h := hlin (fun s => γ (e s)) w
        rw [hsum] at h
        have h' : ∑ s, γ (e s) * hf G (cols s) w = γ (e (Sum.inl 0)) := by
          have hc : ∀ s, hf G (cols s) w = fromBlocks hyp 0 0 G2 s (Sum.inl 1) := fun s => hentry s (Sum.inl 1)
          simp only [hc, Fintype.sum_sum_type, Fin.sum_univ_two, fromBlocks_apply₁₁, fromBlocks_apply₂₁, hyp]
          simp
        rw [← h', ← h]
        simp [hf]
      have hrest : ∑ i, γ (e (Sum.inr i)) • bK i = 0 := by
        apply Subtype.ext
        have := hsum
        simp only [Fintype.sum_sum_type, Fin.sum_univ_two, hz1, hw1, zero_smul, zero_add] at this
        simpa [cols] using this
      have hcoef := (Fintype.linearIndependent_iff.1 bK.linearIndependent) _ hrest
      have hγ0 : γ = 0 := by
        funext k
        obtain ⟨s, rfl⟩ := e.surjective k
        rcases s with i | i
        · fin_cases i
          · exact hw1
          · exact hz1
        · exact hcoef i
      have := congrFun hγ0
      funext k
      have hk := this k
      simp only [hγ, Pi.sub_apply, Pi.zero_apply] at hk
      exact sub_eq_zero.mp hk
    have hu : IsUnit P := Matrix.mulVec_injective_iff_isUnit.1 hinj
    exact ((Matrix.isUnit_iff_isUnit_det P).1 hu).ne_zero
  have hG2 : ∀ a b, FD.cc (G2 a b) = G2 b a := fun a b => (hf_symm hG _ _).symm
  have hdetP : (P.map FD.cc).det ≠ 0 := by
    have : (P.map FD.cc).det = IsCMField.complexConj E P.det :=
      (RingHom.map_det (IsCMField.complexConj E : E →+* E) P).symm
    rw [this]
    exact (map_ne_zero _).2 hP
  have hdetT : ((fromBlocks hyp 0 0 G2).submatrix e.symm e.symm).det ≠ 0 := by
    rw [← hT, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hP hd) hdetP
  have hG2d : G2.det ≠ 0 := by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁] at hdetT
    intro h
    rw [h, mul_zero] at hdetT
    exact hdetT rfl
  exact ⟨m, e, G2, P, hP, hT, hG2, hG2d⟩

end PositivityTheory.Rg.Sw.Glob.WLt

end
end

section
open Matrix NumberField GlobalTheory.Inertia
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Rg.Sw.Glob.WLt

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hyp_map (τ : E →+* ℂ) : (hyp : Matrix (Fin 2) (Fin 2) E).map τ = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hyp]

theorem index_hyp (τ : E →+* ℂ) :
    posIndex ((hyp : Matrix (Fin 2) (Fin 2) E).map τ) = 1 ∧ negIndex ((hyp : Matrix (Fin 2) (Fin 2) E).map τ) = 1 := by
  rw [hyp_map]
  have hP : (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    norm_num
  have hD : (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ)ᵀ * !![0, 1; 1, 0] *
      (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) = diagonal ![2, -2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal] <;> norm_num
  refine ⟨?_, ?_⟩
  · rw [posIndex_eq_card_of_congr_diagonal hP hD, Finset.card_eq_one]
    refine ⟨0, ?_⟩
    ext k
    fin_cases k <;> simp
  · rw [negIndex_eq_card_of_congr_diagonal hP hD, Finset.card_eq_one]
    refine ⟨1, ?_⟩
    ext k
    fin_cases k <;> simp

theorem hf_blocks {m : ℕ} (G2 : Matrix (Fin m) (Fin m) E) (u u' : Fin 2 ⊕ Fin m → E) :
    hf (fromBlocks hyp 0 0 G2) u u' = hf hyp (u ∘ Sum.inl) (u' ∘ Sum.inl) + hf G2 (u ∘ Sum.inr) (u' ∘ Sum.inr) := by
  simp only [hf]
  rw [fromBlocks_mulVec]
  simp [dotProduct, Fintype.sum_sum_type, Function.comp_def]

private theorem posIndex_negIndex_eq_one_add_of_hyperbolic_split {n : Type} [Fintype n] [DecidableEq n] {m : ℕ} {G : Matrix n n E}
    {G2 : Matrix (Fin m) (Fin m) E} {P : Matrix n n E} (e : Fin 2 ⊕ Fin m ≃ n) (hP : P.det ≠ 0)
    (hPG : Pᵀ * G * P.map FD.cc = (fromBlocks hyp 0 0 G2).submatrix e.symm e.symm)
    (hG2 : ∀ a b, FD.cc (G2 a b) = G2 b a) (τ : E →+* ℂ) :
    posIndex (G.map τ) = 1 + posIndex (G2.map τ) ∧ negIndex (G.map τ) = 1 + negIndex (G2.map τ) := by
  have hQ : (P.map τ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero τ).2 hP
  have hmap : (P.map τ)ᵀ * G.map τ * (P.map τ).map (starRingEnd ℂ) =
      ((fromBlocks hyp 0 0 G2).submatrix e.symm e.symm).map τ := by
    rw [← hPG, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    congr 1
    ext i j
    simp [emb_cc]
  have hH1 : ((hyp : Matrix (Fin 2) (Fin 2) E).map τ).IsHermitian := by
    rw [hyp_map]
    apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  have hH2 : (G2.map τ).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [Matrix.map_apply]
    rw [← starRingEnd_apply, ← emb_cc, hG2]
  have hblk : ((fromBlocks hyp 0 0 G2).submatrix e.symm e.symm).map τ =
      (fromBlocks ((hyp : Matrix (Fin 2) (Fin 2) E).map τ) 0 0 (G2.map τ)).submatrix e.symm e.symm := by
    rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]
    simp
  obtain ⟨h1, h2⟩ := index_hyp (E := E) τ
  constructor
  · rw [← posIndex_congr (G.map τ) hQ, hmap, hblk, posIndex_submatrix_equiv,
      posIndex_fromBlocks hH1 hH2, h1]
  · rw [← negIndex_congr (G.map τ) hQ, hmap, hblk, negIndex_submatrix_equiv,
      negIndex_fromBlocks hH1 hH2, h2]

set_option maxHeartbeats 1600000 in

theorem main_iso : ∀ (k : ℕ) {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n E),
    (∀ a b, FD.cc (G a b) = G b a) → G.det ≠ 0 → 2 * k < Fintype.card n →
    (∀ τ : E →+* ℂ, k ≤ posIndex (G.map τ) ∧ k ≤ negIndex (G.map τ)) →
    ∃ W : Submodule E (n → E), Module.finrank E W = k ∧ ∀ x ∈ W, ∀ y ∈ W, hf G x y = 0 := fun
  | 0 => by
    intro G _ _ _ _
    refine ⟨⊥, by simp, ?_⟩
    intro x hx y hy
    rw [Submodule.mem_bot] at hx
    subst hx
    simp [hf]
  | k + 1 => by
    rename_i n _ _
    intro G hG hdet hcard hidx
    have h3 : 3 ≤ Fintype.card n := by omega
    obtain ⟨z, hz, hzz⟩ := iso_gen G hG hdet h3 (fun τ =>
      ⟨le_trans (Nat.le_add_left 1 k) (hidx τ).1, le_trans (Nat.le_add_left 1 k) (hidx τ).2⟩)
    obtain ⟨m, e, G2, P, hP, hPG, hG2, hdet2⟩ := split hG hdet hz hzz
    have hm := Fintype.card_congr e
    simp at hm
    obtain ⟨W2, hW2r, hW2⟩ := main_iso k G2 hG2 hdet2 (by simp; omega) (fun τ => by
      obtain ⟨h1, h2⟩ := posIndex_negIndex_eq_one_add_of_hyperbolic_split e hP hPG hG2 τ
      obtain ⟨h4, h5⟩ := hidx τ
      exact ⟨by omega, by omega⟩)
    let ψ : E × W2 →ₗ[E] (Fin 2 ⊕ Fin m → E) :=
      { toFun := fun p => Sum.elim ![p.1, 0] (p.2 : Fin m → E)
        map_add' := by
          intro p q
          ext (i | i)
          · fin_cases i <;> simp
          · simp
        map_smul' := by
          intro c p
          ext (i | i)
          · fin_cases i <;> simp
          · simp }
    let L : (Fin 2 ⊕ Fin m → E) →ₗ[E] (n → E) := P.mulVecLin ∘ₗ LinearMap.funLeft E E e.symm
    have hLapp : ∀ u, L u = P *ᵥ (u ∘ e.symm) := fun u => rfl
    have hψ : Function.Injective ψ := by
      intro p q hpq
      have h1 := congrFun hpq (Sum.inl 0)
      have h2 : ∀ i, (p.2 : Fin m → E) i = (q.2 : Fin m → E) i := fun i => congrFun hpq (Sum.inr i)
      simp [ψ] at h1
      exact Prod.ext h1 (Subtype.ext (funext h2))
    have hL : Function.Injective L := by
      have hu : Function.Injective P.mulVec :=
        Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det P).2 (isUnit_iff_ne_zero.2 hP))
      exact hu.comp (LinearMap.funLeft_injective_of_surjective E E _ e.symm.surjective)
    have hinj : Function.Injective (L ∘ₗ ψ) := by
      rw [LinearMap.coe_comp]
      exact hL.comp hψ
    have key : ∀ u u' : Fin 2 ⊕ Fin m → E, hf G (L u) (L u') = hf (fromBlocks hyp 0 0 G2) u u' := by
      intro u u'
      have := hf_congr G P (u ∘ e.symm) (u' ∘ e.symm)
      rw [hPG, hf_submatrix] at this
      rw [hLapp, hLapp]
      simpa [Function.comp_def] using this.symm
    refine ⟨LinearMap.range (L ∘ₗ ψ), ?_, ?_⟩
    · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, Module.finrank_self, hW2r]
      ring
    · intro x hx y hy
      obtain ⟨p, rfl⟩ := LinearMap.mem_range.1 hx
      obtain ⟨q, rfl⟩ := LinearMap.mem_range.1 hy
      show hf G (L (ψ p)) (L (ψ q)) = 0
      rw [key, hf_blocks]
      have e1 : ∀ r : E × W2, (ψ r ∘ Sum.inl) = ![r.1, 0] := by
        intro r
        funext i
        simp [ψ]
      have e2 : ∀ r : E × W2, (ψ r ∘ Sum.inr) = (r.2 : Fin m → E) := by
        intro r
        funext i
        simp [ψ]
      rw [e1, e2, e1, e2, hW2 _ p.2.2 _ q.2.2]
      simp [hf, hyp, dotProduct, mulVec, Fin.sum_univ_two]

end PositivityTheory.Rg.Sw.Glob.WLt

end
end

section
noncomputable section

open scoped Matrix ComplexConjugate
open Matrix Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Inertia NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open ReciprocityTheory.ChartRestriction.G

set_option maxHeartbeats 1600000 in
theorem wittLBlt : WittLBlt := by
  intro D V k hk hS
  letI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE
  have hH := GlobalTheory.Doubling.isHermND_gram V
  have hσ : ∀ x : D.host.E, D.sp.cm.sig x = FD.cc x := fun x => rfl
  have hT : ∀ a b, FD.cc (V.gram a b) = V.gram b a := fun a b => by rw [← hσ]; exact hH.1 b a
  have hTt : V.gramᵀ = V.gram.map FD.cc := Matrix.ext fun a b => (hT a b).symm
  have hG : ∀ a b, FD.cc (V.gramᵀ a b) = V.gramᵀ b a := fun a b => by
    simp only [transpose_apply]; exact hT b a
  have hd : V.gramᵀ.det ≠ 0 := by rw [det_transpose]; exact hH.2

  have hsigτ : ∀ τ0 : D.what₂.Tau, k ≤ posIndex (V.gram.map (tauE D τ0)) ∧ k ≤ negIndex (V.gram.map (tauE D τ0)) := by
    intro τ0
    obtain ⟨ε, fr, hu, hfr, hp, hq⟩ := hS τ0
    have hP : (fr.map (starRingEnd ℂ)).det ≠ 0 := by
      have : (fr.map (starRingEnd ℂ)).det = starRingEnd ℂ fr.det := (RingHom.map_det (starRingEnd ℂ) fr).symm
      rw [this]
      exact (map_ne_zero _).2 hu.ne_zero
    have hd' : (fr.map (starRingEnd ℂ))ᵀ * V.gram.map (tauE D τ0) * (fr.map (starRingEnd ℂ)).map (starRingEnd ℂ) =
        diagonal (PositivityTheory.Rg.Sw.sgn ε) := by
      have h1 : (fr.map (starRingEnd ℂ)).map (starRingEnd ℂ) = fr := by
        ext a b; simp
      rw [h1]
      exact hfr
    rw [posIndex_eq_card_of_congr_diagonal hP hd', negIndex_eq_card_of_congr_diagonal hP hd']
    have e1 : (Finset.univ.filter fun a => 0 < (PositivityTheory.Rg.Sw.sgn ε a).re) = Finset.univ.filter fun a => ε a = true := by
      apply Finset.filter_congr
      intro a _
      simp only [PositivityTheory.Rg.Sw.sgn]
      cases ε a <;> norm_num
    have e2 : (Finset.univ.filter fun a => (PositivityTheory.Rg.Sw.sgn ε a).re < 0) = Finset.univ.filter fun a => ε a = false := by
      apply Finset.filter_congr
      intro a _
      simp only [PositivityTheory.Rg.Sw.sgn]
      cases ε a <;> norm_num
    rw [e1, e2]
    exact ⟨hp, hq⟩
  have hsig : ∀ φ : D.host.E →+* ℂ, k ≤ posIndex (V.gram.map φ) ∧ k ≤ negIndex (V.gram.map φ) := by
    intro φ
    obtain ⟨τ0, h | h⟩ := Formalism.L2.Fam.ThC.tauE_or (D := D) φ
    · rw [← h]; exact hsigτ τ0
    · have hφ : φ = ComplexEmbedding.conjugate (tauE D τ0) := by rw [h]; exact (star_star φ).symm
      rw [hφ, posIndex_map_conjugate _ hT, negIndex_map_conjugate _ hT]
      exact hsigτ τ0
  have hsigT : ∀ φ : D.host.E →+* ℂ, k ≤ posIndex (V.gramᵀ.map φ) ∧ k ≤ negIndex (V.gramᵀ.map φ) := by
    intro φ
    have hm : V.gramᵀ.map φ = V.gram.map (ComplexEmbedding.conjugate φ) := by
      rw [hTt]
      ext a b
      simp only [Matrix.map_apply]
      exact WLt.emb_cc φ _
    rw [hm]
    exact hsig _
  obtain ⟨W, hWr, hW⟩ := WLt.main_iso k V.gramᵀ hG hd (by simpa using hk) hsigT
  rw [← GlobalTheory.SiegelWeilLitCompare.wittIdx_eq]
  refine le_csSup ⟨V.rank, ?_⟩ ⟨W, fun x hx y hy => ?_, hWr⟩
  · rintro r ⟨W', -, rfl⟩
    exact (Submodule.finrank_le W').trans (by simp)
  · have h := hW y hy x hx
    simp only [WLt.hf, dotProduct, mulVec, Function.comp_apply] at h
    show ∑ i, ∑ j, FD.cc (x i) * V.gram i j * y j = 0
    rw [Finset.sum_comm, ← h]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    show FD.cc (x b) * V.gram b a * y a = y a * (V.gram b a * FD.cc (x b))
    ring

end PositivityTheory.Rg.Sw.Glob

end
end

section
noncomputable section

open scoped Matrix ComplexConjugate nonZeroDivisors
open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.WEq

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

local notation "hermF" => ReciprocityTheory.ChartRestriction.G.FD.herm
local notation "ccF" => ReciprocityTheory.ChartRestriction.G.FD.cc

def dSgn (r k : ℕ) : Matrix (Fin r) (Fin r) E := Matrix.diagonal fun a => if (a : ℕ) < k then 1 else -1

theorem dSgn_hermF (r k : ℕ) (a b : Fin r) : ccF (dSgn (E := E) r k a b) = dSgn r k b a := by
  by_cases h : a = b
  · subst h
    simp only [dSgn, Matrix.diagonal_apply_eq, ReciprocityTheory.ChartRestriction.G.FD.cc]
    split_ifs <;> simp
  · simp [dSgn, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h), ReciprocityTheory.ChartRestriction.G.FD.cc]

theorem dSgn_det (k : ℕ) : (dSgn (E := E) r k).det ≠ 0 := by
  rw [dSgn, Matrix.det_diagonal, Finset.prod_ne_zero_iff]
  intro a _
  split_ifs <;> norm_num

theorem mem_one_iff_isIntegral (z : E) : z ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ IsIntegral ℤ z := by
  rw [FractionalIdeal.mem_one_iff, IsIntegralClosure.isIntegral_iff (A := 𝓞 E)]

theorem cc_isIntegral {z : E} (h : IsIntegral ℤ z) : IsIntegral ℤ (cc z) :=
  h.map (IsCMField.complexConj E : E →+* E).toIntAlgHom

theorem herm_diag (d : Fin r → E) (x y : Fin r → E) :
    hermF (Matrix.diagonal d) x y = ∑ a, x a * d a * ccF (y a) := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem mem_stdLat_iff_forall_isIntegral (n : ℕ) (x : Fin n → E) :
    x ∈ GlobalTheory.InertWitt.stdLat E n ↔ ∀ i, IsIntegral ℤ (x i) := by
  constructor
  · rintro ⟨w, rfl⟩ i
    exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mpr ⟨w i, rfl⟩
  · intro h
    choose w hw using fun i => (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp (h i)
    exact ⟨w, funext fun i => hw i⟩

private theorem isIntegral_ite_one_neg_one (k : ℕ) (a : Fin r) : IsIntegral ℤ (if (a : ℕ) < k then (1 : E) else -1) := by
  split_ifs
  · exact isIntegral_one
  · exact isIntegral_one.neg

theorem mod_std (k : ℕ) (x : Fin r → E) : x ∈ GlobalTheory.InertWitt.stdLat E r ↔
    ∀ y ∈ GlobalTheory.InertWitt.stdLat E r, hermF (dSgn r k) x y ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [mem_stdLat_iff_forall_isIntegral]
  constructor
  · intro hx y hy
    rw [mem_stdLat_iff_forall_isIntegral] at hy
    rw [mem_one_iff_isIntegral, dSgn, herm_diag]
    exact IsIntegral.sum _ fun a _ => ((hx a).mul (isIntegral_ite_one_neg_one k a)).mul (cc_isIntegral (hy a))
  · intro h i
    have hy : (Pi.single i 1 : Fin r → E) ∈ GlobalTheory.InertWitt.stdLat E r := by
      rw [mem_stdLat_iff_forall_isIntegral]
      intro j
      by_cases hj : j = i
      · subst hj; simpa using isIntegral_one
      · simpa [Pi.single_apply, hj] using isIntegral_zero
    have h1 := h _ hy
    rw [mem_one_iff_isIntegral, dSgn, herm_diag] at h1
    have h2 : IsIntegral ℤ (x i * (if (i : ℕ) < k then (1 : E) else -1)) := by
      convert h1 using 1
      rw [Finset.sum_eq_single i]
      · simp [ReciprocityTheory.ChartRestriction.G.FD.cc]
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · simp
    have h3 := h2.mul (isIntegral_ite_one_neg_one k i)
    have h4 : x i * (if (i : ℕ) < k then (1 : E) else -1) * (if (i : ℕ) < k then (1 : E) else -1) = x i := by
      split_ifs <;> ring
    rwa [h4] at h3

def ext {k : ℕ} (hr : 2 * k = r) (u : Fin k → E) : Fin r → E := fun a =>
  if h : (a : ℕ) < k then u ⟨a, h⟩ else u ⟨a - k, by have := a.isLt; omega⟩

def extL {k : ℕ} (hr : 2 * k = r) : (Fin k → E) →ₗ[E] (Fin r → E) where
  toFun := ext hr
  map_add' u v := by funext a; simp only [ext, Pi.add_apply]; split_ifs <;> rfl
  map_smul' c u := by funext a; simp only [ext, Pi.smul_apply, RingHom.id_apply]; split_ifs <;> rfl

theorem extL_injective {k : ℕ} (hr : 2 * k = r) : Function.Injective (extL (E := E) hr) := by
  intro u v h
  funext i
  have := congrFun h ⟨i, by omega⟩
  simpa [extL, ext, i.isLt] using this

theorem herm_ext {k : ℕ} (hr : 2 * k = r) (u v : Fin k → E) :
    hermF (dSgn r k) (ext hr u) (ext hr v) = 0 := by
  rw [dSgn, herm_diag]
  subst hr
  rw [← Equiv.sum_comp (finCongr (two_mul k).symm), Fin.sum_univ_add]
  simp [ext, Matrix.diagonal_apply_eq]

end Gen

end PositivityTheory.Rg.Sw.Glob.WEq
end
end

section
noncomputable section

open scoped Matrix ComplexConjugate nonZeroDivisors
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.WEq

local notation "hermF" => ReciprocityTheory.ChartRestriction.G.FD.herm
local notation "ccF" => ReciprocityTheory.ChartRestriction.G.FD.cc

theorem coord_hT (D : D7) [IsCMField D.host.E] (hst : ∀ z : D.host.E, star z = IsCMField.complexConj D.host.E z)
    (V : HSp D) (x y : Fin V.rank → D.host.E) :
    V.hT (V.frame.equivFun.symm y) (V.frame.equivFun.symm x) = hermF (V.gram)ᵀ x y := by
  simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, Matrix.transpose_apply, HSpace.gram, ReciprocityTheory.ChartRestriction.G.FD.cc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [starRingEnd_apply, hst]
  ring

theorem perm_exists {r k : ℕ} (hk : k ≤ r) (ε : Fin r → Bool) (he : cnt ε true = k) :
    ∃ π : Equiv.Perm (Fin r), ∀ a, ε a = decide (((π a : Fin r) : ℕ) < k) := by
  classical
  have c1 : Fintype.card {a // ε a = true} = Fintype.card {a : Fin r // (a : ℕ) < k} := by
    rw [Fintype.card_subtype]
    have e : {a : Fin r // (a : ℕ) < k} ≃ Fin k :=
      ⟨fun a => ⟨a, a.2⟩, fun i => ⟨⟨i, by omega⟩, i.2⟩, fun _ => rfl, fun _ => rfl⟩
    rw [Fintype.card_congr e, Fintype.card_fin]
    exact he
  have c2 : Fintype.card {a // ¬ ε a = true} = Fintype.card {a : Fin r // ¬ (a : ℕ) < k} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, c1]
  let e1 := Fintype.equivOfCardEq c1
  let e2 := Fintype.equivOfCardEq c2
  refine ⟨(Equiv.sumCompl (fun a => ε a = true)).symm.trans
    ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl (fun a : Fin r => (a : ℕ) < k))), fun a => ?_⟩
  by_cases h : ε a = true
  · rw [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos (p := fun a => ε a = true) h, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.sumCompl_apply_inl, h]
    exact (decide_eq_true (e1 ⟨a, h⟩).2).symm
  · rw [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg (p := fun a => ε a = true) h, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.sumCompl_apply_inr]
    simp only [Bool.not_eq_true] at h
    rw [h]
    exact (decide_eq_false (e2 ⟨a, by simp [h]⟩).2).symm

theorem wittLBeq : WittLBeq := by
  intro D V k hk hS
  letI hcm : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ z : D.host.E, star z = IsCMField.complexConj D.host.E z := fun _ => rfl
  set r := V.rank with hrdef
  set G₁ : Matrix (Fin r) (Fin r) D.host.E := (V.gram)ᵀ with hG₁
  let v : (Fin r → D.host.E) ≃ₗ[D.host.E] V.V := V.frame.equivFun.symm
  let L : Submodule (𝓞 D.host.E) (Fin r → D.host.E) :=
    V.L0.map ((V.frame.equivFun : V.V →ₗ[D.host.E] (Fin r → D.host.E)).restrictScalars (𝓞 D.host.E))
  have memL : ∀ x, x ∈ L ↔ v x ∈ V.L0 := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [v] using hy
    · intro hx
      exact ⟨v x, hx, V.frame.equivFun.apply_symm_apply x⟩
  have hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L := by
    refine ⟨V.standardTuple_isLattice.fg.map _, ?_⟩
    have hc : (L : Set (Fin r → D.host.E)) = V.frame.equivFun '' (V.L0 : Set V.V) := by
      ext x; simp [L]
    rw [hc, show (⇑V.frame.equivFun : V.V → (Fin r → D.host.E)) =
        ⇑(V.frame.equivFun : V.V →ₗ[D.host.E] (Fin r → D.host.E)) from rfl, Submodule.span_image,
      V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]
  have hone : ∀ z : D.host.E, z ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) ↔
      z ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    intro z
    rw [Submodule.mem_one, FractionalIdeal.mem_one_iff]
  have hdual : ∀ z : V.V, z ∈ V.L0 ↔ ∀ y ∈ V.L0, V.hT y z ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    intro z
    have hu := V.baseLattice_isUnimodular
    unfold Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual at hu
    conv_lhs => rw [← hu]
    simp [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
  have hmod : ∀ x, x ∈ L ↔ ∀ y ∈ L, hermF G₁ x y ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    intro x
    rw [memL, hdual]
    constructor
    · intro h y hy
      rw [← coord_hT D hst V x y, ← hone]
      exact h _ ((memL y).1 hy)
    · intro h y' hy'
      have hy : V.frame.equivFun y' ∈ L := (memL _).2 (by simpa [v] using hy')
      have := h _ hy
      rw [← coord_hT D hst V x _, ← hone] at this
      simpa [v] using this
  have hG : ∀ a b, ccF (G₁ a b) = G₁ b a := by
    intro a b
    have := V.herm.eq (V.frame b) (V.frame a)
    simp only [hG₁, Matrix.transpose_apply, HSpace.gram, ReciprocityTheory.ChartRestriction.G.FD.cc]
    rw [← hst]
    exact this
  have hd : G₁.det ≠ 0 := by rw [hG₁, Matrix.det_transpose]; exact GlobalTheory.MassLinkSD.gram_det_ne V
  have key : ∀ ρ : D.what₂.Tau, ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      (dSgn r k).map (tauE D ρ) = Qᵀ * G₁.map (tauE D ρ) * Q.map (starRingEnd ℂ) := by
    intro ρ
    obtain ⟨ε, fr, hfr, hdiag, hk1, hk2⟩ := hS ρ
    have hc := cnt_add ε
    obtain ⟨π, hπ⟩ := perm_exists (r := r) (k := k) (by omega) ε (by omega)
    let X : Matrix (Fin r) (Fin r) ℂ := (π.symm.toPEquiv).toMatrix
    have hX : X.det ≠ 0 := by
      simp only [X, Matrix.det_permutation]
      rcases Int.units_eq_one_or (Equiv.Perm.sign π.symm) with h | h <;> simp [h]
    have hfr' : fr.det ≠ 0 := hfr.ne_zero
    have hT' : (frᴴ)ᵀ = fr.map (starRingEnd ℂ) := by
      ext i j; simp [Matrix.conjTranspose_apply]
    have h1 : ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) G₁ fr = Matrix.diagonal (sgn ε) := by
      rw [GlobalTheory.Published.gram_eq, hG₁, Matrix.transpose_map]
      have e : (HSpace.gram V).map (tauE D ρ) = gramAt D V ρ := rfl
      rw [e]
      have := congrArg Matrix.transpose hdiag
      rw [Matrix.diagonal_transpose, Matrix.transpose_mul, Matrix.transpose_mul, hT', ← Matrix.mul_assoc] at this
      exact this
    have h2 : ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (dSgn r k) X = Matrix.diagonal (sgn ε) := by
      have hXc : X.map (starRingEnd ℂ) = X := by
        ext i j; simp only [X, Matrix.map_apply, PEquiv.toMatrix_apply]; split_ifs <;> simp
      have hXt : Xᵀ = π.toPEquiv.toMatrix := by
        simp only [X]
        rw [← PEquiv.toMatrix_symm, ← Equiv.toPEquiv_symm, Equiv.symm_symm]
      rw [GlobalTheory.Published.gram_eq, hXc, hXt, PEquiv.toMatrix_toPEquiv_mul]
      simp only [X]
      rw [PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm, Matrix.submatrix_submatrix, dSgn,
        Matrix.diagonal_map (map_zero _), Function.comp_id, Function.id_comp, Matrix.submatrix_diagonal_equiv]
      congr 1
      funext a
      have ha := hπ a
      simp only [Function.comp_apply, sgn]
      rw [ha]
      by_cases h : ((π a : Fin r) : ℕ) < k <;> simp [h]
    exact GlobalTheory.Published.Landherr.congr_of_gram_eq (G := G₁) (G' := dSgn r k) (tauE D ρ) hfr' hX (h1.trans h2.symm)
  have hs : ∀ σ : D.host.E →+* ℂ, ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      (dSgn r k).map σ = Qᵀ * G₁.map σ * Q.map (starRingEnd ℂ) := by
    intro σ
    by_cases h : ∃ ρ, tauE D ρ = NumberField.ComplexEmbedding.conjugate σ
    · obtain ⟨ρ, hρ⟩ := h
      have := GlobalTheory.Published.Landherr.congr_conjugate (G := G₁) (G' := dSgn r k) (tauE D ρ) (key ρ)
      rw [hρ, NumberField.ComplexEmbedding.involutive_conjugate D.host.E σ] at this
      exact this
    · obtain ⟨ρ, hρ⟩ := (GlobalTheory.PointAtPlace.tauE_cm σ).2 h
      rw [← hρ]
      exact key ρ
  have hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice (GlobalTheory.InertWitt.stdLat D.host.E r) :=
    ⟨(GlobalTheory.InertWitt.stdLat_isLattice D.host.E r).fg, (GlobalTheory.InertWitt.stdLat_isLattice D.host.E r).span_eq_top⟩
  have hcc : ∀ z ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E),
      ccF z ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    intro z hz
    rw [mem_one_iff_isIntegral] at hz ⊢
    exact cc_isIntegral hz
  haveI : Algebra.Unramified (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) :=
    Formalism.L2.Pj.unramBridge D.host.E (Formalism.L2.Pj.cmUnram_conj D)
  obtain ⟨P, hP, hPG⟩ := GlobalTheory.SelfDualGenus.congr_of_modular (G := G₁) (G' := dSgn r k) (L := L)
    (L' := GlobalTheory.InertWitt.stdLat D.host.E r) (𝔟 := 1)
    (GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt) GlobalTheory.QNorm.hasseNormSt one_ne_zero hcc hG
    (fun a b => dSgn_hermF (r := r) (k := k) a b) hd (dSgn_det (r := r) (k := k)) hL hL' hmod
    (mod_std (r := r) (k := k)) hs
  let f : (Fin k → D.host.E) →ₗ[D.host.E] V.V := v.toLinearMap ∘ₗ P.mulVecLin ∘ₗ extL hk
  have hPi : Function.Injective P.mulVecLin := by
    have hu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2 (isUnit_iff_ne_zero.2 hP)
    simpa [Matrix.coe_mulVecLin] using (Matrix.mulVec_injective_iff_isUnit.2 hu)
  have hf : Function.Injective f := v.injective.comp (hPi.comp (extL_injective hk))
  have hfin : Module.finrank D.host.E (LinearMap.range f) = k := by
    rw [LinearMap.finrank_range_of_inj hf, Module.finrank_fin_fun]
  have hiso : ∀ x ∈ LinearMap.range f, ∀ y ∈ LinearMap.range f, V.hT x y = 0 := by
    rintro _ ⟨u, rfl⟩ _ ⟨u', rfl⟩
    show V.hT (v (P *ᵥ ext hk u)) (v (P *ᵥ ext hk u')) = 0
    rw [coord_hT D hst V, GlobalTheory.SelfDualGenus.herm_mulVec, ← hPG, herm_ext]
  unfold Formalism.MainNotions.SchurIrreducible.wittIdx
  refine le_csSup ⟨Module.finrank D.host.E V.V, ?_⟩ ⟨LinearMap.range f, hfin, hiso⟩
  rintro d ⟨W, rfl, -⟩
  exact Submodule.finrank_le W

end PositivityTheory.Rg.Sw.Glob.WEq

namespace PositivityTheory.Rg.Sw.Glob

theorem wittLBeq : WittLBeq := WEq.wittLBeq

end PositivityTheory.Rg.Sw.Glob
end
end

section
namespace PositivityTheory.Rg.Sw.Glob

theorem sigOK : SigOK := sigOK_of wittLBlt wittLBeq

end PositivityTheory.Rg.Sw.Glob
end
