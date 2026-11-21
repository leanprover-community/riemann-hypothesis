import Development.EtaleCohomology.DivisorCycles.CycleCount
import Development.EtaleCohomology.DivisorCycles.SpecPtPf
import Development.EtaleCohomology.DivisorCycles.OpenCoset
import Development.EtaleCohomology.DivisorCycles.DegPoly2
import Development.EtaleCohomology.DivisorCycles.FinStruct
import Development.EtaleCohomology.DivisorCycles.FinKey
import Development.EtaleCohomology.DivisorCycles.FinBigCorner
import Development.EtaleCohomology.DivisorCycles.SemisPf
import Development.EtaleCohomology.DivisorCycles.MatUnitsOf
import Development.EtaleCohomology.DivisorCycles.FinRep
import Development.EtaleCohomology.DivisorCycles.FinDenseAlg
import Development.EtaleCohomology.DivisorCycles.SepPolyProof
import Development.EtaleCohomology.DivisorCycles.ChainPf
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CosetOfCover
import Development.EtaleCohomology.DivisorCycles.FinFinEmbed

section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb

open Polynomial in

def DivPlus : Prop :=
  ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (K K' : Type) [Field K] [IsAlgClosed K] [CharZero K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] [Field K'] [IsAlgClosed K'] [Algebra K K']
    (N n : ℕ) (ρ : Γ →* GL (Fin N) K),
      Continuous (fun g : Γ => (ρ g : Matrix (Fin N) (Fin N) K)) → IsSSMat ρ →
    ∀ (S : Set Γ), Dense S →
    ∀ (P : Γ → K[X]), (∀ s ∈ S, (P s).Monic ∧ (P s).natDegree = n) →
      (∀ s ∈ S, aeval (ρ s : Matrix (Fin N) (Fin N) K) (P s) = 0) →
    ∀ (X : Matrix (Fin N) (Fin N) K'), InLieZar ρ X →
      (∃ e : Fin n → K', Function.Injective e ∧ IsLac e ∧ ∀ i, X.charpoly.IsRoot (e i)) →
    ∀ (ψ : Γ →* Kˣ), Continuous (fun g : Γ => ((ψ g : Kˣ) : K)) →
      (∀ s ∈ S, ((ψ s : Kˣ) : K) = (-1) ^ n * (P s).coeff 0) →
    ∃ r : Γ →* GL (Fin n) K,
      Continuous (fun g : Γ => (r g : Matrix (Fin n) (Fin n) K)) ∧ IsSSMat r ∧
      (∃ A : Matrix (Fin N) (Fin n) K, A.rank = n ∧
        ∀ g : Γ, (ρ g : Matrix (Fin N) (Fin N) K) * A = A * (r g : Matrix (Fin n) (Fin n) K)) ∧
      (∀ g : Γ, aeval (ρ g : Matrix (Fin N) (Fin N) K) (r g : Matrix (Fin n) (Fin n) K).charpoly = 0) ∧
      (∀ s ∈ S, aeval (r s : Matrix (Fin n) (Fin n) K) (P s) = 0) ∧
      (∀ g : Γ, ((r g : Matrix (Fin n) (Fin n) K).det) = ((ψ g : Kˣ) : K)) ∧
      IsOpen {g : Γ | (r g : Matrix (Fin n) (Fin n) K).charpoly.Separable} ∧
      Dense {g : Γ | (r g : Matrix (Fin n) (Fin n) K).charpoly.Separable} ∧
      (∀ s ∈ S, (r s : Matrix (Fin n) (Fin n) K).charpoly.Separable →
        (r s : Matrix (Fin n) (Fin n) K).charpoly = P s) ∧
      (∀ s ∈ S, ProdGen n (P s) → (r s : Matrix (Fin n) (Fin n) K).charpoly = P s) ∧
      ∃ (k : ℕ) (T : Fin k → Matrix (Fin n) (Fin N) K) (T' : Fin k → Matrix (Fin N) (Fin n) K),
        (∀ j g, T j * (ρ g : Mat K N) = (r g : Mat K n) * T j) ∧
        (∀ j g, (ρ g : Mat K N) * T' j = T' j * (r g : Mat K n)) ∧ ∑ j, T' j * T j = 1

theorem plus_of (hSpec : SpecLie) (hDeg : DegAll) (hStruct : Struct) (hKey : Key) (hBig : BigCorner)
    (hSemis : Semis) (hMU : MatrixUnits₂) (hRep : Rep) (hDA : DenseAlg) (hSub : FinSub) (hFD : FinDense)
    (hFP : FinPoly) (hEm : FinEmbed) : DivPlus := by
  intro Γ _ _ _ _ K K' _ _ _ _ _ _ _ _ _ N n ρ hρ hss S hS P hP hk X hX he ψ hψ hψS
  obtain ⟨e, -, hL, hr⟩ := he
  obtain ⟨X₀, e₀, hX₀, hL₀, hr₀⟩ := hSpec Γ K K' N n ρ X e hX hL hr
  have hd : ∀ g, Deg n (ρ g : Mat K N) := hDeg Γ K N n ρ hρ S hS fun s hs =>
    ⟨P s, (hP s hs).1.ne_zero, (hP s hs).2.le, hk s hs⟩
  obtain ⟨p, hG⟩ := hStruct Γ K N n ρ X₀ e₀ hss hd hX₀ hL₀ hr₀
  have key := hKey Γ K N n ρ e₀ p hd hL₀ hG
  obtain ⟨hsys, -, hC, -, hN, hK, -⟩ := hG
  obtain ⟨R, hR, hRC, hRN, hRK⟩ := hBig Γ K N n ρ (env ρ) p hC hN hK
    fun g => (key ⊤ inferInstance inferInstance g).2
  obtain ⟨E, hE⟩ := hMU K N n R p hsys hRC (hSemis Γ K N ρ R hss hRN hRK)
  obtain ⟨r, A, B, hsub⟩ := hRep Γ K N n ρ R p E hsys hE hR
  obtain ⟨h1, h2, h3, h4⟩ := hSub Γ K N n ρ r A B hsub hss
  have hc : Continuous (fun g => (r g : Mat K n)) := by
    simp only [h3]
    exact (continuous_const.matrix_mul hρ).matrix_mul continuous_const
  obtain ⟨ho, hD⟩ := hFD Γ K n r hc fun U hU hf g => by
    obtain ⟨m, hm, hE⟩ := (key U hU hf g).1
    exact hDA Γ K N n ρ r A B hsub U g m hm hE
  have hkr : ∀ s ∈ S, Polynomial.aeval (r s : Mat K n) (P s) = 0 := fun s hs => (h4 s _).1 (hk s hs)
  have hsep : ∀ s ∈ S, (r s : Mat K n).charpoly.Separable → (r s : Mat K n).charpoly = P s := fun s hs =>
    (hFP K n _ _ (hP s hs).1 (hP s hs).2 (hkr s hs)).1
  have hdet : ∀ g, (r g : Mat K n).det = ((ψ g : Kˣ) : K) := by
    have := Continuous.ext_on (hS.inter_of_isOpen_right hD ho) hc.matrix_det hψ (fun s hs => by
      show (r s : Mat K n).det = _
      rw [hψS s hs.1, Matrix.det_eq_sign_charpoly_coeff, hsep s hs.1 hs.2, Fintype.card_fin])
    exact fun g => congrFun this g
  refine ⟨r, hc, h1, ⟨A, h2, hsub.2.1⟩, fun g => (h4 g _).2 (Matrix.aeval_self_charpoly _), hkr, hdet, ho, hD,
    hsep, fun s hs hg => (hFP K n _ _ (hP s hs).1 (hP s hs).2 (hkr s hs)).2 hg ?_, hEm Γ K N n ρ r A B hsub hss h1⟩
  rw [hdet, hψS s hs]

end LateralTheory.DivDb
end

section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb

theorem goal_of (hSpec : SpecLie) (hDeg : DegAll) (hStruct : Struct) (hKey : Key) (hBig : BigCorner)
    (hSemis : Semis) (hMU : MatrixUnits₂) (hRep : Rep) (hDA : DenseAlg) (hSub : FinSub) (hFD : FinDense)
    (hFP : FinPoly) (hEm : FinEmbed) : DivWCoreLac := by
  intro Γ _ _ _ _ K K' _ _ _ _ _ _ _ _ _ N n ρ hρ hss S hS P hP hk X hX he ψ hψ hψS
  obtain ⟨r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, k, T, T', hT, -, hs⟩ :=
    plus_of hSpec hDeg hStruct hKey hBig hSemis hMU hRep hDA hSub hFD hFP hEm
      Γ K K' N n ρ hρ hss S hS P hP hk X hX he ψ hψ hψS
  refine ⟨r, h1, h2, h3, ⟨k, Matrix.of fun q a => T q.2 q.1 a, ?_, fun g => ?_⟩, h4, h5, h6, h7, h8, h9, h10⟩
  · have hC : (Matrix.of fun a (q : Fin n × Fin k) => T' q.2 a q.1) *
        (Matrix.of fun (q : Fin n × Fin k) a => T q.2 q.1 a) = 1 := by
      rw [← hs]; ext a b
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.sum_apply, Fintype.sum_prod_type_right]
    refine le_antisymm ((Matrix.rank_le_card_width _).trans (by simp)) ?_
    have := Matrix.rank_mul_le_right (Matrix.of fun a (q : Fin n × Fin k) => T' q.2 a q.1)
      (Matrix.of fun (q : Fin n × Fin k) a => T q.2 q.1 a)
    rw [hC] at this
    simpa using this
  · ext ⟨i, j⟩ a
    have := congrFun (congrFun (hT j g) i) a
    simp only [Matrix.mul_apply] at this
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, this]

end LateralTheory.DivDb
end

section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.SpecLiePf
open LateralTheory.DivDb

theorem SpecLie_of (hS : SpecPt) : SpecLie := by
  intro Γ K K' _ _ _ _ _ N n ρ X e hX hL hR
  classical
  let x : (Fin N × Fin N) ⊕ Fin n → K' := Sum.elim (fun p => X p.1 p.2) e
  let gAB : Finset (Fin n) → Finset (Fin n) → MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K := fun A B =>
    MvPolynomial.C (B.card : K) * ∑ i ∈ A, MvPolynomial.X (Sum.inr i) -
      MvPolynomial.C (A.card : K) * ∑ i ∈ B, MvPolynomial.X (Sum.inr i)
  let G : Set (MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K) :=
    {g | ∃ A B : Finset (Fin n), A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ g = gAB A B}
  have hGf : G.Finite :=
    (Set.finite_range (fun AB : Finset (Fin n) × Finset (Fin n) => gAB AB.1 AB.2)).subset
      (by rintro g ⟨A, B, -, -, -, rfl⟩; exact ⟨(A, B), rfl⟩)
  have haG : ∀ g ∈ G, MvPolynomial.aeval x g ≠ 0 := by
    rintro g ⟨A, B, hA, hB, hAB, rfl⟩
    simp only [gAB, map_sub, map_mul, map_sum, MvPolynomial.aeval_X, x, Sum.elim_inr, map_natCast]
    exact sub_ne_zero.mpr (hL A B hA hB hAB)
  obtain ⟨y, hy, hyG⟩ := hS K K' _ x G hGf haG
  refine ⟨Matrix.of fun a b => y (Sum.inl (a, b)), fun i => y (Sum.inr i), ?_, ?_, ?_⟩
  · change ∀ f ∈ Van (img ρ ⊤ : Set (Mat K N)), dAt f 1 _ = 0
    intro f hf
    have hf' : ∀ g : Γ, MvPolynomial.eval (fun p : Fin N × Fin N => (ρ g : Matrix (Fin N) (Fin N) K) p.1 p.2) f = 0 :=
      fun g => hf _ ⟨g, trivial, rfl⟩
    have h0 := hX f hf'
    let L : MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K := ∑ p : Fin N × Fin N,
      MvPolynomial.C (MvPolynomial.eval (fun q : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) K) q.1 q.2)
        (MvPolynomial.pderiv p f)) * MvPolynomial.X (Sum.inl p)
    have hxL : MvPolynomial.aeval x L = 0 := by
      simpa only [L, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, x, Sum.elim_inl] using h0
    have h1 := hy L hxL
    simpa only [L, dAt, ev, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.of_apply] using h1
  · intro A B hA hB hAB
    have h1 := hyG _ ⟨A, B, hA, hB, hAB, rfl⟩
    simp only [gAB, map_sub, map_mul, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X] at h1
    exact sub_ne_zero.mp h1
  · intro i
    let M : Matrix (Fin N) (Fin N) (MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K) :=
      Matrix.scalar (Fin N) (MvPolynomial.X (Sum.inr i)) - Matrix.of (fun a b => MvPolynomial.X (Sum.inl (a, b)))
    have hx : MvPolynomial.aeval x M.det = 0 := by
      have e1 : MvPolynomial.aeval x M.det = ((MvPolynomial.aeval x).toRingHom.mapMatrix M).det := by
        rw [← RingHom.map_det]; rfl
      have e2 : (MvPolynomial.aeval x).toRingHom.mapMatrix M = Matrix.scalar (Fin N) (e i) - X := by
        ext a b
        by_cases h : a = b
        · subst h; simp [M, x]
        · simp [M, x, h]
      rw [e1, e2, ← Matrix.eval_charpoly]; exact hR i
    have h1 := hy _ hx
    have e1 : MvPolynomial.eval y M.det = ((MvPolynomial.eval y).mapMatrix M).det := by
      rw [← RingHom.map_det]
    have e2 : (MvPolynomial.eval y).mapMatrix M =
        Matrix.scalar (Fin N) (y (Sum.inr i)) - Matrix.of (fun a b => y (Sum.inl (a, b))) := by
      ext a b
      by_cases h : a = b
      · subst h; simp [M]
      · simp [M, h]
    rw [e1, e2] at h1
    change Polynomial.eval (y (Sum.inr i)) (Matrix.charpoly (Matrix.of fun a b => y (Sum.inl (a, b)))) = 0
    rw [Matrix.eval_charpoly]; exact h1

end LateralTheory.DivDb.SpecLiePf
end

section
namespace LateralTheory.Fin.SpecLie
theorem etale_special_point_exists_of_key : LateralTheory.DivDb.SpecPt := by
  apply LateralTheory.DivDb.SpecPtPf.SpecPt_of
theorem etale_spectrum_lie_algebra_instance : LateralTheory.DivDb.SpecLie := by
  apply LateralTheory.DivDb.SpecLiePf.SpecLie_of <;> first | exact etale_special_point_exists_of_key
theorem intersectionNumber_baseChange : LateralTheory.DivDb.SpecLie := etale_spectrum_lie_algebra_instance
end LateralTheory.Fin.SpecLie
end

section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.DegAll₂
open LateralTheory.DivDb

theorem entries_cont {Γ K : Type} [TopologicalSpace Γ] [TopologicalSpace K] {N : ℕ}
    {φ : Γ → Mat K N} (hφ : Continuous φ) :
    Continuous (fun g => fun p : Fin N × Fin N => φ g p.1 p.2) :=
  continuous_pi fun p => (hφ.matrix_elem p.1 p.2)

theorem poly_cont {Γ K : Type} [TopologicalSpace Γ] [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] {N : ℕ} {φ : Γ → Mat K N} (hφ : Continuous φ) (f : MP K N) :
    Continuous (fun g => MvPolynomial.aeval (fun p : Fin N × Fin N => φ g p.1 p.2) f) := by
  refine ((MvPolynomial.continuous_eval f).comp (entries_cont hφ)).congr ?_
  intro g
  rw [MvPolynomial.aeval_eq_eval₂Hom, Algebra.algebraMap_self]
  rfl

end LateralTheory.DivDb.DegAll₂

namespace LateralTheory.DivDb

theorem DegAll_of (hP : DegPoly) : DegAll := by
  intro Γ K _ _ _ _ _ _ N n ρ hρ S hS hSd g
  obtain ⟨𝓕, h𝓕⟩ := hP K N n
  rw [h𝓕 K]
  intro f hf
  have key := Continuous.ext_on hS (DegAll₂.poly_cont hρ f) continuous_const
    (fun s hs => ((h𝓕 K _).1 (hSd s hs)) f hf)
  exact congrFun key g

end LateralTheory.DivDb
end

section
namespace LateralTheory.Fin.DegAll
theorem etale_degree_polynomial_bound : LateralTheory.DivDb.DegPoly := by
  apply LateralTheory.DivDb.DegPoly₂.DegPoly_of
theorem etale_rep_image_degree_bound_all_holds_assembled : LateralTheory.DivDb.DegAll := by
  apply LateralTheory.DivDb.DegAll_of <;> first | exact etale_degree_polynomial_bound
theorem intersectionNumber_baseChange : LateralTheory.DivDb.DegAll := etale_rep_image_degree_bound_all_holds_assembled
end LateralTheory.Fin.DegAll
end

section
namespace LateralTheory.Fin.Semis
theorem etale_semisimplicity_instance : LateralTheory.DivDb.Semis := by
  apply LateralTheory.DivDb.SemisPf.Semis_of
theorem intersectionNumber_baseChange : LateralTheory.DivDb.Semis := etale_semisimplicity_instance
end LateralTheory.Fin.Semis
end

section
namespace LateralTheory.Fin.MatrixUnits₂
theorem etale_matrix_units_system_of_key : LateralTheory.DivDb.MatrixUnits₂ := by
  apply LateralTheory.DivDb.MatrixUnitConstruction.MatUnits_of
theorem intersectionNumber_baseChange : LateralTheory.DivDb.MatrixUnits₂ := etale_matrix_units_system_of_key
end LateralTheory.Fin.MatrixUnits₂
end

section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.FiniteSubrepresentation

variable {K : Type} [Field K] {N n : ℕ}

theorem pow_tw (X : Matrix (Fin N) (Fin N) K) (Y : Matrix (Fin n) (Fin n) K) (T : Matrix (Fin N) (Fin n) K)
    (h : X * T = T * Y) (k : ℕ) : X ^ k * T = T * Y ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

theorem aeval_tw (X : Matrix (Fin N) (Fin N) K) (Y : Matrix (Fin n) (Fin n) K) (T : Matrix (Fin N) (Fin n) K)
    (h : X * T = T * Y) (q : Polynomial K) : Polynomial.aeval X q * T = T * Polynomial.aeval Y q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, smul_mul_assoc, one_mul, one_mul, Matrix.smul_mul,
      Matrix.mul_smul, pow_tw X Y T h]

end LateralTheory.DivDb.FiniteSubrepresentation

theorem LateralTheory.DivDb.FiniteSubrepresentation.FinSub_of : LateralTheory.DivDb.FinSub := by
  intro Γ K _ _ N n ρ r A B hS hρ
  obtain ⟨hBA, hAr, hspan⟩ := hS
  have hinj : ∀ w : Fin n → K, A *ᵥ w = 0 → w = 0 := by
    intro w hw
    have := congrArg (B *ᵥ ·) hw
    simpa [Matrix.mulVec_mulVec, hBA] using this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro W hW
    obtain ⟨W'', hc, hs⟩ := hρ (W.map (Matrix.mulVecLin A)) (by
      rintro g _ ⟨w, hw, rfl⟩
      refine ⟨(r g : Matrix (Fin n) (Fin n) K) *ᵥ w, hW g w hw, ?_⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hAr g])
    refine ⟨W''.comap (Matrix.mulVecLin A), ?_, ?_⟩
    · constructor
      · rw [Submodule.disjoint_def]
        intro w hw hw'
        apply hinj
        have h1 : A *ᵥ w ∈ W.map (Matrix.mulVecLin A) := ⟨w, hw, rfl⟩
        exact (Submodule.disjoint_def.mp hc.disjoint) _ h1 hw'
      · rw [codisjoint_iff, eq_top_iff]
        intro v _
        have hv : A *ᵥ v ∈ W.map (Matrix.mulVecLin A) ⊔ W'' := by rw [hc.sup_eq_top]; trivial
        obtain ⟨y, ⟨w, hw, rfl⟩, z, hz, hyz⟩ := Submodule.mem_sup.mp hv
        rw [Submodule.mem_sup]
        refine ⟨w, hw, v - w, ?_, by abel⟩
        show A *ᵥ (v - w) ∈ W''
        rw [Matrix.mulVec_sub, ← hyz]
        simpa [Matrix.mulVecLin_apply] using hz
    · intro g v hv
      show A *ᵥ ((r g : Matrix (Fin n) (Fin n) K) *ᵥ v) ∈ W''
      rw [Matrix.mulVec_mulVec, ← hAr g, ← Matrix.mulVec_mulVec]
      exact hs g _ hv
  · apply le_antisymm
    · simpa using Matrix.rank_le_width A
    · have := Matrix.rank_mul_le_right B A
      rw [hBA, Matrix.rank_one] at this
      simpa using this
  · intro g
    rw [Matrix.mul_assoc, hAr g, ← Matrix.mul_assoc, hBA, Matrix.one_mul]
  · intro g q
    constructor
    · intro h
      have h2 := aeval_tw _ _ A (hAr g) q
      rw [h, Matrix.zero_mul] at h2
      have h3 := congrArg (B * ·) h2
      simpa [← Matrix.mul_assoc, hBA] using h3.symm
    · intro h
      apply hspan
      intro T hT
      rw [aeval_tw _ _ T (hT g) q, h, Matrix.mul_zero]
end

section
namespace LateralTheory.Fin.FinSub
theorem finite_subrepresentation_etale_charpoly_instance : LateralTheory.DivDb.FinSub := by
  apply LateralTheory.DivDb.FiniteSubrepresentation.FinSub_of
theorem intersectionNumber_baseChange : LateralTheory.DivDb.FinSub := finite_subrepresentation_etale_charpoly_instance
end LateralTheory.Fin.FinSub
end

section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.OpenCosetPf
open LateralTheory.DivDb

def J {Γ C : Type} [Group Γ] [Field C] {n : ℕ} (r : Γ →* GL (Fin n) C) (S : Set Γ) : Ideal (MP C n) where
  carrier := {q | ∀ x ∈ S, ev (r x : Mat C n) q = 0}
  zero_mem' := fun x _ => by simp [ev]
  add_mem' := fun {a b} ha hb x hx => by
    have h1 := ha x hx; have h2 := hb x hx
    simp only [ev, map_add] at *; rw [h1, h2, add_zero]
  smul_mem' := fun c q hq x hx => by
    have h1 := hq x hx
    simp only [ev, smul_eq_mul, map_mul] at *; rw [h1, mul_zero]

theorem main (hChain : Chain) : OpenCoset :=
  _root_.UpperTheory.Reformulated.B.Qn18.main hChain

end LateralTheory.DivDb.OpenCosetPf

namespace LateralTheory.DivDb
theorem OpenCoset_of (hChain : Chain) : OpenCoset := OpenCosetPf.main hChain
end LateralTheory.DivDb
end

section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.FinDensePf

theorem cont_ev {Γ K : Type} [TopologicalSpace Γ] [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    (n : ℕ) (x : Γ → Matrix (Fin n) (Fin n) K) (hx : Continuous x) (f : LateralTheory.DivDb.MP K n) :
    Continuous (fun g => LateralTheory.DivDb.ev (x g) f) := by
  have h1 : Continuous (fun g => (fun p : Fin n × Fin n => x g p.1 p.2)) :=
    continuous_pi fun p => hx.matrix_elem p.1 p.2
  exact (MvPolynomial.continuous_eval f).comp h1

end LateralTheory.DivDb.FinDensePf

namespace LateralTheory.DivDb

theorem FinDense_of (hSep : SepPoly) (hOC : OpenCoset) : FinDense := by
  intro Γ K _ _ _ _ _ _ _ _ _ n r hr hU
  obtain ⟨f, hf⟩ := hSep K n
  have hset : {g : Γ | (r g : Mat K n).charpoly.Separable} = {g | ev (r g : Mat K n) f ≠ 0} := by
    ext g; exact hf _
  rw [hset]
  have hc := LateralTheory.DivDb.FinDensePf.cont_ev n (fun g => (r g : Mat K n)) hr f
  refine ⟨isOpen_ne_fun hc continuous_const, ?_⟩
  rw [dense_iff_inter_open]
  intro O hO hne
  by_contra hemp
  have hz : ∀ g ∈ O, ev (r g : Mat K n) f = 0 := by
    intro g hg
    by_contra h
    exact hemp ⟨g, hg, h⟩
  obtain ⟨U, hUn, hUf, g, hg⟩ := hOC Γ K n r f O hO hne hz
  obtain ⟨u, hu, hs⟩ := hU U hUn hUf g
  exact (hf _).1 hs (hg u hu)

end LateralTheory.DivDb
end

section
namespace LateralTheory.Fin.FinDense
theorem etale_frobenius_charpoly_separable : LateralTheory.DivDb.SepPoly := by
  apply LateralTheory.DivDb.SepPoly_of
theorem etale_divisibility_chain_of_key : LateralTheory.DivDb.Chain := by
  apply LateralTheory.DivDb.Chain_of
theorem etale_open_coset_condition_holds_assembled : LateralTheory.DivDb.OpenCoset := by
  apply LateralTheory.DivDb.OpenCoset_of <;> first | exact etale_divisibility_chain_of_key
theorem etale_finite_image_dense_holds_assembled : LateralTheory.DivDb.FinDense := by
  apply LateralTheory.DivDb.FinDense_of <;> first | exact etale_frobenius_charpoly_separable | exact etale_open_coset_condition_holds_assembled
theorem intersectionNumber_baseChange : LateralTheory.DivDb.FinDense := etale_finite_image_dense_holds_assembled
end LateralTheory.Fin.FinDense
end

section
open Matrix Polynomial PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.FinPolyPf

variable {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}

omit [IsAlgClosed K] in
theorem root_sub (x : Matrix (Fin n) (Fin n) K) (P : K[X]) (hP : P ≠ 0) (hx : aeval x P = 0) :
    x.charpoly.roots ⊆ P.roots := by
  intro a ha
  rw [Polynomial.mem_roots (Matrix.charpoly_monic x).ne_zero] at ha
  rw [Polynomial.mem_roots hP]
  cases n with
  | zero => simp [Matrix.charpoly, Matrix.det_fin_zero] at ha
  | succ m =>
    have hs : a ∈ spectrum K x := Matrix.mem_spectrum_of_isRoot_charpoly ha
    have h2 := spectrum.subset_polynomial_aeval x P ⟨a, hs, rfl⟩
    rw [hx, spectrum.zero_eq] at h2
    simpa using h2

theorem card_roots_eq (P : K[X]) : Multiset.card P.roots = P.natDegree :=
  IsAlgClosed.card_roots_eq_natDegree

theorem cp_card (x : Matrix (Fin n) (Fin n) K) : Multiset.card x.charpoly.roots = n := by
  rw [card_roots_eq, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

theorem eq_of_roots (x : Matrix (Fin n) (Fin n) K) (P : K[X]) (hm : P.Monic)
    (h : x.charpoly.roots = P.roots) : x.charpoly = P := by
  rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic x) (card_roots_eq _),
    ← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (card_roots_eq _), h]

theorem FinPoly_of : FinPoly := by
  intro K _ _ n x P hm hd hx
  have hsub := root_sub x P hm.ne_zero hx
  have hPc : Multiset.card P.roots = n := by rw [card_roots_eq, hd]
  refine ⟨fun hsep => ?_, fun hpg hdet => ?_⟩
  · apply eq_of_roots x P hm
    have hle : x.charpoly.roots ≤ P.roots :=
      (Multiset.le_iff_subset (Polynomial.nodup_roots hsep)).2 hsub
    exact Multiset.eq_of_le_of_card_le hle (by rw [hPc, cp_card])
  · apply eq_of_roots x P hm
    by_contra hne
    refine hpg.2 _ (fun a ha => hsub ha) (cp_card x) hne ?_
    rw [← Matrix.det_eq_prod_roots_charpoly, hdet,
      (IsAlgClosed.splits P).coeff_zero_eq_prod_roots_of_monic hm, hd, ← mul_assoc, ← pow_add,
      Even.neg_one_pow ⟨n, rfl⟩, one_mul]

end LateralTheory.DivDb.FinPolyPf
end

section
namespace LateralTheory.Fin.FinPoly
theorem charpoly_eq_of_annihilating_poly_etale_instance : LateralTheory.DivDb.FinPoly := by
  apply LateralTheory.DivDb.FinPolyPf.FinPoly_of
theorem intersectionNumber_baseChange : LateralTheory.DivDb.FinPoly := charpoly_eq_of_annihilating_poly_etale_instance
end LateralTheory.Fin.FinPoly
end

section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb

theorem goal_holds : DivWCoreLac :=
  goal_of LateralTheory.Fin.SpecLie.intersectionNumber_baseChange LateralTheory.Fin.DegAll.intersectionNumber_baseChange LateralTheory.Fin.Struct.intersectionNumber_baseChange LateralTheory.Fin.Key.intersectionNumber_baseChange LateralTheory.Fin.BigCorner.intersectionNumber_baseChange LateralTheory.Fin.Semis.intersectionNumber_baseChange LateralTheory.Fin.MatrixUnits₂.intersectionNumber_baseChange LateralTheory.Fin.Rep.intersectionNumber_baseChange LateralTheory.Fin.DenseAlg.intersectionNumber_baseChange LateralTheory.Fin.FinSub.intersectionNumber_baseChange LateralTheory.Fin.FinDense.intersectionNumber_baseChange LateralTheory.Fin.FinPoly.intersectionNumber_baseChange LateralTheory.Fin.FinEmbed.intersectionNumber_baseChange

end LateralTheory.DivDb
end
