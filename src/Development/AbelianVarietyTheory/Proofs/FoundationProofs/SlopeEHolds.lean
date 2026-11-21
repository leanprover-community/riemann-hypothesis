import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.SlopeE
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MaxSlopeLeLogOfIntegralHermitianForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PairingNormalisingConstantLogLeBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NablaDeltaOperatorLatticePreservedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExtNormMulWeylPairingIntegralSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPairingGramMatrixValuesAndDefiniteStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthogonalSumCoefficientLatticeIsLatticeAndDualStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDualStatement
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedWeylLatticeHermitianDuality
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
import BuildAid.ForwardExisting

section
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem testLatticeCondition_sumLat_nabK_and_delK : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) → ∀ (C : Type) [Nonempty C] (M : C → ι → Submodule (𝓞 K) (Fin n → K)), (∀ c τ, IsSelfDualK (G τ) (M c τ)) → ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ), IsMetric (sumGram lam e G) X → TestLatticeCondition N X (sumLat lam e fun c => nabK lam (M c)) (bound (Fintype.card ι) n R) ∧ TestLatticeCondition N X (sumLat lam e fun c => delK lam (M c)) (bound (Fintype.card ι) n R) := by
  intro K _ _ _ _ v₀ hv ι _ n lam R hR hsp G hG C _ M hM N e X hX
  classical
  obtain ⟨s, hs0, hs, hlog⟩ := GlobalTheory.T.pairing_normalising_constant_log_le_bound K ι n lam R hR hsp
  have hlat := fun c => GlobalTheory.T.nablaDeltaOperator_lattice_preserved K ι n lam (M c) (fun τ => (hM c τ).1)
  have main : ∀ T : C → Submodule (𝓞 K) (VV K lam), (∀ c, Submodule.IsLattice K (T c)) →
      (∀ c, T c ≤ nabK lam (M c)) → TestLatticeCondition N X (sumLat lam e T) (bound (Fintype.card ι) n R) := by
    intro T hT hle
    obtain ⟨hL, hN, -⟩ := GlobalTheory.T.orthogonalSumCoefficientLattice_isLattice_and_dual K ι n lam C N e T hT
    haveI : Finite C :=
      Finite.of_injective (fun c => e.symm (c, (e ⟨0, hN⟩).2)) (fun a b h => by
        simpa using h)
    letI : Fintype C := Fintype.ofFinite C
    obtain ⟨hval, hdef, -, hdet⟩ := GlobalTheory.T.sumPairingGramMatrix_values_and_definite K ι n lam G hG C N e
    have hne : sumLat lam e T ≠ ⊥ := by
      intro h
      have h2 := hL.span_eq_top
      rw [h] at h2
      haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
      simp at h2
    refine ⟨hL.fg, hne, fun v => (hX v).1, le_trans ?_ hlog⟩
    refine GlobalTheory.T.maxSlope_le_log_of_integral_hermitian_form K v₀ hv N (sumGram lam e G) X ⟨hdef.2.1, hX⟩ s hs0 _ hL.fg hne ?_
    intro x hx y hy
    rw [hval, Finset.mul_sum, ← hs]
    refine Subring.sum_mem _ fun c _ => ?_
    have hmem : ∀ z ∈ sumLat lam e T, valAt lam e c z ∈ nabK lam (M c) := fun z hz =>
      hle c ((Submodule.mem_iInf _).1 hz c)
    exact GlobalTheory.T.extNorm_mul_weylPairing_integral_selfDual K ι n lam G (M c) (fun τ => (hG τ).1) hdet (hM c) _ (hmem x hx) _ (hmem y hy)
  exact ⟨main _ (fun c => (hlat c).1) (fun c => le_rfl),
    main _ (fun c => (hlat c).2) (fun c => delLeNab K ι n lam (M c))⟩

end GlobalTheory.TestLat
end

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxSlope_sum_weyl_and_dualWeyl_lattices_le : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) → ∀ (C : Type) [Nonempty C] (M : C → ι → Submodule (𝓞 K) (Fin n → K)), (∀ c τ, IsSelfDualK (G τ) (M c τ)) → ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ), IsMetric (sumGram lam e G) X → TestLatticeCondition N X (sumLat lam e fun c => nabK lam (M c)) (bound (Fintype.card ι) n R) ∧ TestLatticeCondition N X (sumLat lam e fun c => delK lam (M c)) (bound (Fintype.card ι) n R) := by
  atlas_forward_decl GlobalTheory.TestLat.testLatticeCondition_sumLat_nabK_and_delK
end

section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem star_mem_one_of_mem_one {K : Type} [Field K] [NumberField K] [StarRing K] {z : K}
    (hz : z ∈ (1 : Submodule (𝓞 K) K)) : star z ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hz
  have ha : IsIntegral ℤ (algebraMap (𝓞 K) K a) := a.isIntegral_coe
  have hb : IsIntegral ℤ (star (algebraMap (𝓞 K) K a)) :=
    ha.map (starRingEnd K).toIntAlgHom
  exact Submodule.mem_one.mpr ⟨⟨_, hb⟩, rfl⟩

theorem inv_mulVec_star_mem_hdualFr {K : Type} [Field K] [NumberField K] [StarRing K] {N : ℕ}
    {H : Matrix (Fin N) (Fin N) K} (hd : IsUnit H.det) {M : Submodule (𝓞 K) (Fin N → K)} {x : Fin N → K}
    (hx : x ∈ dualFr M) : H⁻¹ *ᵥ star x ∈ hdualFr H M := by
  intro m hm
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]
  have h := star_mem_one_of_mem_one (hx m hm)
  rw [← Matrix.star_dotProduct_star] at h
  exact h

theorem dualForm_integral_on_dualFr : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (N : ℕ) (H : Matrix (Fin N) (Fin N) K), Hᴴ = H → IsUnit H.det → ∀ (M : Submodule (𝓞 K) (Fin N → K)) (s : ℕ), (∀ x ∈ hdualFr H M, ∀ y ∈ hdualFr H M, (s : K) * (star x ⬝ᵥ H *ᵥ y) ∈ (algebraMap (𝓞 K) K).range) → ∀ x ∈ dualFr M, ∀ y ∈ dualFr M, (s : K) * (star x ⬝ᵥ (H⁻¹)ᵀ *ᵥ y) ∈ (algebraMap (𝓞 K) K).range := by
  intro K _ _ _ N H hH hd M s h x hx y hy
  have key := h _ (inv_mulVec_star_mem_hdualFr hd hy) _ (inv_mulVec_star_mem_hdualFr hd hx)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec, Matrix.star_mulVec, star_star,
    Matrix.conjTranspose_nonsing_inv, hH, ← Matrix.mulVec_transpose, dotProduct_comm] at key
  exact key

end GlobalTheory.TestLat
end

section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transported_weylLattice_hermitianDuality : NabDelDual := by
  first | exact @GlobalTheory.TransDual.nabDelDual | exact GlobalTheory.TransDual.nabDelDual | (intros; apply GlobalTheory.TransDual.nabDelDual <;> assumption)
end

section
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem testLatticeCondition_dualFr_sumLat_delK : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) → ∀ (C : Type) [Nonempty C] (M : C → ι → Submodule (𝓞 K) (Fin n → K)), (∀ c τ, IsSelfDualK (G τ) (M c τ)) → ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ), IsMetric ((sumGram lam e G)⁻¹)ᵀ X → TestLatticeCondition N X (dualFr (sumLat lam e fun c => delK lam (M c))) (bound (Fintype.card ι) n R) := by
  intro K _ _ _ _ v₀ hv ι _ n lam R hR hsp G hG C _ M hM N e X hX
  have hGh : ∀ τ, (G τ)ᴴ = G τ := fun τ => (hG τ).1
  have hdel : ∀ c, Submodule.IsLattice K (delK lam (M c)) := fun c =>
    (GlobalTheory.T.nablaDeltaOperator_lattice_preserved K ι n lam (M c) fun τ => (hM c τ).1).2
  obtain ⟨hlat, hN, hdual⟩ := GlobalTheory.T.orthogonalSumCoefficientLattice_isLattice_and_dual K ι n lam C N e (fun c => delK lam (M c)) hdel
  haveI : Finite C := by
    let i₀ : VVIdx lam := (e ⟨0, hN⟩).2
    refine Finite.of_injective (fun c : C => e.symm (c, i₀)) ?_
    intro a b hab
    exact (Prod.ext_iff.1 (e.symm.injective hab)).1
  letI : Fintype C := Fintype.ofFinite C
  obtain ⟨hval, hH, hHi, hGu⟩ := GlobalTheory.T.sumPairingGramMatrix_values_and_definite K ι n lam G hG C N e
  have hHu : IsUnit (sumGram lam e G).det := by
    have h1 := (hH.2.2 v₀.embedding).isUnit
    rw [Matrix.isUnit_iff_isUnit_det] at h1
    have h2 : ((sumGram lam e G).map v₀.embedding).det = v₀.embedding (sumGram lam e G).det :=
      (RingHom.map_det v₀.embedding (sumGram lam e G)).symm
    rw [h2] at h1
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, map_zero] at h1
    exact not_isUnit_zero h1
  have hnab : hdualFr (sumGram lam e G) (sumLat lam e fun c => delK lam (M c))
      = sumLat lam e fun c => nabK lam (M c) := by
    rw [hdual G hGh]
    congr 1
    funext c
    rw [(GlobalTheory.T.transported_weylLattice_hermitianDuality K ι n lam G (M c) hGh hGu fun τ => (hM c τ).1).2]
    congr 1
    funext τ
    exact (hM c τ).2
  obtain ⟨s, hs, hse, hsb⟩ := GlobalTheory.T.pairing_normalising_constant_log_le_bound K ι n lam R hR hsp
  have hint : ∀ x ∈ hdualFr (sumGram lam e G) (sumLat lam e fun c => delK lam (M c)),
      ∀ y ∈ hdualFr (sumGram lam e G) (sumLat lam e fun c => delK lam (M c)),
        (s : K) * (star x ⬝ᵥ sumGram lam e G *ᵥ y) ∈ (algebraMap (𝓞 K) K).range := by
    intro x hx y hy
    rw [hnab] at hx hy
    rw [hval, Finset.mul_sum]
    refine Subring.sum_mem _ fun c _ => ?_
    rw [← hse]
    exact GlobalTheory.T.extNorm_mul_weylPairing_integral_selfDual K ι n lam G (M c) hGh hGu (hM c) _
      ((Submodule.mem_iInf _).1 hx c) _ ((Submodule.mem_iInf _).1 hy c)
  have hint' := dualForm_integral_on_dualFr K N (sumGram lam e G) hH.1 hHu _ s hint
  have hD := (GlobalTheory.T.dualLattice_isLattice_and_hermitianDual.1 K N (sumGram lam e G) _ hHu hlat).1
  have hne : dualFr (sumLat lam e fun c => delK lam (M c)) ≠ ⊥ := by
    intro h0
    have htop := hD.span_eq_top
    rw [h0] at htop
    haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    simp at htop
  refine ⟨hD.fg, hne, fun v => (hX v).1, le_trans ?_ hsb⟩
  exact GlobalTheory.T.maxSlope_le_log_of_integral_hermitian_form K v₀ hv N _ X ⟨hHi.2.1, hX⟩ s hs _ hD.fg hne hint'

end GlobalTheory.TestLat
end

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxSlope_dual_sum_weyl_lattices_le : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) → ∀ (C : Type) [Nonempty C] (M : C → ι → Submodule (𝓞 K) (Fin n → K)), (∀ c τ, IsSelfDualK (G τ) (M c τ)) → ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ), IsMetric ((sumGram lam e G)⁻¹)ᵀ X → TestLatticeCondition N X (dualFr (sumLat lam e fun c => delK lam (M c))) (bound (Fintype.card ι) n R) := by
  atlas_forward_decl GlobalTheory.TestLat.testLatticeCondition_dualFr_sumLat_delK
end

section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_extension_along_field_embedding_duals : TauLatLattice ∧ TauLatDual ∧ RoundLat := by
  first | exact @GlobalTheory.TauLat.tauLat_lattice_dual_round | exact GlobalTheory.TauLat.tauLat_lattice_dual_round | (intros; apply GlobalTheory.TauLat.tauLat_lattice_dual_round <;> assumption)
end

section
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem isDefGram_map {E K : Type} [Field E] [Field K] [NumberField K] [StarRing K] (cE : E →+* E)
    (hc : ∀ (φ : E →+* ℂ) (x : E), φ (cE x) = starRingEnd ℂ (φ x)) (f : E →+* K)
    (hf : ∀ x, star (f x) = f (cE x)) {n : ℕ} (A : Matrix (Fin n) (Fin n) E)
    (hA : ∀ φ : E →+* ℂ, (A.map φ).PosDef) : IsDefGram (A.map f) := by
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  refine ⟨?_, ?_, ?_⟩
  · ext a b
    have h := congrFun (congrFun (hA (σ.comp f)).isHermitian.eq a) b
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply] at h ⊢
    rw [hf]
    apply σ.injective
    have h2 := hc (σ.comp f) (A b a)
    simp only [RingHom.comp_apply] at h h2
    rw [h2]
    exact h
  · intro a b ψ
    simp only [Matrix.map_apply]
    rw [hf]
    exact hc (ψ.comp f) _
  · intro φ
    rw [Matrix.map_map]
    exact hA (φ.comp f)

theorem map_inv_of_isUnit_det {E K : Type} [Field E] [Field K] (f : E →+* K) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) E) (hA : IsUnit A.det) : (A.map f)⁻¹ = A⁻¹.map f := by
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA]
  simp

theorem isUnit_det_map {E K : Type} [Field E] [Field K] (f : E →+* K) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) E) : IsUnit (A.map f).det ↔ IsUnit A.det := by
  have : (A.map f).det = f A.det := by rw [RingHom.map_det]; rfl
  rw [this, isUnit_iff_ne_zero, isUnit_iff_ne_zero, map_ne_zero]

theorem defGram_selfDual_of_embedding : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (cE : E →+* E), (∀ (φ : E →+* ℂ) (x : E), φ (cE x) = starRingEnd ℂ (φ x)) → ∀ (ι : Type) (emb : ι → E →+* K), (∀ τ x, star (emb τ x) = emb τ (cE x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ φ : E →+* ℂ, (J.map φ).PosDef) → ∀ τ, IsDefGram (gramK emb J τ) ∧ IsDefGram (gramKd emb J τ) ∧ ∀ L : Submodule (𝓞 E) (Fin n → E), IsSelfDualE cE J L → IsSelfDualK (gramK emb J τ) (tauLat emb τ L) ∧ IsSelfDualK (gramKd emb J τ) (dualFr (tauLat emb τ L)) := by
  intro E K _ _ _ _ _ cE hc ι emb hemb n J hJ τ
  obtain ⟨φ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hdet : IsUnit J.det :=
    (isUnit_det_map φ₀ J).1 ((Matrix.isUnit_iff_isUnit_det _).1 (hJ φ₀).isUnit)
  have h1 : IsDefGram (gramK emb J τ) := isDefGram_map cE hc (emb τ) (hemb τ) J hJ
  have hdK : IsUnit (gramK emb J τ).det := (isUnit_det_map (emb τ) J).2 hdet
  refine ⟨h1, ?_, ?_⟩
  · have e : gramKd emb J τ = ((J⁻¹)ᵀ).map (emb τ) := by
      unfold gramKd
      rw [map_inv_of_isUnit_det _ _ hdet, Matrix.transpose_map]
    rw [e]
    refine isDefGram_map cE hc (emb τ) (hemb τ) _ fun φ => ?_
    rw [Matrix.transpose_map, ← map_inv_of_isUnit_det _ _ hdet]
    exact (hJ φ).inv.transpose
  · intro L hL
    have hl : Submodule.IsLattice K (tauLat emb τ L) := GlobalTheory.T.lattice_extension_along_field_embedding_duals.1 E K ι n emb τ L hL.1
    have hd : hdualFr (gramK emb J τ) (tauLat emb τ L) = tauLat emb τ L :=
      GlobalTheory.T.lattice_extension_along_field_embedding_duals.2.1 E K ι n emb cE τ (hemb τ) J L L hdet hL.1 hL.2
    refine ⟨⟨hl, hd⟩, (GlobalTheory.T.dualLattice_isLattice_and_hermitianDual.1 K n _ _ hdK hl).1, ?_⟩
    have h := GlobalTheory.T.dualLattice_isLattice_and_hermitianDual.2 K n _ _ h1.1 hdK hl
    rw [hd] at h
    exact h

end GlobalTheory.TestLat
end

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.defGram_selfDual_after_field_embedding : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (cE : E →+* E), (∀ (φ : E →+* ℂ) (x : E), φ (cE x) = starRingEnd ℂ (φ x)) → ∀ (ι : Type) (emb : ι → E →+* K), (∀ τ x, star (emb τ x) = emb τ (cE x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ φ : E →+* ℂ, (J.map φ).PosDef) → ∀ τ, IsDefGram (gramK emb J τ) ∧ IsDefGram (gramKd emb J τ) ∧ ∀ L : Submodule (𝓞 E) (Fin n → E), IsSelfDualE cE J L → IsSelfDualK (gramK emb J τ) (tauLat emb τ L) ∧ IsSelfDualK (gramKd emb J τ) (dualFr (tauLat emb τ L)) := by
  atlas_forward_decl GlobalTheory.TestLat.defGram_selfDual_of_embedding
end

section
open NumberField
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem slopeK_holds : SlopeK := by
  intro K _ _ _ _ v₀ hv ι _ n lam R hR hs G hG C _ M hM N e X
  exact ⟨GlobalTheory.T.maxSlope_sum_weyl_and_dualWeyl_lattices_le K v₀ hv ι n lam R hR hs G hG C M hM N e X,
    GlobalTheory.T.maxSlope_dual_sum_weyl_lattices_le K v₀ hv ι n lam R hR hs G hG C M hM N e X⟩

theorem slopeE_holds : SlopeE := by
  intro E K _ _ _ _ _ _ v₀ hv cE hcE ι _ emb hemb n lam R hR hs J hJ C _ L hL N e X
  have h := GlobalTheory.T.defGram_selfDual_after_field_embedding E K cE hcE ι emb hemb n J hJ
  have h1 := slopeK_holds K v₀ hv ι n lam R hR hs (gramK emb J) (fun τ => (h τ).1) C
    (fun c τ => tauLat emb τ (L c)) (fun c τ => ((h τ).2.2 (L c) (hL c)).1) N e X
  have h2 := slopeK_holds K v₀ hv ι n lam R hR hs (gramKd emb J) (fun τ => (h τ).2.1) C
    (fun c τ => dualFr (tauLat emb τ (L c))) (fun c τ => ((h τ).2.2 (L c) (hL c)).2) N e X
  exact ⟨h1.2, fun hm => (h1.1 hm).1, h2.2, fun hm => (h2.1 hm).1⟩

theorem slope_holds : GlobalTheory.TestLat.SlopeK ∧ GlobalTheory.TestLat.SlopeE := ⟨slopeK_holds, slopeE_holds⟩

end GlobalTheory.TestLat
end
