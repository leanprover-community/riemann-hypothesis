import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularSemisimpleUnitaryDataOfRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticTraceFromModel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalFramePairsDifferIsometryUnitriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncatedKernelOrbitSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentEqZeroOfCommuteSepAlg

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegularSemisimpleUnitaryData_of_regular : ∀ {D : D7} {V : HSp D} (γ : GF V), IsRegSS γ.1.1 → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.IsRegular D.sp.cm.sig V.gram γ.1 := by
  first | exact @GlobalTheory.ConjLevi.RegularData.isRegular_of_isRegSS | exact GlobalTheory.ConjLevi.RegularData.isRegular_of_isRegSS | (intros; apply GlobalTheory.ConjLevi.RegularData.isRegular_of_isRegSS <;> assumption)
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.SplitFactor

theorem exists_split_factor : ∀ {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (γ : GL (Fin n) E), 0 < n → IsRegSS (γ : Matrix (Fin n) (Fin n) E) → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.ClauseAlg σ J γ → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.ClauseRank σ J γ → ¬ Irreducible (γ : Matrix (Fin n) (Fin n) E).charpoly → ¬ IsNonFieldAniso σ J (γ : Matrix (Fin n) (Fin n) E) → ∃ (k : ℕ) (K : Fin k → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, Algebra F (K i)), Nonempty (GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg σ J (γ : Matrix (Fin n) (Fin n) E) ≃ₐ[F] ∀ i, K i) ∧ ∃ i, ¬ IsField (K i ⊗[F] E) := by
  intro F E _ _ _ n σ J γ hn hreg hAlg hRank hirr hnf
  obtain ⟨k, K, hK, hKA, ⟨e⟩⟩ := hRank.1
  refine ⟨k, K, hK, hKA, ⟨e⟩, ?_⟩
  by_contra hall
  push_neg at hall
  have h2 := hRank.2 k K ⟨e⟩
  have hk1 : 1 ≤ k := h2.2.1 ⟨⟨0, hn⟩⟩
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have hk' : k = 1 := by omega
    have hfield : IsField (GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix (Fin n) (Fin n) E)) := h2.2.2.2 ⟨hk', hall⟩
    obtain ⟨φ, -⟩ := hAlg.1
    have hfA : IsField (AdjoinRoot (γ : Matrix (Fin n) (Fin n) E).charpoly) :=
      φ.toMulEquiv.isField hfield
    have hmax : (Ideal.span {(γ : Matrix (Fin n) (Fin n) E).charpoly}).IsMaximal :=
      Ideal.Quotient.maximal_of_isField _ hfA
    have hne : (γ : Matrix (Fin n) (Fin n) E).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
    have hprime : Prime (γ : Matrix (Fin n) (Fin n) E).charpoly :=
      (Ideal.span_singleton_prime hne).1 hmax.isPrime
    exact hirr hprime.irreducible
  · exact hnf ⟨hreg, k, K, hK, hKA, ⟨e⟩, hk, hall⟩

end GlobalTheory.SplitFactor
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_factor_regularSemisimple_reducible : ∀ {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (γ : GL (Fin n) E), 0 < n → IsRegSS (γ : Matrix (Fin n) (Fin n) E) → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.ClauseAlg σ J γ → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.ClauseRank σ J γ → ¬ Irreducible (γ : Matrix (Fin n) (Fin n) E).charpoly → ¬ IsNonFieldAniso σ J (γ : Matrix (Fin n) (Fin n) E) → ∃ (k : ℕ) (K : Fin k → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, Algebra F (K i)), Nonempty (GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg σ J (γ : Matrix (Fin n) (Fin n) E) ≃ₐ[F] ∀ i, K i) ∧ ∃ i, ¬ IsField (K i ⊗[F] E) := by
  atlas_forward_decl GlobalTheory.SplitFactor.exists_split_factor
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SplitFactorIdem

open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms

section Quad

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem exists_coord (h2 : Module.finrank F E = 2) {a : E}
    (ha : a ∉ Set.range (algebraMap F E)) (x : E) :
    ∃ u v : F, x = algebraMap F E u + v • a := by
  have hli : LinearIndependent F ![(1 : E), a] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    by_cases ht : t = 0
    · subst ht
      simp only [map_zero, zero_mul, add_zero] at hst
      exact ⟨(map_eq_zero_iff _ (algebraMap F E).injective).1 hst, rfl⟩
    · exfalso
      apply ha
      have ht' : algebraMap F E t ≠ 0 := (map_ne_zero _).2 ht
      refine ⟨-(s / t), ?_⟩
      rw [map_neg, map_div₀]
      field_simp
      linear_combination (-1 : E) * hst
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  refine ⟨b.repr x 0, b.repr x 1, ?_⟩
  conv_lhs => rw [← b.sum_repr x]
  simp [Fin.sum_univ_two, b, Algebra.algebraMap_eq_smul_one]

theorem fixed_mem {σ : E →ₐ[F] E} (hq : IsQuadInvol F E σ) {x : E} (hx : σ x = x) :
    x ∈ Set.range (algebraMap F E) := by
  by_contra hx'
  obtain ⟨e, he⟩ := hq.ne_id
  obtain ⟨u, v, rfl⟩ := exists_coord hq.finrank_eq hx' e
  apply he
  rw [map_add, AlgHom.commutes, map_smul, hx]

theorem exists_root (K : Type) [Field K] [Algebra F K] (h2 : Module.finrank F E = 2) {a : E}
    (ha : a ∉ Set.range (algebraMap F E)) (t s : F)
    (hts : a * a = algebraMap F E t * a - algebraMap F E s) (hK : ¬ IsField (K ⊗[F] E)) :
    ∃ β : K, β * β - algebraMap F K t * β + algebraMap F K s = 0 := by
  by_contra hno
  push_neg at hno
  apply hK
  haveI : Nontrivial (K ⊗[F] E) :=
    (Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := K) (B := E)
      (algebraMap F E).injective).nontrivial
  let A : K ⊗[F] E := (1 : K) ⊗ₜ a
  let ι := algebraMap K (K ⊗[F] E)
  have hι : ∀ c : F, ι (algebraMap F K c) = (1 : K) ⊗ₜ algebraMap F E c := by
    intro c
    simp [ι, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
    rw [Algebra.TensorProduct.one_def]
  have hA : A * A = ι (algebraMap F K t) * A - ι (algebraMap F K s) := by
    simp only [hι, A, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← TensorProduct.tmul_sub, hts]
  have hspan : ∀ x : K ⊗[F] E, ∃ u v : K, x = ι u + ι v * A := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul k e =>
      obtain ⟨u, v, rfl⟩ := exists_coord h2 ha e
      refine ⟨u • k, v • k, ?_⟩
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_add, ← TensorProduct.smul_tmul,
        ← TensorProduct.smul_tmul]
      simp [ι, A, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy =>
      obtain ⟨u, v, rfl⟩ := hx
      obtain ⟨u', v', rfl⟩ := hy
      exact ⟨u + u', v + v', by simp only [map_add]; ring⟩
  refine ⟨exists_pair_ne _, fun x y => mul_comm x y, ?_⟩
  intro x hx
  obtain ⟨u, v, rfl⟩ := hspan x
  set T := algebraMap F K t
  set S := algebraMap F K s
  set N := u * u + T * u * v + S * v * v with hNdef
  have hN : N ≠ 0 := by
    by_cases hv : v = 0
    · subst hv
      have hu : u ≠ 0 := by rintro rfl; simp at hx
      simpa [N] using hu
    · intro h0
      apply hno (-u / v)
      field_simp
      linear_combination h0
  refine ⟨ι (N⁻¹ * (u + T * v)) - ι (N⁻¹ * v) * A, ?_⟩
  have hinv : (ι u * ι u + ι T * ι u * ι v + ι S * ι v * ι v) * ι N⁻¹ = 1 := by
    rw [show ι u * ι u + ι T * ι u * ι v + ι S * ι v * ι v = ι N by simp [N]]
    rw [← map_mul, mul_inv_cancel₀ hN, map_one]
  simp only [map_mul, map_add]
  linear_combination (-(ι N⁻¹ * ι v * ι v)) * hA + hinv

end Quad

section Mat

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ}

theorem cT_sub (σ : E →+* E) (X Y : Matrix (Fin n) (Fin n) E) :
    Formalism.UG.cT σ (X - Y) = Formalism.UG.cT σ X - Formalism.UG.cT σ Y := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_scalar (σ : E →+* E) (a : E) :
    Formalism.UG.cT σ (algebraMap E (Matrix (Fin n) (Fin n) E) a) =
      algebraMap E (Matrix (Fin n) (Fin n) E) (σ a) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Formalism.UG.cT, Matrix.algebraMap_matrix_apply]
  · simp [Formalism.UG.cT, Matrix.algebraMap_matrix_apply, h, Ne.symm h]

theorem adj_mul {σ : E →+* E} {J X X' Y Y' : Matrix (Fin n) (Fin n) E}
    (hX : Formalism.UG.cT σ X * J = J * X') (hY : Formalism.UG.cT σ Y * J = J * Y') :
    Formalism.UG.cT σ (X * Y) * J = J * (Y' * X') := by
  rw [Formalism.UG.cT_mul, Matrix.mul_assoc, hX, ← Matrix.mul_assoc, hY, Matrix.mul_assoc]

theorem adj_sub {σ : E →+* E} {J X X' Y Y' : Matrix (Fin n) (Fin n) E}
    (hX : Formalism.UG.cT σ X * J = J * X') (hY : Formalism.UG.cT σ Y * J = J * Y') :
    Formalism.UG.cT σ (X - Y) * J = J * (X' - Y') := by
  rw [cT_sub, Matrix.sub_mul, hX, hY, Matrix.mul_sub]

theorem adj_scalar (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (a : E) :
    Formalism.UG.cT σ (algebraMap E (Matrix (Fin n) (Fin n) E) a) * J =
      J * algebraMap E (Matrix (Fin n) (Fin n) E) (σ a) := by
  rw [cT_scalar, Algebra.commutes]

theorem piece (σ : E →ₐ[F] E) (J γm : Matrix (Fin n) (Fin n) E) (t s : F)
    (pp bb bb' dd : genAlg γm)
    (hp : Formalism.UG.cT (σ : E →+* E) (pp : Matrix (Fin n) (Fin n) E) * J = J * pp)
    (hb' : Formalism.UG.cT (σ : E →+* E) (bb' : Matrix (Fin n) (Fin n) E) * J = J * bb')
    (hd : Formalism.UG.cT (σ : E →+* E) (dd : Matrix (Fin n) (Fin n) E) * J = J * dd)
    (R1 : pp * pp = pp) (R2 : pp * bb' = bb') (R3 : bb + bb' = algebraMap F _ t * pp)
    (R4 : bb * bb' = algebraMap F _ s * pp) (R5 : dd * (bb - bb') = pp)
    (a : E) (hT : algebraMap F E t = a + σ a) (hS : algebraMap F E s = a * σ a)
    (εL : genAlg γm) (hε : εL = dd * (pp * algebraMap E (genAlg γm) a - bb')) :
    εL * εL = εL ∧
      Formalism.UG.cT (σ : E →+* E) (εL : Matrix (Fin n) (Fin n) E) * J * (εL : Matrix (Fin n) (Fin n) E) = 0 := by
  set AL := algebraMap E (genAlg γm) a
  set BL := algebraMap E (genAlg γm) (σ a)
  have RT : AL + BL = algebraMap F (genAlg γm) t := by
    rw [IsScalarTower.algebraMap_apply F E (genAlg γm), hT, map_add]
  have RS : AL * BL = algebraMap F (genAlg γm) s := by
    rw [IsScalarTower.algebraMap_apply F E (genAlg γm), hS, map_mul]
  have RA : AL * AL = algebraMap F (genAlg γm) t * AL - algebraMap F (genAlg γm) s := by
    rw [← RT, ← RS]; ring
  constructor
  · have h1 : (pp * AL - bb') * (pp * AL - bb') = (bb - bb') * (pp * AL - bb') := by
      linear_combination pp * pp * RA - algebraMap F (genAlg γm) s * R1 - pp * AL * R3 + R4
    rw [hε]
    linear_combination dd * dd * h1 + dd * (pp * AL - bb') * R5 + dd * AL * R1 - dd * R2
  · have hA' : Formalism.UG.cT (σ : E →+* E) ((AL : genAlg γm) : Matrix (Fin n) (Fin n) E) * J =
        J * ((BL : genAlg γm) : Matrix (Fin n) (Fin n) E) := by
      simp only [AL, BL, Subalgebra.coe_algebraMap]
      exact adj_scalar _ J a
    have hεm : Formalism.UG.cT (σ : E →+* E) (εL : Matrix (Fin n) (Fin n) E) * J =
        J * (((BL * pp - bb') * dd : genAlg γm) : Matrix (Fin n) (Fin n) E) := by
      rw [hε]
      simp only [Subalgebra.coe_mul, Subalgebra.coe_sub]
      exact adj_mul hd (adj_sub (adj_mul hp hA') hb')
    have hY : (BL * pp - bb') * dd * εL = 0 := by
      rw [hε]
      linear_combination dd * dd * (pp * pp * RS - pp * bb' * RT +
        algebraMap F (genAlg γm) s * R1 + bb' * R3 - R4)
    rw [hεm, Matrix.mul_assoc, ← Subalgebra.coe_mul, hY]
    simp

end Mat

theorem exists_isotropic_idempotent : ∀ {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (γ : GL (Fin n) E), GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.IsRegular σ J γ → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.ClauseAlg σ J γ → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.ClausePlus σ J γ → ∀ (k : ℕ) (K : Fin k → Type) [∀ i, Field (K i)] [∀ i, Algebra F (K i)], Nonempty (GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg σ J (γ : Matrix (Fin n) (Fin n) E) ≃ₐ[F] ∀ i, K i) → ∀ i, ¬ IsField (K i ⊗[F] E) → ∃ ε ∈ GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix (Fin n) (Fin n) E), ε * ε = ε ∧ ε ≠ 0 ∧ Formalism.UG.cT (σ : E →+* E) ε * J * ε = 0 := by
  intro F E _ _ _ _ n σ J γ hR hA hP k K _ _ he i hi
  classical
  obtain ⟨e⟩ := he
  obtain ⟨α, hα⟩ := hR.quad.ne_id
  obtain ⟨t, ht⟩ := fixed_mem hR.quad (x := α + σ α) (by rw [map_add, hR.quad.invol, add_comm])
  obtain ⟨s, hs⟩ := fixed_mem hR.quad (x := α * σ α) (by rw [map_mul, hR.quad.invol, mul_comm])
  have hαF : α ∉ Set.range (algebraMap F E) := by
    rintro ⟨c, rfl⟩; exact hα (σ.commutes c)
  have hαsq : α * α = algebraMap F E t * α - algebraMap F E s := by rw [ht, hs]; ring
  obtain ⟨β, hβ⟩ := exists_root (K i) hR.quad.finrank_eq hαF t s hαsq hi
  have hdisc : β - (algebraMap F (K i) t - β) ≠ 0 := by
    have hE : algebraMap F E (t * t - 4 * s) ≠ 0 := by
      rw [map_sub, map_mul, map_mul, ht, hs, map_ofNat]
      intro h; apply hα
      have h' : (α - σ α) * (α - σ α) = 0 := by linear_combination h
      exact (sub_eq_zero.1 (mul_self_eq_zero.1 h')).symm
    have hK : algebraMap F (K i) (t * t - 4 * s) ≠ 0 :=
      (map_ne_zero _).2 (fun h0 => hE (by rw [h0, map_zero]))
    intro h0; apply hK
    rw [map_sub, map_mul, map_mul, map_ofNat]
    have h' : (β - (algebraMap F (K i) t - β)) * (β - (algebraMap F (K i) t - β)) = 0 := by
      rw [h0, mul_zero]
    linear_combination h' - 4 * hβ
  set T' := algebraMap F (K i) t with hT'
  let y : ∀ j, K j := Pi.single i 1
  let w : ∀ j, K j := Pi.single i β
  let x : ∀ j, K j := Pi.single i (T' - β)
  let z : ∀ j, K j := Pi.single i (β - (T' - β))⁻¹
  have Q1 : y * y = y := by
    ext j; by_cases h : j = i
    · subst h; simp [y]
    · simp [y, Pi.single_apply, h]
  have Q2 : y * x = x := by
    ext j; by_cases h : j = i
    · subst h; simp [y, x]
    · simp [y, x, Pi.single_apply, h]
  have Q3 : w + x = algebraMap F _ t * y := by
    ext j; by_cases h : j = i
    · subst h; simp [y, w, x, Pi.algebraMap_apply, T']
    · simp [y, w, x, Pi.single_apply, h]
  have Q4 : w * x = algebraMap F _ s * y := by
    ext j; by_cases h : j = i
    · subst h; simp [y, w, x, Pi.algebraMap_apply, T']
      linear_combination -hβ
    · simp [y, w, x, Pi.single_apply, h]
  have Q5 : z * (w - x) = y := by
    ext j; by_cases h : j = i
    · subst h; simp [y, w, x, z, inv_mul_cancel₀ hdisc]
    · simp [y, w, x, z, Pi.single_apply, h]
  let φ : (∀ j, K j) →ₐ[F] genAlg (γ : Matrix (Fin n) (Fin n) E) :=
    (plusAlg σ J (γ : Matrix (Fin n) (Fin n) E)).val.comp
      (e.symm : (∀ j, K j) →ₐ[F] plusAlg σ J (γ : Matrix (Fin n) (Fin n) E))
  have hmem : ∀ v, Formalism.UG.cT (σ : E →+* E) ((φ v : genAlg (γ : Matrix (Fin n) (Fin n) E)) :
      Matrix (Fin n) (Fin n) E) * J = J * ((φ v : genAlg (γ : Matrix (Fin n) (Fin n) E)) :
      Matrix (Fin n) (Fin n) E) := fun v => (e.symm v).2
  have R1 : φ y * φ y = φ y := by rw [← map_mul, Q1]
  have R2 : φ y * φ x = φ x := by rw [← map_mul, Q2]
  have R3 : φ w + φ x = algebraMap F _ t * φ y := by rw [← map_add, Q3, map_mul, AlgHom.commutes]
  have R4 : φ w * φ x = algebraMap F _ s * φ y := by rw [← map_mul, Q4, map_mul, AlgHom.commutes]
  have R5 : φ z * (φ w - φ x) = φ y := by rw [← map_sub, ← map_mul, Q5]
  have P1 := piece σ J _ t s (φ y) (φ w) (φ x) (φ z) (hmem y) (hmem x) (hmem z) R1 R2 R3 R4 R5
    α ht hs _ rfl
  have P2 := piece σ J _ t s (φ y) (φ w) (φ x) (φ z) (hmem y) (hmem x) (hmem z) R1 R2 R3 R4 R5
    (σ α) (by rw [hR.quad.invol, ht, add_comm]) (by rw [hR.quad.invol, hs, mul_comm]) _ rfl
  have RT : algebraMap E (genAlg (γ : Matrix (Fin n) (Fin n) E)) α +
      algebraMap E (genAlg (γ : Matrix (Fin n) (Fin n) E)) (σ α) = algebraMap F _ t := by
    rw [IsScalarTower.algebraMap_apply F E (genAlg (γ : Matrix (Fin n) (Fin n) E)), ht, map_add]
  have hsum : φ z * (φ y * algebraMap E _ α - φ x) + φ z * (φ y * algebraMap E _ (σ α) - φ x)
      = φ y := by
    linear_combination R5 + φ z * φ y * RT - φ z * R3
  have hy0 : ((φ y : genAlg (γ : Matrix (Fin n) (Fin n) E)) : Matrix (Fin n) (Fin n) E) ≠ 0 := by
    intro h0
    have h1 : φ y = 0 := Subtype.ext h0
    have h2 : y = 0 := by
      have h3 : e.symm y = 0 := Subtype.ext h1
      simpa using congrArg e h3
    have h4 := congrFun h2 i
    simp [y] at h4
  by_cases h1 : (((φ z * (φ y * algebraMap E _ α - φ x) :
      genAlg (γ : Matrix (Fin n) (Fin n) E))) : Matrix (Fin n) (Fin n) E) = 0
  · refine ⟨_, (φ z * (φ y * algebraMap E _ (σ α) - φ x)).2, congrArg Subtype.val P2.1, ?_, P2.2⟩
    intro h2; apply hy0
    rw [← hsum, Subalgebra.coe_add, h1, h2, add_zero]
  · exact ⟨_, (φ z * (φ y * algebraMap E _ α - φ x)).2, congrArg Subtype.val P1.1, h1, P1.2⟩

end GlobalTheory.SplitFactorIdem
end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_idempotent_of_split_factor : ∀ {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (γ : GL (Fin n) E), GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.IsRegular σ J γ → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.ClauseAlg σ J γ → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.ClausePlus σ J γ → ∀ (k : ℕ) (K : Fin k → Type) [∀ i, Field (K i)] [∀ i, Algebra F (K i)], Nonempty (GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg σ J (γ : Matrix (Fin n) (Fin n) E) ≃ₐ[F] ∀ i, K i) → ∀ i, ¬ IsField (K i ⊗[F] E) → ∃ ε ∈ GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix (Fin n) (Fin n) E), ε * ε = ε ∧ ε ≠ 0 ∧ Formalism.UG.cT (σ : E →+* E) ε * J * ε = 0 := by
  atlas_forward_decl GlobalTheory.SplitFactorIdem.exists_isotropic_idempotent
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.IdemIsotropic

open Matrix Formalism.UG

variable {D : D7}

theorem hT_eq_hform (V : HSp D) (x y : V.V) :
    V.hT x y = hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram (V.frame.repr x) (V.frame.repr y) := by
  conv_lhs => rw [← V.frame.sum_repr x, ← V.frame.sum_repr y]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hform,
    HSpace.gram, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show _ = star _ * _ * _
  rw [starRingEnd_apply]
  ring

theorem hform_mulVec {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J M N : Matrix n n A) (a b : n → A) :
    hform σ J (M *ᵥ a) (N *ᵥ b) = hform σ (cT σ M * J * N) a b := by
  have h2 : (fun i => σ ((M *ᵥ a) i)) = (M.map σ) *ᵥ (fun i => σ (a i)) := by
    funext i; simp [Matrix.mulVec, dotProduct]
  rw [GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.hform_eq, GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.hform_eq, h2, Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, cT, Matrix.mul_assoc]

theorem hform_zero {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A) (a b : n → A) :
    hform σ (0 : Matrix n n A) a b = 0 := by
  simp [hform]

theorem cT_sub' {A : Type} [CommRing A] {n : Type} (σ : A →+* A) (M N : Matrix n n A) :
    cT σ (M - N) = cT σ M - cT σ N := by
  ext i j; simp [cT]

theorem hT_toLin (V : HSp D) (M N : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (a b : V.V) :
    V.hT (Matrix.toLin V.frame V.frame M a) (Matrix.toLin V.frame V.frame N b) =
      hform (D.sp.cm.sig : D.host.E →+* D.host.E) (cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * N)
        (V.frame.repr a) (V.frame.repr b) := by
  rw [hT_eq_hform, Matrix.repr_toLin, Matrix.repr_toLin, hform_mulVec]

theorem gram_herm (V : HSp D) : cT (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram = V.gram := by
  refine Matrix.ext fun i j => ?_
  show star (V.hT (V.frame j) (V.frame i)) = V.hT (V.frame i) (V.frame j)
  exact V.herm.eq (V.frame j) (V.frame i)

theorem idem_isotropic_pair : ∀ {D : D7} {V : HSp D} (γ : GF V) (ε : Matrix (Fin V.rank) (Fin V.rank) D.host.E), ε ∈ GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg γ.1.1 → ε * ε = ε → ε ≠ 0 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) ε * V.gram * ε = 0 → ∃ X X' : Submodule D.host.E V.V, X ≠ ⊥ ∧ X ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X ∧ X' ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X' ∧ (∀ x ∈ X, GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ X) ∧ (∀ x ∈ X', GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ X') ∧ (∀ x ∈ X, (∀ y ∈ X', V.hD x y = 0) → x = 0) ∧ (∀ y ∈ X', (∀ x ∈ X, V.hD x y = 0) → y = 0) := by
  intro D V γ ε hmem hidem hne hiso
  set σ := (D.sp.cm.sig : D.host.E →+* D.host.E) with hσ
  set J := V.gram with hJdef
  have hdet : IsUnit J.det := isUnit_iff_ne_zero.2 (GlobalTheory.Mem.Vol.hspace_gram_det_ne_zero V)
  have hJJ : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hJJ' : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul _ hdet
  have cancel : ∀ A B : Matrix (Fin V.rank) (Fin V.rank) D.host.E, J * A = J * B → A = B := by
    intro A B h
    rw [← Matrix.one_mul A, ← Matrix.one_mul B, ← hJJ', Matrix.mul_assoc, h, ← Matrix.mul_assoc]
  set ε' := J⁻¹ * cT σ ε * J with hε'
  have hR : J * ε' = cT σ ε * J := by
    rw [hε', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  clear_value ε'
  have hTL : ∀ (M N : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (a b : V.V),
      V.hT (Matrix.toLin V.frame V.frame M a) (Matrix.toLin V.frame V.frame N b) =
        hform σ (cT σ M * J * N) (V.frame.repr a) (V.frame.repr b) := hT_toLin V
  have hσσ : ∀ e, σ (σ e) = e := fun e => star_star e
  have cTcT : ∀ M : Matrix (Fin V.rank) (Fin V.rank) D.host.E, cT σ (cT σ M) = M := by
    intro M; ext i j; simp [cT, hσσ]
  have herm : cT σ J = J := gram_herm V
  have hR' : cT σ ε' * J = J * ε := by
    have h := congrArg (cT σ) hR
    rw [cT_mul, cT_mul, herm, cTcT] at h
    exact h
  have h0 : ε' * ε = 0 := cancel _ _ (by rw [← Matrix.mul_assoc, hR, hiso, Matrix.mul_zero])
  set g := (γ.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) with hg
  set gi := ((γ.1⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) with hgi
  have hγ : cT σ g * J * g = J := γ.2
  have hggi : g * gi = 1 := Units.mul_inv γ.1
  have hgig : gi * g = 1 := Units.inv_mul γ.1
  have hmem' : ε ∈ Algebra.adjoin D.host.E {g} := hmem
  have hJg : J * g = cT σ gi * J := by
    calc J * g = cT σ (g * gi) * J * g := by rw [hggi, cT_one, Matrix.one_mul]
      _ = cT σ gi * (cT σ g * J * g) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT σ gi * J := by rw [hγ]
  have hεgi : Commute gi ε :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hmem' (by rw [Commute, SemiconjBy, hgig, hggi])
  have hε'g : ε' * g = g * ε' := cancel _ _ (by
    rw [← Matrix.mul_assoc, hR, Matrix.mul_assoc, hJg, ← Matrix.mul_assoc J g, hJg, Matrix.mul_assoc, hR,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul, ← cT_mul, hεgi.eq])
  have hcomm : Commute ε' ε := Algebra.commute_of_mem_adjoin_singleton_of_commute hmem' hε'g
  have hgε : Commute g ε := Algebra.commute_of_mem_adjoin_singleton_of_commute hmem' (Commute.refl g)
  have h1 : ε * ε' = 0 := by rw [← hcomm.eq, h0]
  have mA : cT σ (1 - ε - ε') * J * ε = 0 := by
    rw [cT_sub', cT_sub', cT_one, Matrix.sub_mul, Matrix.sub_mul, Matrix.sub_mul, Matrix.sub_mul,
      Matrix.one_mul, hiso, hR', Matrix.mul_assoc, hidem, sub_zero, sub_self]
  have mB : cT σ ε' * J * (1 - ε - ε') = 0 := by
    rw [hR', Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, Matrix.mul_assoc,
      hidem, h1, Matrix.mul_zero, sub_self, sub_zero]
  have mC : cT σ ε' * J * ε' = 0 := by rw [hR', Matrix.mul_assoc, h1, Matrix.mul_zero]
  have split : ∀ v : V.V, v = Matrix.toLin V.frame V.frame ε v + Matrix.toLin V.frame V.frame ε' v +
      Matrix.toLin V.frame V.frame (1 - ε - ε') v := by
    intro v
    simp only [map_sub, Matrix.toLin_one, LinearMap.sub_apply, LinearMap.id_apply]
    abel
  have mem_perp : ∀ (W : Submodule D.host.E V.V) (y : V.V),
      y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W ↔ ∀ w ∈ W, V.hT w y = 0 := by
    intro W y
    simp [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp, Submodule.mem_iInf, LinearMap.mem_ker]
  have ratAct_eq : ∀ x, GlobalTheory.Cusp.ratAct D.sp.cm V γ x = Matrix.toLin V.frame V.frame g x := fun _ => rfl
  refine ⟨LinearMap.range (Matrix.toLin V.frame V.frame ε), LinearMap.range (Matrix.toLin V.frame V.frame ε'),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [LinearMap.range_eq_bot] at h
    exact hne ((Matrix.toLin V.frame V.frame).map_eq_zero_iff.1 h)
  · rintro _ ⟨b, rfl⟩
    rw [mem_perp]
    rintro _ ⟨a, rfl⟩
    rw [hTL, hiso, hform_zero]
  · rintro _ ⟨b, rfl⟩
    rw [mem_perp]
    rintro _ ⟨a, rfl⟩
    rw [hTL, mC, hform_zero]
  · rintro _ ⟨a, rfl⟩
    refine ⟨Matrix.toLin V.frame V.frame g a, ?_⟩
    rw [ratAct_eq, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← Matrix.toLin_mul, ← Matrix.toLin_mul,
      hgε.eq]
  · rintro _ ⟨a, rfl⟩
    refine ⟨Matrix.toLin V.frame V.frame g a, ?_⟩
    rw [ratAct_eq, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← Matrix.toLin_mul, ← Matrix.toLin_mul,
      hε'g]
  · rintro _ ⟨a, rfl⟩ hy
    refine V.nondeg.2 _ fun v => ?_
    rw [split v, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hTL ε ε, hiso, hform_zero,
      hTL (1 - ε - ε') ε, mA, hform_zero, zero_add, add_zero]
    exact hy _ ⟨v, rfl⟩
  · rintro _ ⟨b, rfl⟩ hx
    refine V.nondeg.1 _ fun v => ?_
    have e1 : V.hT (Matrix.toLin V.frame V.frame ε' b) v =
        V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame ε v) +
        V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame ε' v) +
        V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame (1 - ε - ε') v) := by
      conv_lhs => rw [split v]
      simp only [map_add]
    have e2 : V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame ε' v) = 0 := by
      rw [hTL, mC, hform_zero]
    have e3 : V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame (1 - ε - ε') v) = 0 := by
      rw [hTL, mB, hform_zero]
    have e4 : V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame ε v) = 0 := hx _ ⟨v, rfl⟩
    linear_combination e1 + e2 + e3 + e4

end GlobalTheory.IdemIsotropic
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicIdempotent_gives_dual_stable_subspaces : ∀ {D : D7} {V : HSp D} (γ : GF V) (ε : Matrix (Fin V.rank) (Fin V.rank) D.host.E), ε ∈ GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg γ.1.1 → ε * ε = ε → ε ≠ 0 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) ε * V.gram * ε = 0 → ∃ X X' : Submodule D.host.E V.V, X ≠ ⊥ ∧ X ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X ∧ X' ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X' ∧ (∀ x ∈ X, GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ X) ∧ (∀ x ∈ X', GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ X') ∧ (∀ x ∈ X, (∀ y ∈ X', V.hD x y = 0) → x = 0) ∧ (∀ y ∈ X', (∀ x ∈ X, V.hD x y = 0) → y = 0) := by
  atlas_forward_decl GlobalTheory.IdemIsotropic.idem_isotropic_pair
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.IsoDuality

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem hT_herm (V : Formalism.BasicNotions.HSpace E) (x y : V.V) : star (V.hT x y) = V.hT y x := by
  have := V.herm.eq x y
  rw [← starRingEnd_apply]; exact this

theorem iso_zero (V : Formalism.BasicNotions.HSpace E) {W : Submodule E V.V} (hW : W ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W)
    {w v : V.V} (hw : w ∈ W) (hv : v ∈ W) : V.hT w v = 0 := by
  have := hW hv
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp, Submodule.mem_iInf, LinearMap.mem_ker] at this
  exact this w hw

theorem finrank_le_of_sep (V : Formalism.BasicNotions.HSpace E) (A B : Submodule E V.V)
    (h : ∀ y ∈ B, (∀ x ∈ A, V.hT x y = 0) → y = 0) :
    Module.finrank E B ≤ Module.finrank E A := by
  classical
  let bA := Module.finBasis E A
  let Φ : B →ₗ[E] (Fin (Module.finrank E A) → E) :=
    LinearMap.pi (fun i => (V.hT (bA i : V.V)).comp B.subtype)
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : ∀ i, V.hT (bA i : V.V) y = 0 := fun i => congrFun hy i
    apply Subtype.ext
    apply h y y.2
    intro x hx
    have hx' : (⟨x, hx⟩ : A) = ∑ i, (bA.repr ⟨x, hx⟩ i) • bA i := (bA.sum_repr _).symm
    have : x = ∑ i, (bA.repr ⟨x, hx⟩ i) • (bA i : V.V) := by
      calc x = ((∑ i, (bA.repr ⟨x, hx⟩ i) • bA i : A) : V.V) := by rw [← hx']
        _ = _ := by simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [this, map_sum]
    simp [map_smulₛₗ, hy']
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this

end GlobalTheory.IsoDuality

namespace GlobalTheory.IsoDuality

theorem exists_dual_bases : ∀ {D : D7} {V : HSp D} (X X' : Submodule D.host.E V.V), X ≠ ⊥ → X ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X → X' ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X' → (∀ x ∈ X, (∀ y ∈ X', V.hD x y = 0) → x = 0) → (∀ y ∈ X', (∀ x ∈ X, V.hD x y = 0) → y = 0) → ∃ (a : ℕ) (x x' : Fin a → V.V), 0 < a ∧ a ≤ wittIndex V ∧ Submodule.span D.host.E (Set.range x) = X ∧ Submodule.span D.host.E (Set.range x') = X' ∧ LinearIndependent D.host.E (Sum.elim x x') ∧ (∀ i j, V.hD (x i) (x j) = 0) ∧ (∀ i j, V.hD (x' i) (x' j) = 0) ∧ (∀ i j, V.hD (x i) (x' j) = if i = j then 1 else 0) := by
  classical
  intro D V X X' hX0 hX hX' h1 h2
  have hTX := fun {w v : V.V} (hw : w ∈ X) (hv : v ∈ X) => iso_zero V hX hw hv
  have hTX' := fun {w v : V.V} (hw : w ∈ X') (hv : v ∈ X') => iso_zero V hX' hw hv

  have hle1 : Module.finrank D.host.E X ≤ Module.finrank D.host.E X' :=
    finrank_le_of_sep V X' X (fun y hy h => h1 y hy (fun z hz => h z hz))
  have hle2 : Module.finrank D.host.E X' ≤ Module.finrank D.host.E X :=
    finrank_le_of_sep V X X' (fun y hy h => h2 y hy (fun z hz => by
      show V.hT y z = 0
      rw [← hT_herm, h z hz, star_zero]))
  set a := Module.finrank D.host.E X with ha
  let bx := Module.finBasis D.host.E X
  let x : Fin a → V.V := fun i => (bx i : V.V)
  have hxX : ∀ i, x i ∈ X := fun i => (bx i).2
  let Φ : X' →ₗ[D.host.E] (Fin a → D.host.E) :=
    LinearMap.pi (fun i => (V.hT (x i)).comp X'.subtype)
  have hΦ : ∀ y i, Φ y i = V.hT (x i) y := fun y i => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : ∀ i, V.hT (x i) y = 0 := fun i => congrFun hy i
    apply Subtype.ext
    apply h2 y y.2
    intro z hz
    have hz' : (⟨z, hz⟩ : X) = ∑ i, (bx.repr ⟨z, hz⟩ i) • bx i := (bx.sum_repr _).symm
    have : z = ∑ i, (bx.repr ⟨z, hz⟩ i) • x i := by
      calc z = ((∑ i, (bx.repr ⟨z, hz⟩ i) • bx i : X) : V.V) := by rw [← hz']
        _ = _ := by simp only [Submodule.coe_sum, Submodule.coe_smul]; rfl
    show V.hT (y : V.V) z = 0
    rw [← hT_herm, this, map_sum]
    simp [map_smulₛₗ, hy']
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    · exact hinj
    · simp [a]; omega
  choose g hg using fun j : Fin a => hsurj (Pi.single j 1)
  let x' : Fin a → V.V := fun j => (g j : V.V)
  have hx'X : ∀ j, x' j ∈ X' := fun j => (g j).2
  have hxx' : ∀ i j, V.hT (x i) (x' j) = if i = j then 1 else 0 := by
    intro i j
    have := congrFun (hg j) i
    rw [hΦ] at this
    show V.hT (x i) (g j : V.V) = _
    rw [this, Pi.single_apply]
  have hxli : LinearIndependent D.host.E x :=
    bx.linearIndependent.map' X.subtype (Submodule.ker_subtype X)
  have hli : LinearIndependent D.host.E (Sum.elim x x') := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fintype.sum_sum_type] at hc
    simp only [Sum.elim_inl, Sum.elim_inr] at hc
    have hd : ∀ k, c (Sum.inr k) = 0 := by
      intro k
      have := congrArg (V.hT (x k)) hc
      rw [map_add, map_sum, map_sum, map_zero] at this
      simp only [map_smul, smul_eq_mul, hTX (hxX k) (hxX _), mul_zero, Finset.sum_const_zero,
        zero_add, hxx', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
      exact this
    have hc' : ∑ i, c (Sum.inl i) • x i = 0 := by
      simpa [hd] using hc
    have hcl := Fintype.linearIndependent_iff.1 hxli _ hc'
    rintro (i | j)
    · exact hcl i
    · exact hd j
  have hx'li : LinearIndependent D.host.E x' := hli.comp Sum.inr Sum.inr_injective
  refine ⟨a, x, x', ?_, ?_, ?_, ?_, hli, ?_, ?_, ?_⟩
  · exact Nat.pos_of_ne_zero (fun h => hX0 (Submodule.finrank_eq_zero.1 h))
  · exact GlobalTheory.Cusp.finrank_le_wittIndex hX
  · have : Set.range x = X.subtype '' Set.range bx := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, bx.span_eq, Submodule.map_top, Submodule.range_subtype]
  · apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]; rintro _ ⟨j, rfl⟩; exact hx'X j
    · rw [finrank_span_eq_card hx'li]; simp [a]; omega
  · intro i j
    show V.hT (x j) (x i) = 0
    exact hTX (hxX j) (hxX i)
  · intro i j
    show V.hT (x' j) (x' i) = 0
    exact hTX' (hx'X j) (hx'X i)
  · intro i j
    show V.hT (x' j) (x i) = _
    rw [← hT_herm, hxx']
    split_ifs <;> simp

end GlobalTheory.IsoDuality
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_bases_isotropic_subspaces_duality : ∀ {D : D7} {V : HSp D} (X X' : Submodule D.host.E V.V), X ≠ ⊥ → X ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X → X' ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X' → (∀ x ∈ X, (∀ y ∈ X', V.hD x y = 0) → x = 0) → (∀ y ∈ X', (∀ x ∈ X, V.hD x y = 0) → y = 0) → ∃ (a : ℕ) (x x' : Fin a → V.V), 0 < a ∧ a ≤ wittIndex V ∧ Submodule.span D.host.E (Set.range x) = X ∧ Submodule.span D.host.E (Set.range x') = X' ∧ LinearIndependent D.host.E (Sum.elim x x') ∧ (∀ i j, V.hD (x i) (x j) = 0) ∧ (∀ i j, V.hD (x' i) (x' j) = 0) ∧ (∀ i j, V.hD (x i) (x' j) = if i = j then 1 else 0) := by
  atlas_forward_decl GlobalTheory.IsoDuality.exists_dual_bases
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.WittCarry

theorem exists_GF_carry_hyperbolic : ∀ {D : D7} {V : HSp D} (Φ : WittFrame V) {a : ℕ} (ha : a ≤ wittIndex V) (x x' : Fin a → V.V), LinearIndependent D.host.E (Sum.elim x x') → (∀ i j, V.hD (x i) (x j) = 0) → (∀ i j, V.hD (x' i) (x' j) = 0) → (∀ i j, V.hD (x i) (x' j) = if i = j then 1 else 0) → ∃ g : GF V, ∀ i, GlobalTheory.Cusp.ratAct D.sp.cm V g (x i) = Φ.e (Fin.castLE ha i) ∧ GlobalTheory.Cusp.ratAct D.sp.cm V g (x' i) = Φ.f (Fin.castLE ha i) := by
  intro D V Φ a ha x x' hli h1 h2 h3
  classical
  have hs : ∀ u w, star (V.hT u w) = V.hT w u := fun u w => V.herm.eq u w
  have hn : ∀ u, (∀ w, V.hT u w = 0) → u = 0 := fun u hu => V.nondeg.1 u hu
  have sw : ∀ u w, V.hD u w = star (V.hD w u) := fun u w => (hs u w).symm
  have hcast : ∀ i j : Fin a, (Fin.castLE ha i = Fin.castLE ha j) ↔ i = j :=
    fun i j => (Fin.castLE_injective ha).eq_iff
  let e' : Fin a → V.V := fun i => Φ.e (Fin.castLE ha i)
  let f' : Fin a → V.V := fun i => Φ.f (Fin.castLE ha i)
  have hli' : LinearIndependent D.host.E (Sum.elim e' f') := by
    refine LinearIndependent.of_pairwise_dual_eq_zero_one _
      (Sum.elim (fun i => V.hT (f' i)) (fun i => V.hT (e' i))) ?_ ?_
    · rintro (i | i) (j | j) hij
      · have : Fin.castLE ha j ≠ Fin.castLE ha i := fun h => hij (congrArg Sum.inl ((hcast j i).1 h).symm)
        exact (Φ.ef _ _).trans (if_neg this)
      · exact Φ.ff _ _
      · exact Φ.ee _ _
      · have : Fin.castLE ha i ≠ Fin.castLE ha j := fun h => hij (congrArg Sum.inr ((hcast i j).1 h))
        show V.hD (f' j) (e' i) = 0
        rw [sw]; show star (V.hD (Φ.e (Fin.castLE ha i)) (Φ.f (Fin.castLE ha j))) = 0
        rw [Φ.ef, if_neg this, star_zero]
    · rintro (i | i)
      · exact (Φ.ef _ _).trans (if_pos rfl)
      · show V.hD (f' i) (e' i) = 1
        rw [sw]; show star (V.hD (Φ.e (Fin.castLE ha i)) (Φ.f (Fin.castLE ha i))) = 1
        rw [Φ.ef, if_pos rfl, star_one]
  have hg : ∀ p q, V.hT (Sum.elim x x' p) (Sum.elim x x' q) = V.hT (Sum.elim e' f' p) (Sum.elim e' f' q) := by
    rintro (i | i) (j | j)
    · show V.hD (x j) (x i) = V.hD (e' j) (e' i)
      rw [h1, Φ.ee]
    · show V.hD (x' j) (x i) = V.hD (f' j) (e' i)
      rw [sw, sw (f' j)]
      show star (V.hD (x i) (x' j)) = star (V.hD (Φ.e (Fin.castLE ha i)) (Φ.f (Fin.castLE ha j)))
      rw [h3, Φ.ef]; simp only [hcast]
    · show V.hD (x j) (x' i) = V.hD (e' j) (f' i)
      show _ = V.hD (Φ.e (Fin.castLE ha j)) (Φ.f (Fin.castLE ha i))
      rw [h3, Φ.ef]; simp only [hcast]
    · show V.hD (x' j) (x' i) = V.hD (f' j) (f' i)
      rw [h2, Φ.ff]
  obtain ⟨g, hgB, hgv⟩ := GlobalTheory.LocOver.WittFrames.exists_isom_of_gram witt_extension_theorem V.hT hs hn _ _ hli hli' hg
  let M : Matrix (Fin V.rank) (Fin V.rank) D.host.E := LinearMap.toMatrix V.frame V.frame g.toLinearMap
  let N : Matrix (Fin V.rank) (Fin V.rank) D.host.E := LinearMap.toMatrix V.frame V.frame g.symm.toLinearMap
  have hMN : M * N = 1 := by
    rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_one V.frame]; congr 1; ext y; simp
  have hNM : N * M = 1 := by
    rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_one V.frame]; congr 1; ext y; simp
  let U : GL (Fin V.rank) D.host.E := ⟨M, N, hMN, hNM⟩
  have hrat : ∀ γ : GF V, γ.1 = U → GlobalTheory.Cusp.ratAct D.sp.cm V γ = g.toLinearMap := fun γ h => by
    show Matrix.toLin V.frame V.frame γ.1.1 = _
    rw [h]; exact Matrix.toLin_toMatrix _ _ _
  refine ⟨⟨U, ?_⟩, fun i => ?_⟩
  · show Formalism.UG.cT _ M * V.gram * M = V.gram
    funext i j
    have hexp : ∀ k, g (V.frame k) = ∑ l, M l k • V.frame l := fun k => by
      conv_lhs => rw [← V.frame.sum_repr (g (V.frame k))]
      simp [M, LinearMap.toMatrix_apply]
    rw [show V.gram i j = V.hT (V.frame i) (V.frame j) from rfl, ← hgB, hexp, hexp]
    simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, map_sum, map_smulₛₗ,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    have hσ : ∀ z, (D.sp.cm.sig : D.host.E →+* D.host.E) z = star z := fun z => rfl
    simp only [hσ, starRingEnd_apply, HSpace.gram, RingHom.id_apply]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  · rw [hrat _ rfl]
    exact ⟨hgv (Sum.inl i), hgv (Sum.inr i)⟩

end GlobalTheory.WittCarry
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_carry_hyperbolicFamily_wittFrame : ∀ {D : D7} {V : HSp D} (Φ : WittFrame V) {a : ℕ} (ha : a ≤ wittIndex V) (x x' : Fin a → V.V), LinearIndependent D.host.E (Sum.elim x x') → (∀ i j, V.hD (x i) (x j) = 0) → (∀ i j, V.hD (x' i) (x' j) = 0) → (∀ i j, V.hD (x i) (x' j) = if i = j then 1 else 0) → ∃ g : GF V, ∀ i, GlobalTheory.Cusp.ratAct D.sp.cm V g (x i) = Φ.e (Fin.castLE ha i) ∧ GlobalTheory.Cusp.ratAct D.sp.cm V g (x' i) = Φ.f (Fin.castLE ha i) := by
  atlas_forward_decl GlobalTheory.WittCarry.exists_GF_carry_hyperbolic
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.Cusp.ConjLevi

variable {D : D7} {V : HSp D}

theorem ratAct_mul_apply (a b : GF V) (v : V.V) :
    GlobalTheory.Cusp.ratAct D.sp.cm V (a * b) v = GlobalTheory.Cusp.ratAct D.sp.cm V a (GlobalTheory.Cusp.ratAct D.sp.cm V b v) := by
  simp only [GlobalTheory.Cusp.ratAct]
  rw [show (a * b).1.1 = a.1.1 * b.1.1 from rfl, Matrix.toLin_mul V.frame V.frame V.frame]
  rfl

theorem ratAct_one_apply (v : V.V) : GlobalTheory.Cusp.ratAct D.sp.cm V 1 v = v := by
  simp only [GlobalTheory.Cusp.ratAct]
  rw [show (1 : GF V).1.1 = 1 from rfl, Matrix.toLin_one]
  rfl

theorem ratAct_inv_apply (g : GF V) (v : V.V) :
    GlobalTheory.Cusp.ratAct D.sp.cm V g⁻¹ (GlobalTheory.Cusp.ratAct D.sp.cm V g v) = v := by
  rw [← ratAct_mul_apply, inv_mul_cancel, ratAct_one_apply]

theorem conj_maps (γ g : GF V) (S : Submodule D.host.E V.V)
    (h : ∀ v ∈ S, GlobalTheory.Cusp.ratAct D.sp.cm V γ v ∈ S) :
    ∀ w ∈ S.map (GlobalTheory.Cusp.ratAct D.sp.cm V g),
      GlobalTheory.Cusp.ratAct D.sp.cm V (g * γ * g⁻¹) w ∈ S.map (GlobalTheory.Cusp.ratAct D.sp.cm V g) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [ratAct_mul_apply, ratAct_inv_apply, ratAct_mul_apply]
  exact ⟨_, h y hy, rfl⟩

theorem map_span_range (g : GF V) {a : ℕ} (x : Fin a → V.V) (y : Fin a → V.V)
    (hx : ∀ i, GlobalTheory.Cusp.ratAct D.sp.cm V g (x i) = y i) :
    (Submodule.span D.host.E (Set.range x)).map (GlobalTheory.Cusp.ratAct D.sp.cm V g) =
      Submodule.span D.host.E (Set.range y) := by
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext i
  exact hx i

end GlobalTheory.Cusp.ConjLevi

open GlobalTheory.Cusp.ConjLevi in

theorem GlobalTheory.Cusp.ConjLevi.conj_mem_levi_stdVec : ∀ {D : D7} {V : HSp D} (Φ : WittFrame V) (γ g : GF V) {a : ℕ} (ha : a ≤ wittIndex V) (j : Fin (wittIndex V)), j.val + 1 = a → ∀ (x x' : Fin a → V.V), (∀ i, GlobalTheory.Cusp.ratAct D.sp.cm V g (x i) = Φ.e (Fin.castLE ha i)) → (∀ i, GlobalTheory.Cusp.ratAct D.sp.cm V g (x' i) = Φ.f (Fin.castLE ha i)) → (∀ v ∈ Submodule.span D.host.E (Set.range x), GlobalTheory.Cusp.ratAct D.sp.cm V γ v ∈ Submodule.span D.host.E (Set.range x)) → (∀ v ∈ Submodule.span D.host.E (Set.range x'), GlobalTheory.Cusp.ratAct D.sp.cm V γ v ∈ Submodule.span D.host.E (Set.range x')) → rat V (g * γ * g⁻¹) ∈ Φ.levi D.sp.cm (AF D.host.F) {stdVec j} := by
  intro D V Φ γ g a ha j hj x x' hx hx' h1 h2
  have hmem : ∀ i : Fin (wittIndex V), i ≤ j ↔ ∃ k : Fin a, Fin.castLE ha k = i := fun i => by
    constructor
    · intro hi
      exact ⟨⟨i.val, by have := Fin.le_def.1 hi; omega⟩, Fin.ext rfl⟩
    · rintro ⟨k, rfl⟩
      exact Fin.le_def.2 (by simp only [Fin.val_castLE]; omega)
  have hE : Φ.sub (stdVec j) = Submodule.span D.host.E (Set.range fun i : Fin a => Φ.e (Fin.castLE ha i)) := by
    rw [WittFrame.sub]
    congr 1
    ext v
    simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, stdVec]
    constructor
    · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · by_cases h : i ≤ j
        · obtain ⟨k, rfl⟩ := (hmem i).1 h; exact ⟨k, rfl⟩
        · rw [if_neg h] at hi; exact absurd hi (by decide)
      · by_cases h : i ≤ j
        · rw [if_pos h] at hi; exact absurd hi (by decide)
        · rw [if_neg h] at hi; exact absurd hi (by decide)
    · rintro ⟨k, rfl⟩
      exact Or.inl ⟨_, by rw [if_pos ((hmem _).2 ⟨k, rfl⟩)], rfl⟩
  have hF : Φ.sub (-stdVec j) = Submodule.span D.host.E (Set.range fun i : Fin a => Φ.f (Fin.castLE ha i)) := by
    rw [WittFrame.sub]
    congr 1
    ext v
    simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, stdVec, Pi.neg_apply]
    constructor
    · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · by_cases h : i ≤ j
        · rw [if_pos h] at hi; exact absurd hi (by decide)
        · rw [if_neg h] at hi; exact absurd hi (by decide)
      · by_cases h : i ≤ j
        · obtain ⟨k, rfl⟩ := (hmem i).1 h; exact ⟨k, rfl⟩
        · rw [if_neg h] at hi; exact absurd hi (by decide)
    · rintro ⟨k, rfl⟩
      refine Or.inr ⟨_, ?_, rfl⟩
      rw [if_pos ((hmem _).2 ⟨k, rfl⟩)]
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  unfold WittFrame.levi
  simp only [Finset.mem_singleton, iInf_iInf_eq_left]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · show GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.diagH _ _ _ (g * γ * g⁻¹) ∈ _
    rw [GlobalTheory.Cusp.diagH_mem_parab, hE, ← map_span_range g x _ hx]
    exact conj_maps γ g _ h1
  · show GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.diagH _ _ _ (g * γ * g⁻¹) ∈ _
    rw [GlobalTheory.Cusp.diagH_mem_parab, hF, ← map_span_range g x' _ hx']
    exact conj_maps γ g _ h2
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_mem_standardLevi_wittFrame : ∀ {D : D7} {V : HSp D} (Φ : WittFrame V) (γ g : GF V) {a : ℕ} (ha : a ≤ wittIndex V) (j : Fin (wittIndex V)), j.val + 1 = a → ∀ (x x' : Fin a → V.V), (∀ i, GlobalTheory.Cusp.ratAct D.sp.cm V g (x i) = Φ.e (Fin.castLE ha i)) → (∀ i, GlobalTheory.Cusp.ratAct D.sp.cm V g (x' i) = Φ.f (Fin.castLE ha i)) → (∀ v ∈ Submodule.span D.host.E (Set.range x), GlobalTheory.Cusp.ratAct D.sp.cm V γ v ∈ Submodule.span D.host.E (Set.range x)) → (∀ v ∈ Submodule.span D.host.E (Set.range x'), GlobalTheory.Cusp.ratAct D.sp.cm V γ v ∈ Submodule.span D.host.E (Set.range x')) → rat V (g * γ * g⁻¹) ∈ Φ.levi D.sp.cm (AF D.host.F) {stdVec j} := by
  atlas_forward_decl GlobalTheory.Cusp.ConjLevi.conj_mem_levi_stdVec
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp

namespace GlobalTheory.ConjLevi

theorem exists_conj_mem_levi : ∀ {D : D7} {V : HSp D}, 0 < V.rank → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → ∀ (Φ : WittFrame V) (γ : GF V), IsRegSS γ.1.1 → ¬ Irreducible γ.1.1.charpoly → ¬ IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1 → ∃ (g : GF V) (P : Finset (SV (wittIndex V))), IsPar P ∧ P.Nonempty ∧ rat V (g * γ * g⁻¹) ∈ Φ.levi D.sp.cm (AF D.host.F) P := by
  intro D V hr hRS Φ γ hss hirr hnf
  have hreg := GlobalTheory.T.isRegularSemisimpleUnitaryData_of_regular γ hss
  obtain ⟨hA, hP, -, hR, -⟩ := hRS.1 D.host.F D.host.E (Fin V.rank) D.sp.cm.sig V.gram γ.1 hreg
  obtain ⟨k, K, hK1, hK2, he, i, hi⟩ := GlobalTheory.T.exists_split_factor_regularSemisimple_reducible D.sp.cm.sig V.gram γ.1 hr hss hA hR hirr hnf
  obtain ⟨ε, hεL, hεε, hε0, hεi⟩ :=
    @GlobalTheory.T.exists_isotropic_idempotent_of_split_factor _ _ _ _ _ _ _ D.sp.cm.sig V.gram γ.1 hreg hA hP k K hK1 hK2 he i hi
  obtain ⟨X, X', hX0, hXi, hX'i, hXs, hX's, hn1, hn2⟩ := GlobalTheory.T.isotropicIdempotent_gives_dual_stable_subspaces γ ε hεL hεε hε0 hεi
  obtain ⟨a, x, x', ha0, ha, hx, hx', hli, hee, hff, hef⟩ := GlobalTheory.T.exists_dual_bases_isotropic_subspaces_duality X X' hX0 hXi hX'i hn1 hn2
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_unitary_carry_hyperbolicFamily_wittFrame Φ ha x x' hli hee hff hef
  refine ⟨g, {stdVec ⟨a - 1, by omega⟩}, ?_, Finset.singleton_nonempty _, ?_⟩
  · have := isPar_stdPar ({⟨a - 1, by omega⟩} : Finset (Fin (wittIndex V)))
    simpa [stdPar] using this
  · exact GlobalTheory.T.conj_mem_standardLevi_wittFrame Φ γ g ha ⟨a - 1, by omega⟩ (by simp only; omega) x x' (fun i => (hg i).1)
      (fun i => (hg i).2) (by rw [hx]; exact hXs) (by rw [hx']; exact hX's)

end GlobalTheory.ConjLevi
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_mem_standardLevi_of_reducible_charpoly : ∀ {D : D7} {V : HSp D}, 0 < V.rank → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → ∀ (Φ : WittFrame V) (γ : GF V), IsRegSS γ.1.1 → ¬ Irreducible γ.1.1.charpoly → ¬ IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1 → ∃ (g : GF V) (P : Finset (SV (wittIndex V))), IsPar P ∧ P.Nonempty ∧ rat V (g * γ * g⁻¹) ∈ Φ.levi D.sp.cm (AF D.host.F) P := by
  atlas_forward_decl GlobalTheory.ConjLevi.exists_conj_mem_levi
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.KTClass

theorem tsum_conj_eq_classKernel {D : D7} {V : HSp D} (γ : GF V) (f : GA D V → ℂ) (x : GA D V) :
    ∑' δ : {δ : GF V | IsConj γ δ}, f (x⁻¹ * rat V δ * x) =
      GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f x := by
  have hGQ : ∀ g, g ∈ GQ V ↔ ∃ c, rat V c = g := fun g => by
    rw [show GQ V = (rat V).range from (range_ratEmb ..).symm]; rfl
  have himg : (rat V) '' {δ | IsConj γ δ} = GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass (GQ V) (rat V γ) := by
    ext y; constructor
    · rintro ⟨δ, hδ, rfl⟩
      obtain ⟨c, rfl⟩ := isConj_iff.1 hδ
      exact ⟨rat V c⁻¹, (hGQ _).2 ⟨c⁻¹, rfl⟩, by simp [map_mul, map_inv, mul_assoc]⟩
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨c, rfl⟩ := (hGQ g).1 hg
      exact ⟨c⁻¹ * γ * c, isConj_iff.2 ⟨c⁻¹, by group⟩, by simp [map_mul, map_inv]⟩
  rw [GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel, ← himg,
    tsum_image (fun y => f (x⁻¹ * y * x)) (ratEmb_injective _ _).injOn]

theorem kT_eq_classKernel : ∀ {D : D7} {V : HSp D}, GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm → ∀ {lam : D.what₂.Tau → Fin V.rank → ℤ} {S : D.what₂.Tau → SPar} {M : DSModel V S} {T : TypeDataG V} {U : AuxiliaryPlaceHermitianSpace V} {μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)} {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)} {μ : Measure (GA D V)} {fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}, IsTestData V lam M T U μa μf μ fa ff → ∀ (Φ : WittFrame V) (K : Subgroup (GA D V)) (γ : GF V) (Tr : A0 (wittIndex V)) (x : GA D V), kT Φ K {δ | IsConj γ δ} (tensor D.sp.cm.sig V.gram fa ff) Tr x = classKernel (GQ V) (rat V γ) (tensor D.sp.cm.sig V.gram fa ff) x := by
  intro D V hPC lam S M T U μa μf μ fa ff hTD Φ K γ Tr x
  obtain ⟨hodd, -, -, hnf, hμ, ha, hb⟩ := hTD
  have hH := (GlobalTheory.T.typeHypothesis_forms_agree D V T hnf).1
  haveI : ∀ w, (μa w).IsHaarMeasure := hμ.haar_arch
  haveI : ∀ v, (μf v).IsHaarMeasure := hμ.haar_loc
  have hU : ∀ 𝔉 : IsoFlag V, 𝔉.Proper →
      GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.UnipIntegralsVanish 𝔉 (tensor D.sp.cm.sig V.gram fa ff) := fun 𝔉 h𝔉 =>
    (hPC.2 D V hodd S M T hH U μa μf _ ⟨fa, ff, ha, hb, rfl⟩ 𝔉 h𝔉).1
  have hcl : ∀ δ ∈ {δ : GF V | IsConj γ δ}, ∀ g, g * δ * g⁻¹ ∈ {δ : GF V | IsConj γ δ} :=
    fun δ hδ g => (show IsConj γ δ from hδ).trans (isConj_iff.2 ⟨g, rfl⟩)
  rw [GlobalTheory.T.truncated_kernel_orbit_sum D V Φ K _ hU _ hcl Tr x]
  exact tsum_conj_eq_classKernel γ _ x

end GlobalTheory.KTClass
end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_data_trace_identity : ∀ {D : D7} {V : HSp D}, GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm → ∀ {lam : D.what₂.Tau → Fin V.rank → ℤ} {S : D.what₂.Tau → SPar} {M : DSModel V S} {T : TypeDataG V} {U : AuxiliaryPlaceHermitianSpace V} {μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)} {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)} {μ : Measure (GA D V)} {fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}, IsTestData V lam M T U μa μf μ fa ff → ∀ (Φ : WittFrame V) (K : Subgroup (GA D V)) (γ : GF V) (Tr : A0 (wittIndex V)) (x : GA D V), kT Φ K {δ | IsConj γ δ} (tensor D.sp.cm.sig V.gram fa ff) Tr x = classKernel (GQ V) (rat V γ) (tensor D.sp.cm.sig V.gram fa ff) x := by
  atlas_forward_decl GlobalTheory.KTClass.kT_eq_classKernel
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitTorusZero

open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp

variable {D : D7} {V : HSp D}

theorem exists_minLevi (Φ : WittFrame V) (γ : GF V) :
    ∃ (g : GF V) (P : Finset (SV (wittIndex V))), IsMinLevi Φ (g * γ * g⁻¹) P := by
  classical
  let A : Finset (Finset (SV (wittIndex V))) := Finset.univ.filter fun P =>
    IsPar P ∧ ∃ g : GF V, rat V (g * γ * g⁻¹) ∈ Φ.levi D.sp.cm (AF D.host.F) P
  have hA : (∅ : Finset (SV (wittIndex V))) ∈ A := by
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨by simp, by simp⟩, 1, ?_⟩
    simp [WittFrame.levi]
  obtain ⟨P, hPA, hmax⟩ := A.exists_max_image Finset.card ⟨_, hA⟩
  obtain ⟨hP, g, hg⟩ := (Finset.mem_filter.1 hPA).2
  refine ⟨g, P, hP, hg, fun g' P' hP' h' => hmax P' (Finset.mem_filter.2 ⟨Finset.mem_univ _, hP', g' * g, ?_⟩)⟩
  have e : g' * g * γ * (g' * g)⁻¹ = g' * (g * γ * g⁻¹) * g'⁻¹ := by group
  rw [e]; exact h'

theorem rat_mem_GQ (g : GF V) : rat V g ∈ GQ V := by
  rw [GlobalTheory.AdelicU.GQ_eq, ← GlobalTheory.AdelicU.range_ratEmb]; exact ⟨g, rfl⟩

theorem zeroClause_of_conj (μ : Measure (GA D V)) (f : GA D V → ℂ) (γ g : GF V)
    (h : ZeroClause μ f (rat V (g * γ * g⁻¹))) : ZeroClause μ f (rat V γ) := by
  have hg := rat_mem_GQ g
  have e : ratClass (GQ V) (rat V (g * γ * g⁻¹)) = ratClass (GQ V) (rat V γ) := by
    ext δ
    simp only [ratClass, Set.mem_ofPred_eq, map_mul, map_inv]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(rat V g)⁻¹ * k, mul_mem (inv_mem hg) hk, by group⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨rat V g * k, mul_mem hg hk, by group⟩
  intro 𝓕 h𝓕
  have := h 𝓕 h𝓕
  unfold HasClassInt classKernel at *
  rw [e] at this
  exact this

theorem summable_class {f : GA D V → ℂ} (hf : HasCompactSupport f) {γ : GA D V} (hγ : γ ∈ GQ V) (x : GA D V) :
    Summable fun δ : ratClass (GQ V) γ => f (x⁻¹ * δ * x) := by
  have hmem : ∀ δ : ratClass (GQ V) γ, (δ : GA D V) ∈ GQ V := fun ⟨δ, k, hk, e⟩ => e ▸ mul_mem (mul_mem (inv_mem hk) hγ) hk
  let ι : ratClass (GQ V) γ → GQ V := fun δ => ⟨δ, hmem δ⟩
  have hι : Function.Injective ι := fun a b e => Subtype.ext (congrArg (fun z : GQ V => (z : GA D V)) e)
  apply summable_of_hasFiniteSupport
  refine ((GlobalTheory.AutomorphicL2Unitary.finite_support_kernel (Γ := GQ V) hf x x).preimage hι.injOn).subset ?_
  intro δ hδ
  exact hδ

theorem fd_of_quot {μ : Measure (GA D V)} [μ.IsHaarMeasure] {𝓕 : Set (GA D V)} (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
    {φ : GA D V → ℂ} (hφ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ) (hi : Integrable (descend (GQ V) φ) (autMeasure V μ)) :
    IntegrableOn φ 𝓕 μ ∧ ∫ x in 𝓕, φ x ∂μ = ∫ q, descend (GQ V) φ q ∂autMeasure V μ := by
  refine ⟨?_, ?_⟩
  · have := (GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff h𝓕 (p := 1)).1 (memLp_one_iff_integrable.2 hi)
    rw [hφ.lift_descend] at this
    exact memLp_one_iff_integrable.1 this
  · rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕]
    exact congrArg (fun F => ∫ x in 𝓕, F x ∂μ) hφ.lift_descend.symm

theorem exists_regular {k : ℕ} (c c' : ℝ) : ∃ T : A0 k, Regular c T ∧ Regular c' T := by
  set C := max (max c c') 1
  have h1 : c ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have h2 : c' ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have h3 : 1 ≤ C := le_max_right _ _
  have key : ∀ b, b ≤ C → Regular b (WithLp.toLp 2 fun i : Fin k => C * ((k : ℝ) - i) : A0 k) := fun b hb => by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
      nlinarith
    · have : (i : ℝ) + 1 ≤ k := by exact_mod_cast i.2
      nlinarith
  exact ⟨_, key c h1, key c' h2⟩

theorem exists_haar_cent (γ : GA D V) : ∃ dt : Measure (cent γ), dt.IsHaarMeasure := by
  have : LocallyCompactSpace (cent γ) := (GlobalTheory.Orb.isClosed_cent γ).isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact ⟨Measure.haar, inferInstance⟩

theorem hyperZero : GlobalTheory.Published.LabesseWaldspurger → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm →
    GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → HyperZero := by
  intro hLW hPC hTV hRS D V lam S M T U μa μf μ _ _ fa ff hTD γ hreg hirr hna
  obtain ⟨Φ, L, a, hgood⟩ := exists_isGood V
  obtain ⟨g, P, hP⟩ := exists_minLevi Φ γ
  refine zeroClause_of_conj μ _ γ g ?_
  set γ0 := g * γ * g⁻¹ with hγ0
  have hreg0 : IsRegSS γ0.1.1 := by
    show IsRegSS ((g.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * γ.1.1 * ((g.1)⁻¹ : GL (Fin V.rank) D.host.E).1)
    unfold IsRegSS
    rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj]
    exact hreg
  have hPne : P ≠ ∅ := by
    obtain ⟨g', P', hpar', hne', hmem'⟩ := GlobalTheory.T.exists_conj_mem_standardLevi_of_reducible_charpoly hTD.1.pos hRS Φ γ hreg hirr hna
    have e : g' * g⁻¹ * γ0 * (g' * g⁻¹)⁻¹ = g' * γ * g'⁻¹ := by rw [hγ0]; group
    have hle := hP.2.2 (g' * g⁻¹) P' hpar' (e ▸ hmem')
    rintro rfl
    have := Finset.card_pos.2 hne'
    rw [Finset.card_empty] at hle
    omega
  have hf : tensor D.sp.cm.sig V.gram fa ff ∈ CcGA V :=
    (IsTestFnG.isPureTensor ⟨fa, ff, hTD.2.2.2.2.2.1, hTD.2.2.2.2.2.2, rfl⟩).2
  obtain ⟨c1, hc1⟩ := ((hLW.2 D V Φ L a hgood).2 μ).1 _ hf
  obtain ⟨dt, hdt⟩ := exists_haar_cent (rat V γ0)
  obtain ⟨c2, hc2⟩ := ((hLW.2 D V Φ L a hgood).2 μ).2 _ hf γ0 hreg0 P hP dt
  obtain ⟨Tr, h1, h2⟩ := exists_regular (k := wittIndex V) c1 c2
  have hint := (hc1 Tr h1).1 _ (GlobalTheory.regSS_conjClass_isSSClass γ0 hreg0)
  have heq := (hc2 Tr h2).2
  have hz := GlobalTheory.T.elliptic_trace_from_model hLW hPC hTV hRS D V lam S M T U μa μf μ fa ff hTD Φ L a hgood γ0 hreg0 P hP hPne dt Tr
  have hk : kT Φ (levelAll D.sp.cm.sig V.gram L a) {δ | IsConj γ0 δ} (tensor D.sp.cm.sig V.gram fa ff) Tr =
      classKernel (GQ V) (rat V γ0) (tensor D.sp.cm.sig V.gram fa ff) :=
    funext (GlobalTheory.T.test_data_trace_identity hPC hTD Φ _ γ0 Tr)
  rw [hk] at hint heq
  intro 𝓕 h𝓕
  have hinv : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) (classKernel (GQ V) (rat V γ0) (tensor D.sp.cm.sig V.gram fa ff)) :=
    fun δ hδ x => classKernel_mul _ _ hδ x
  obtain ⟨hi, hv⟩ := fd_of_quot h𝓕 hinv hint
  refine ⟨summable_class (GlobalTheory.Orb.continuous_of_mem_ccAd hf).2 (rat_mem_GQ γ0), hi, ?_⟩
  rw [hv, heq, hz, mul_zero]

end GlobalTheory.SplitTorusZero
end
end
