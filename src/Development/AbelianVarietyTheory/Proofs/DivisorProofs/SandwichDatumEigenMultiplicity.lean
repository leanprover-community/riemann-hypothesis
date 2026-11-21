import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepTraceEqMulAlgebraTraceDvr
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfIsDomainMuNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixSandwichTraceEq

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory.Proof.sandwich_datum_actions_ring_homs

theorem actions_ringHom : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (h : ℕ) (D : Datum ε h Λ), (∃ ρ : Λ →+* Matrix (Fin h) (Fin h) O, ⇑ρ = actT D) ∧ (∃ ρ : Λ →+* Matrix (Fin h) (Fin h) O, ⇑ρ = actH D) := by
  intro p _ O _ _ _ ε Λ _ _ h D
  exact ⟨⟨(RingHom.mapMatrix (padicToO p O)).comp (D.ρT : Λ →+* Matrix (Fin h) (Fin h) ℤ_[p]), rfl⟩,
    ⟨(RingHom.mapMatrix (WittVector.fontaineTheta O p)).comp D.ρM, rfl⟩⟩

end GlobalTheory.Proof.sandwich_datum_actions_ring_homs
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sandwich_datum_actions_ring_homs : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (h : ℕ) (D : Datum ε h Λ), (∃ ρ : Λ →+* Matrix (Fin h) (Fin h) O, ⇑ρ = actT D) ∧ (∃ ρ : Λ →+* Matrix (Fin h) (Fin h) O, ⇑ρ = actH D) := by
  atlas_forward_decl GlobalTheory.Proof.sandwich_datum_actions_ring_homs.actions_ringHom
end

section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_isDomain_mu_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p → IsDomain (Ainf p O) ∧ mu ε ≠ 0 := by
  first | exact @GlobalTheory.ainf_isDomain_and_mu_ne_zero | exact GlobalTheory.ainf_isDomain_and_mu_ne_zero | (intros; apply GlobalTheory.ainf_isDomain_and_mu_ne_zero <;> assumption)
end

section
section
noncomputable section

open WittVector GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem trace_actH_eq_trace_actT : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (h : ℕ) (D : Datum ε h Λ) (a : Λ), (actH D a).trace = (actT D a).trace ∧ (actT D a).trace = padicToO p O (D.ρT a).trace := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ h D a
  obtain ⟨hdom, hmu⟩ := GlobalTheory.T.ainf_isDomain_mu_ne_zero p C v O hv ε hε
  haveI := hdom
  obtain ⟨-, -, htr⟩ := GlobalTheory.T.matrix_sandwich_trace_eq (Ainf p O) h (mu ε) D.F D.G
    ((D.ρT a).map (ofPadic p O)) (D.ρM a) hmu D.G_mul_F (D.F_act a)
  have hT : (actT D a).trace = fontaineTheta O p (((D.ρT a).map (ofPadic p O)).trace) := by
    simp only [actT, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum, padicToO,
      RingHom.comp_apply]
  have hH : (actH D a).trace = fontaineTheta O p ((D.ρM a).trace) := by
    simp only [actH, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
  refine ⟨by rw [hH, hT, htr], ?_⟩
  rw [hT]
  simp only [padicToO, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum, RingHom.comp_apply]

end GlobalTheory
end
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sandwich_datum_trace_eq : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (h : ℕ) (D : Datum ε h Λ) (a : Λ), (actH D a).trace = (actT D a).trace ∧ (actT D a).trace = padicToO p O (D.ρT a).trace := by
  atlas_forward_decl GlobalTheory.trace_actH_eq_trace_actT
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem torsionFree_of_finite_domain_action
    (R Λ : Type) [CommRing R] [IsDomain R] [CommRing Λ] [IsDomain Λ] [Algebra R Λ]
    [Module.Finite R Λ] [FaithfulSMul R Λ] (h : ℕ)
    (ρ : Λ →ₐ[R] Matrix (Fin h) (Fin h) R) (a : Λ) (x : Fin h → R)
    (ha : a ≠ 0) (hx : (ρ a).mulVec x = 0) : x = 0 := by
  have hint : IsIntegral R a := Algebra.IsIntegral.isIntegral a
  have halg : IsAlgebraic R a := hint.isAlgebraic
  obtain ⟨c, hc, a', hca⟩ := halg.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero ha)
  have hc0 : c ≠ 0 := by
    exact hc
  have key : c • x = 0 := by
    have h1 : ρ (algebraMap R Λ c) = c • (1 : Matrix (Fin h) (Fin h) R) := by
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    have h2 : (ρ (algebraMap R Λ c)).mulVec x = c • x := by
      rw [h1, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [← h2, hca, mul_comm, map_mul, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  funext i
  have hi : c * x i = 0 := by simpa using congrFun key i
  simpa [hc0] using hi

theorem torsionFree_of_finite_domain_action' :
    ∀ (R Λ : Type) [CommRing R] [IsDomain R] [CommRing Λ] [IsDomain Λ] [Algebra R Λ] [Module.Finite R Λ] [FaithfulSMul R Λ] (h : ℕ) (ρ : Λ →ₐ[R] Matrix (Fin h) (Fin h) R) (a : Λ) (x : Fin h → R), a ≠ 0 → (ρ a).mulVec x = 0 → x = 0 :=
  fun R Λ _ _ _ _ _ _ _ h ρ a x ha hx => torsionFree_of_finite_domain_action R Λ h ρ a x ha hx

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.faithful_rep_mulVec_injective : ∀ (R Λ : Type) [CommRing R] [IsDomain R] [CommRing Λ] [IsDomain Λ] [Algebra R Λ] [Module.Finite R Λ] [FaithfulSMul R Λ] (h : ℕ) (ρ : Λ →ₐ[R] Matrix (Fin h) (Fin h) R) (a : Λ) (x : Fin h → R), a ≠ 0 → (ρ a).mulVec x = 0 → x = 0 := by
  atlas_forward_decl GlobalTheory.torsionFree_of_finite_domain_action'
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem trace_lsmul_free_eq_finrank_mul_trace (R Λ M : Type) [CommRing R] [Nontrivial R] [CommRing Λ] [Nontrivial Λ] [Algebra R Λ] [Module.Free R Λ] [Module.Finite R Λ] [AddCommGroup M] [Module R M] [Module Λ M] [IsScalarTower R Λ M] [Module.Free Λ M] [Module.Finite Λ M] (a : Λ) :
    LinearMap.trace R M (Algebra.lsmul R R M a) = (Module.finrank Λ M : R) * Algebra.trace R Λ a := by
  classical
  let b := Module.Free.chooseBasis R Λ
  let e := Module.Free.chooseBasis Λ M
  rw [LinearMap.trace_eq_matrix_trace R (b.smulTower e), Algebra.trace_eq_matrix_trace b,
    Module.finrank_eq_card_chooseBasisIndex]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, LinearMap.toMatrix_apply,
    Module.Basis.smulTower_apply, Module.Basis.smulTower_repr, Algebra.leftMulMatrix_eq_repr_mul]
  have h : ∀ i k, (b.repr ((e.repr (((Algebra.lsmul R R M) a) (b i • e k))) k)) i = (b.repr (a * b i)) i := by
    intro i k
    show (b.repr ((e.repr (a • (b i • e k))) k)) i = _
    rw [smul_smul, LinearEquiv.map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  simp only [h]
  rw [Finset.sum_comm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_lsmul_eq_finrank_mul_trace : ∀ (R Λ M : Type) [CommRing R] [Nontrivial R] [CommRing Λ] [Nontrivial Λ] [Algebra R Λ] [Module.Free R Λ] [Module.Finite R Λ] [AddCommGroup M] [Module R M] [Module Λ M] [IsScalarTower R Λ M] [Module.Free Λ M] [Module.Finite Λ M] (a : Λ), LinearMap.trace R M (Algebra.lsmul R R M a) = (Module.finrank Λ M : R) * Algebra.trace R Λ a := by
  atlas_forward_decl GlobalTheory.trace_lsmul_free_eq_finrank_mul_trace
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem traceOnLattice_eq_rank_mul_trace : ∀ (p : ℕ) [Fact p.Prime] (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (ρ : Λ →ₐ[ℤ_[p]] Matrix (Fin h) (Fin h) ℤ_[p]) (a : Λ), (ρ a).trace = (N : ℤ_[p]) * Algebra.trace ℤ_[p] Λ a := by
  intro p _ Λ _ _ _ _ _ _ N h hh ρ a
  let f : Λ →+* Module.End ℤ_[p] (Fin h → ℤ_[p]) :=
    ((Matrix.toLinAlgEquiv' : Matrix (Fin h) (Fin h) ℤ_[p] ≃ₐ[ℤ_[p]] _).toAlgHom.comp ρ).toRingHom
  letI : Module Λ (Fin h → ℤ_[p]) := Module.compHom _ f
  have hsmul : ∀ (b : Λ) (x : Fin h → ℤ_[p]), b • x = (ρ b).mulVec x := fun b x => rfl
  haveI : IsScalarTower ℤ_[p] Λ (Fin h → ℤ_[p]) := ⟨fun r b x => by
    rw [hsmul, hsmul, map_smul]
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]⟩
  haveI : Module.Finite Λ (Fin h → ℤ_[p]) := Module.Finite.of_restrictScalars_finite ℤ_[p] Λ _
  haveI : NoZeroSMulDivisors Λ (Fin h → ℤ_[p]) := ⟨fun {b x} hbx => by
    by_cases hb : b = 0
    · exact Or.inl hb
    · exact Or.inr (GlobalTheory.T.faithful_rep_mulVec_injective ℤ_[p] Λ h ρ b x hb (by rw [← hsmul]; exact hbx))⟩
  haveI : Module.Free Λ (Fin h → ℤ_[p]) := Module.free_of_finite_type_torsion_free'
  haveI : Module.IsTorsionFree ℤ_[p] Λ :=
    NoZeroSMulDivisors.iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective ℤ_[p] Λ)
  haveI : Module.Free ℤ_[p] Λ := Module.free_of_finite_type_torsion_free'
  have hrank : Module.finrank Λ (Fin h → ℤ_[p]) = N := by
    have h1 := Module.finrank_mul_finrank ℤ_[p] Λ (Fin h → ℤ_[p])
    rw [Module.finrank_fin_fun] at h1
    have h2 := h1.trans hh
    have hpos : 0 < Module.finrank ℤ_[p] Λ := Module.finrank_pos
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  have key := GlobalTheory.T.trace_lsmul_eq_finrank_mul_trace ℤ_[p] Λ (Fin h → ℤ_[p]) a
  rw [hrank] at key
  rw [← key]
  have hlin : Algebra.lsmul ℤ_[p] ℤ_[p] (Fin h → ℤ_[p]) a = Matrix.toLin' (ρ a) := by
    exact LinearMap.ext fun x => hsmul a x
  rw [hlin, Matrix.trace_toLin'_eq]

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rep_trace_eq_mul_algebra_trace : ∀ (p : ℕ) [Fact p.Prime] (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (ρ : Λ →ₐ[ℤ_[p]] Matrix (Fin h) (Fin h) ℤ_[p]) (a : Λ), (ρ a).trace = (N : ℤ_[p]) * Algebra.trace ℤ_[p] Λ a := by
  atlas_forward_decl GlobalTheory.traceOnLattice_eq_rank_mul_trace
end

section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem eig_decomp_T_H : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ), (iSupIndep (fun σ : Λ →+* O => eig C (actT D) σ) ∧ (⨆ σ : Λ →+* O, eig C (actT D) σ) = ⊤ ∧ ∀ τ : Λ →+* O, Module.finrank C (eig C (actT D) τ) = N) ∧ (iSupIndep (fun σ : Λ →+* O => eig C (actH D) σ) ∧ (⨆ σ : Λ →+* O, eig C (actH D) σ) = ⊤ ∧ ∀ τ : Λ →+* O, Module.finrank C (eig C (actH D) τ) = N) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ N h hh D
  obtain ⟨⟨ρT, hρT⟩, ⟨ρH, hρH⟩⟩ := GlobalTheory.T.sandwich_datum_actions_ring_homs p O ε Λ h D
  have hT : ∀ a, (ρT a).trace = (N : O) * padicToO p O (Algebra.trace ℤ_[p] Λ a) := by
    intro a
    rw [congrFun hρT a, (GlobalTheory.T.sandwich_datum_trace_eq p C v O hv ε hε Λ h D a).2, GlobalTheory.T.rep_trace_eq_mul_algebra_trace p Λ N h hh D.ρT a,
      map_mul, map_natCast]
  have hH : ∀ a, (ρH a).trace = (N : O) * padicToO p O (Algebra.trace ℤ_[p] Λ a) := by
    intro a
    rw [congrFun hρH a, (GlobalTheory.T.sandwich_datum_trace_eq p C v O hv ε hε Λ h D a).1,
      (GlobalTheory.T.sandwich_datum_trace_eq p C v O hv ε hε Λ h D a).2, GlobalTheory.T.rep_trace_eq_mul_algebra_trace p Λ N h hh D.ρT a,
      map_mul, map_natCast]
  rw [← hρT, ← hρH]
  exact ⟨⟨GlobalTheory.T.eigenspaces_of_ring_homs_independent C O Λ h ρT hv.hom_inj, GlobalTheory.T.dvr_rep_eigenspaces_span_top p C v O hv Λ h ρT,
      GlobalTheory.T.rep_trace_eq_mul_algebra_trace_dvr p C v O hv Λ N h ρT hT⟩,
    ⟨GlobalTheory.T.eigenspaces_of_ring_homs_independent C O Λ h ρH hv.hom_inj, GlobalTheory.T.dvr_rep_eigenspaces_span_top p C v O hv Λ h ρH,
      GlobalTheory.T.rep_trace_eq_mul_algebra_trace_dvr p C v O hv Λ N h ρH hH⟩⟩

end GlobalTheory
end
