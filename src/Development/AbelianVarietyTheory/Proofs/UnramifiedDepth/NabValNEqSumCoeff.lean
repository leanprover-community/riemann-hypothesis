import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonNCongr
import BuildAid.ForwardExisting

section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

section NabLin

variable {R : Type} [CommRing R] {d n : ℕ}

theorem dofN_add (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (f g : PS R n d) :
    DofN F b u (f + g) = DofN F b u f + DofN F b u g := by
  simp only [DofN, map_add, mul_add, Finset.sum_add_distrib]

theorem dofN_smul (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (t : R) (f : PS R n d) :
    DofN F b u (t • f) = t • DofN F b u f := by
  simp only [DofN, Derivation.map_smul, map_smul, mul_smul_comm, Finset.smul_sum]

theorem dofN_iterate_add (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (k : ℕ)
    (f g : PS R n d) :
    (DofN F b u)^[k] (f + g) = (DofN F b u)^[k] f + (DofN F b u)^[k] g := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, dofN_add]

theorem dofN_iterate_smul (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (k : ℕ)
    (t : R) (f : PS R n d) :
    (DofN F b u)^[k] (t • f) = t • (DofN F b u)^[k] f := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, dofN_smul]

variable {ι : Type} [Fintype ι]

theorem dmonN_add (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R) (m : ι →₀ ℕ)
    (f g : PS R n d) :
    DmonN F cp u m (f + g) = DmonN F cp u m f + DmonN F cp u m g := by
  unfold DmonN
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, ih, dofN_iterate_add]

theorem dmonN_smul (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R) (m : ι →₀ ℕ)
    (t : R) (f : PS R n d) :
    DmonN F cp u m (t • f) = t • DmonN F cp u m f := by
  unfold DmonN
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, ih, dofN_iterate_smul]

theorem dpolyN_eq_sum_of_subset (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (P : MvPolynomial ι R) (f : PS R n d) (s : Finset (ι →₀ ℕ)) (hs : P.support ⊆ s) :
    DpolyN F cp u P f = ∑ m ∈ s, MvPowerSeries.C (P.coeff m) * DmonN F cp u m f := by
  unfold DpolyN
  refine Finset.sum_subset hs fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.mp hm, map_zero, zero_mul]

theorem dpolyN_add_right (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (P : MvPolynomial ι R) (f g : PS R n d) :
    DpolyN F cp u P (f + g) = DpolyN F cp u P f + DpolyN F cp u P g := by
  simp only [DpolyN, dmonN_add, mul_add, Finset.sum_add_distrib]

theorem dpolyN_smul_right (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (P : MvPolynomial ι R) (t : R) (f : PS R n d) :
    DpolyN F cp u P (t • f) = t • DpolyN F cp u P f := by
  simp only [DpolyN, dmonN_smul, mul_smul_comm, Finset.smul_sum]

theorem dpolyN_add_left (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (P Q : MvPolynomial ι R) (f : PS R n d) :
    DpolyN F cp u (P + Q) f = DpolyN F cp u P f + DpolyN F cp u Q f := by
  classical
  rw [dpolyN_eq_sum_of_subset F cp u (P + Q) f (P.support ∪ Q.support) MvPolynomial.support_add,
    dpolyN_eq_sum_of_subset F cp u P f (P.support ∪ Q.support) Finset.subset_union_left,
    dpolyN_eq_sum_of_subset F cp u Q f (P.support ∪ Q.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, map_add, add_mul]

theorem dpolyN_C_mul_left (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (t : R) (P : MvPolynomial ι R) (f : PS R n d) :
    DpolyN F cp u (MvPolynomial.C t * P) f = MvPowerSeries.C t * DpolyN F cp u P f := by
  have hs : (MvPolynomial.C t * P).support ⊆ P.support := by
    intro m hm
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [MvPolynomial.coeff_C_mul, h0, mul_zero])
  rw [dpolyN_eq_sum_of_subset F cp u _ f P.support hs, DpolyN, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_C_mul, map_mul, mul_assoc]

end NabLin

theorem nabValN_bilinear : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), (∀ (f g : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m (f + g) cp u P = nabValN B K h w0 m f cp u P + nabValN B K h w0 m g cp u P) ∧ (∀ (t : K) (f : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m (t • f) cp u P = t * nabValN B K h w0 m f cp u P) ∧ (∀ (f : PS K n d) (P Q : MvPolynomial ι K), nabValN B K h w0 m f cp u (P + Q) = nabValN B K h w0 m f cp u P + nabValN B K h w0 m f cp u Q) ∧ (∀ (t : K) (f : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m f cp u (MvPolynomial.C t * P) = t * nabValN B K h w0 m f cp u P) := by
  intro K _ _ d O _ _ B h w0 m n ι _ cp u
  refine ⟨fun f g P => ?_, fun t f P => ?_, fun f P Q => ?_, fun t f P => ?_⟩
  · simp only [nabValN, add_mul, dpolyN_add_right, map_add]
  · simp only [nabValN]
    rw [smul_mul_assoc, dpolyN_smul_right, MvPowerSeries.smul_eq_C_mul, map_mul,
      MvPowerSeries.constantCoeff_C]
  · simp only [nabValN, dpolyN_add_left, map_add]
  · simp only [nabValN]
    rw [dpolyN_C_mul_left, map_mul, MvPowerSeries.constantCoeff_C]

end GlobalTheory
end

section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nablaValueCopies_bilinear : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), (∀ (f g : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m (f + g) cp u P = nabValN B K h w0 m f cp u P + nabValN B K h w0 m g cp u P) ∧ (∀ (t : K) (f : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m (t • f) cp u P = t * nabValN B K h w0 m f cp u P) ∧ (∀ (f : PS K n d) (P Q : MvPolynomial ι K), nabValN B K h w0 m f cp u (P + Q) = nabValN B K h w0 m f cp u P + nabValN B K h w0 m f cp u Q) ∧ (∀ (t : K) (f : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m f cp u (MvPolynomial.C t * P) = t * nabValN B K h w0 m f cp u P) := by
  first | exact @GlobalTheory.nabValN_bilinear | exact GlobalTheory.nabValN_bilinear | (intros; apply GlobalTheory.nabValN_bilinear <;> assumption)
end

section
section
set_option autoImplicit false

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory.PowGerm

theorem nabValN_eq_zero_of_coeff_eq_zero :
    ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), ∀ (f : PS K n d) (P : MvPolynomial ι K), (∀ μ : Fin n × Fin d →₀ ℕ, μ.degree ≤ P.totalDegree → MvPowerSeries.coeff μ f = 0) → nabValN B K h w0 m f cp u P = 0 := by
  intro K _ _ d O _ _ B h w0 m n ι _ cp u f P hf
  classical
  unfold nabValN
  rw [NabJet.constantCoeff_DpolyN_eq _ cp u P _ _ subset_rfl]
  refine Finset.sum_eq_zero fun a ha => ?_
  have hdeg : a.degree ≤ P.totalDegree := by
    have := MvPolynomial.le_totalDegree ha
    rwa [Finsupp.degree_apply]
  rw [NabJet.constantCoeff_DmonN_congr _ cp u a _ 0 fun mo hmo => ?_,
    (NabJet.isLinearMap_DmonN (B.FK K) cp u a).map_zero, map_zero, mul_zero]
  rw [NabJet.coeff_mul_congr P.totalDegree f 0 _ (fun b hb => by rw [hf b hb, map_zero]) mo (hmo.trans hdeg), zero_mul]

end GlobalTheory.PowGerm
end

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantValueCopies_eq_zero_of_low_coeff : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), ∀ (f : PS K n d) (P : MvPolynomial ι K), (∀ μ : Fin n × Fin d →₀ ℕ, μ.degree ≤ P.totalDegree → MvPowerSeries.coeff μ f = 0) → nabValN B K h w0 m f cp u P = 0 := by
  atlas_forward_decl GlobalTheory.PowGerm.nabValN_eq_zero_of_coeff_eq_zero
end

section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

theorem functional_eq_sum_coeff_of_vanish {σ K : Type} [CommRing K] [Finite σ]
    (F : MvPowerSeries σ K → K) (N : ℕ)
    (hadd : ∀ f g, F (f + g) = F f + F g) (hsmul : ∀ (t : K) f, F (t • f) = t * F f)
    (hvan : ∀ f, (∀ μ : σ →₀ ℕ, μ.degree ≤ N → MvPowerSeries.coeff μ f = 0) → F f = 0) :
    ∃ S : Finset (σ →₀ ℕ), ∀ f, F f =
      ∑ μ ∈ S, MvPowerSeries.coeff μ f * F (MvPowerSeries.monomial μ (1 : K)) := by
  classical
  let L : MvPowerSeries σ K →ₗ[K] K :=
    { toFun := F, map_add' := hadd, map_smul' := fun t f => by simpa using hsmul t f }
  have hL : ∀ f, L f = F f := fun _ => rfl
  refine ⟨(Finsupp.finite_of_degree_le (σ := σ) N).toFinset, fun f => ?_⟩
  set S := (Finsupp.finite_of_degree_le (σ := σ) N).toFinset with hS
  have hg : F (f - ∑ μ ∈ S, MvPowerSeries.coeff μ f • MvPowerSeries.monomial μ (1 : K)) = 0 := by
    apply hvan
    intro ν hν
    have hνS : ν ∈ S := by simpa [hS] using hν
    rw [map_sub, map_sum, Finset.sum_eq_single_of_mem ν hνS]
    · simp
    · intro μ _ hne
      rw [map_smul, MvPowerSeries.coeff_monomial_ne (Ne.symm hne)]
      simp
  rw [← hL, map_sub, map_sum, sub_eq_zero] at hg
  rw [← hL, hg]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_smul, hL, smul_eq_mul]

theorem nabValN_eq_sum_coeff : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), ∀ (P : MvPolynomial ι K), ∃ S : Finset (Fin n × Fin d →₀ ℕ), ∀ f : PS K n d, nabValN B K h w0 m f cp u P = ∑ μ ∈ S, MvPowerSeries.coeff μ f * nabValN B K h w0 m (MvPowerSeries.monomial μ (1 : K)) cp u P := by
  intro K _ _ d O _ _ B h w0 m n ι _ cp u P
  obtain ⟨h1, h2, -, -⟩ := GlobalTheory.T.nablaValueCopies_bilinear K d O B h w0 m n ι cp u
  exact functional_eq_sum_coeff_of_vanish (fun f => nabValN B K h w0 m f cp u P) P.totalDegree
    (fun f g => h1 f g P) (fun t f => h2 t f P)
    (fun f hf => GlobalTheory.T.invariantValueCopies_eq_zero_of_low_coeff K d O B h w0 m n ι cp u f P hf)

end GlobalTheory
end
