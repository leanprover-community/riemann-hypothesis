import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumScalarActionStatement
import ReciprocityTheory.DualLattices.CotangentSurjective
import ReciprocityTheory.DualLattices.CyclicRecursionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuCoeffZeroNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepBasisCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqQuotientCharpolyPow
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TensorProductAction

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem frame_of_spanning : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N d h : ℕ) (b : Module.Basis (Fin d) ℤ_[p] Λ) (ρ : Λ →+* Matrix (Fin h) (Fin h) (Ainf p O)) (x : Fin N → Fin h → Ainf p O), (∀ c : ℤ_[p], ρ (algebraMap ℤ_[p] Λ c) = ofPadic p O c • (1 : Matrix (Fin h) (Fin h) (Ainf p O))) → h = N * d → Submodule.span (Ainf p O) (Set.range fun ij : Fin N × Fin d => ρ (b ij.2) *ᵥ x ij.1) = ⊤ → ∃ e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O), IsFrame ρ e ∧ ∀ (i : Fin N) (l : Λ), e (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l)) = ρ l *ᵥ x i := by
  intro p _ O _ _ _ Λ _ _ N d h b ρ x hsc hh hspan
  subst hh
  classical
  let bR : Module.Basis (Fin d) (Ainf p O) (RL p O Λ) := Algebra.TensorProduct.basis (Ainf p O) b
  let bP := Pi.basis (fun _ : Fin N => bR)
  let L : (Fin N → RL p O Λ) →ₗ[Ainf p O] (Fin (N * d) → Ainf p O) :=
    bP.constr (Ainf p O) (fun ij => ρ (b ij.2) *ᵥ x ij.1)
  have hL : ∀ i j, L (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j)) = ρ (b j) *ᵥ x i := by
    intro i j
    have hb : Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j) = bP ⟨i, j⟩ := by
      simp [bP, bR, Pi.basis_apply, Algebra.TensorProduct.basis_apply]
    rw [hb]
    exact bP.constr_basis (Ainf p O) (fun ij : (Σ _ : Fin N, Fin d) => ρ (b ij.2) *ᵥ x ij.1) ⟨i, j⟩
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact ⟨_, hL i j⟩
  let σ : (Σ _ : Fin N, Fin d) ≃ Fin (N * d) := (Equiv.sigmaEquivProd _ _).trans finProdFinEquiv
  let E := (bP.reindex σ).equivFun
  have hinj : Function.Injective L := by
    have hf : Function.Surjective (L ∘ₗ E.symm.toLinearMap) := by
      intro y; obtain ⟨w, rfl⟩ := hsurj y; exact ⟨E w, by simp⟩
    have hi := OrzechProperty.injective_of_surjective_endomorphism _ hf
    intro u v huv
    have : E u = E v := hi (by simpa using huv)
    exact E.injective this
  let e := LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
  have he : ∀ w, e w = L w := fun w => rfl
  have hform : ∀ (i : Fin N) (l : Λ), e (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l)) = ρ l *ᵥ x i := by
    intro i l
    rw [he]
    have hps : ∀ (f : Fin d → RL p O Λ), Pi.single i (∑ j, f j) = ∑ j, Pi.single (M := fun _ : Fin N => RL p O Λ) i (f j) :=
      fun f => map_sum (AddMonoidHom.single (fun _ : Fin N => RL p O Λ) i) f _
    rw [← b.sum_repr l, TensorProduct.tmul_sum, hps, map_sum, map_sum, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun j _ => ?_
    set c := (b.repr l) j
    have h1 : c • ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j) = ofPadic p O c • ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j) :=
      (algebraMap_smul (Ainf p O) c _).symm
    have h2 : Pi.single i (ofPadic p O c • ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j))
        = ofPadic p O c • Pi.single (M := fun _ : Fin N => RL p O Λ) i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j) := by
      funext k; by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    rw [TensorProduct.tmul_smul, h1, h2, map_smul, hL, Algebra.smul_def c (b j), map_mul, hsc,
      smul_mul_assoc, one_mul, Matrix.smul_mulVec]
  refine ⟨e, ?_, hform⟩
  intro l w
  let f1 : (Fin N → RL p O Λ) →ₗ[Ainf p O] (Fin (N * d) → Ainf p O) :=
    e.toLinearMap ∘ₗ DistribMulAction.toLinearMap (Ainf p O) (Fin N → RL p O Λ)
      ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l)
  let f2 : (Fin N → RL p O Λ) →ₗ[Ainf p O] (Fin (N * d) → Ainf p O) :=
    (Matrix.mulVecLin (ρ l)) ∘ₗ e.toLinearMap
  have hf : f1 = f2 := by
    refine bP.ext fun ij => ?_
    obtain ⟨i, j⟩ := ij
    have hb : bP ⟨i, j⟩ = Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j) := by
      simp [bP, bR, Pi.basis_apply, Algebra.TensorProduct.basis_apply]
    have hs : ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) • Pi.single (M := fun _ : Fin N => RL p O Λ) i
        ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j) = Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] (l * b j)) := by
      funext k; by_cases hk : k = i
      · subst hk; simp [Algebra.TensorProduct.tmul_mul_tmul]
      · simp [hk]
    show e (((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) • bP ⟨i, j⟩) = ρ l *ᵥ e (bP ⟨i, j⟩)
    simp only [ hb, hs,
      LinearEquiv.coe_coe, hform, Matrix.mulVecLin_apply, map_mul, Matrix.mulVec_mulVec]
  exact LinearMap.congr_fun hf w

end GlobalTheory.DetInv
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_frame_span_generation : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N d h : ℕ) (b : Module.Basis (Fin d) ℤ_[p] Λ) (ρ : Λ →+* Matrix (Fin h) (Fin h) (Ainf p O)) (x : Fin N → Fin h → Ainf p O), (∀ c : ℤ_[p], ρ (algebraMap ℤ_[p] Λ c) = ofPadic p O c • (1 : Matrix (Fin h) (Fin h) (Ainf p O))) → h = N * d → Submodule.span (Ainf p O) (Set.range fun ij : Fin N × Fin d => ρ (b ij.2) *ᵥ x ij.1) = ⊤ → ∃ e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O), IsFrame ρ e ∧ ∀ (i : Fin N) (l : Λ), e (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l)) = ρ l *ᵥ x i := by
  atlas_forward_decl GlobalTheory.DetInv.frame_of_spanning
end

section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rep_basis_charpoly : ∀ (p : ℕ) [Fact p.Prime] (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Free ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] (h d : ℕ) (b : Module.Basis (Fin d) ℤ_[p] Λ) (ρ : Λ →ₐ[ℤ_[p]] Matrix (Fin h) (Fin h) ℤ_[p]), ∃ (N : ℕ) (y : Fin N → Fin h → ℤ_[p]), h = N * d ∧ Submodule.span ℤ_[p] (Set.range fun ij : Fin N × Fin d => ρ (b ij.2) *ᵥ y ij.1) = ⊤ ∧ ∀ a : Λ, (ρ a).charpoly = (LinearMap.mulLeft ℤ_[p] a).charpoly ^ N := by
  first | exact @GlobalTheory.DetInv.rep_free_charpoly | exact GlobalTheory.DetInv.rep_free_charpoly | (intros; apply GlobalTheory.DetInv.rep_free_charpoly <;> assumption)
end

section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem charpoly_eq_of_intertwined :
    ∀ (A : Type) [CommRing A] [IsDomain A] (h : ℕ) (μ : A) (F G X Y : Matrix (Fin h) (Fin h) A),
      μ ≠ 0 → G * F = μ • (1 : Matrix (Fin h) (Fin h) A) → F * X = Y * F →
        Y.charpoly = X.charpoly := by
  intro A _ _ h μ F G X Y hμ hGF hFX
  have hdet : F.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hGF
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ hμ h1.symm
  have hmap : (F.map Polynomial.C) * (X.map Polynomial.C)
      = (Y.map Polynomial.C) * (F.map Polynomial.C) := by
    have := congrArg (fun M => Polynomial.C.mapMatrix M) hFX
    simpa [map_mul] using this
  have hcomm : (F.map Polynomial.C) * Matrix.scalar (Fin h) (Polynomial.X : Polynomial A)
      = Matrix.scalar (Fin h) (Polynomial.X : Polynomial A) * (F.map Polynomial.C) :=
    ((Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq).symm
  have key : (F.map Polynomial.C) * charmatrix X = charmatrix Y * (F.map Polynomial.C) := by
    simp only [charmatrix, RingHom.mapMatrix_apply, mul_sub, sub_mul]
    rw [hmap, hcomm]
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm] at hd
  have hC : (F.map Polynomial.C).det ≠ 0 := by
    have : (F.map Polynomial.C).det = Polynomial.C F.det := by
      simpa using (RingHom.map_det (Polynomial.C : A →+* Polynomial A) F).symm
    rw [this]
    exact Polynomial.C_ne_zero.mpr hdet
  have := mul_right_cancel₀ hC hd
  simpa [Matrix.charpoly] using this.symm

end GlobalTheory.DetInv
end

section
section
open scoped TensorProduct nonZeroDivisors
open Polynomial

namespace GlobalTheory.UnramifiedGenerator

open IsLocalRing

theorem charpoly_map_residue {R O : Type} [CommRing R] [IsLocalRing R] [CommRing O] [IsDomain O]
    [IsLocalRing O] [Algebra R O] [Module.Free R O] [Module.Finite R O]
    [IsLocalHom (algebraMap R O)] (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (π : O) (hπ0 : π ≠ 0) (hπ : maximalIdeal O = Ideal.span {π}) (e : ℕ) (he : 0 < e) (u : Oˣ)
    (hu : algebraMap R O ϖ = π ^ e * u) (a : O) :
    (LinearMap.charpoly (LinearMap.mulLeft R a)).map (residue R) =
      (LinearMap.charpoly (LinearMap.mulLeft (ResidueField R) (residue O a))) ^ e := by
  set k := ResidueField R
  have hsurj : ∀ x : k ⊗[R] O, ∃ y : O, (1 : k) ⊗ₜ[R] y = x := fun x =>
    TensorProduct.mk_surjective R O k residue_surjective x
  have hker : ∀ y : O, (1 : k) ⊗ₜ[R] y = 0 ↔ ∃ z, y = algebraMap R O ϖ * z := by
    intro y
    have h1 : (1 : k) ⊗ₜ[R] y = 0 ↔
        y ∈ LinearMap.ker (TensorProduct.mk R (R ⧸ maximalIdeal R) O 1) := Iff.rfl
    rw [h1, LinearMap.ker_tensorProductMk, hϖ, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    simp only [Submodule.mem_top, true_and, Algebra.smul_def]
    exact ⟨fun ⟨z, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => ⟨z, hz.symm⟩⟩
  let t : Module.End k (k ⊗[R] O) := (LinearMap.mulLeft R π).baseChange k
  let T : Module.End k (k ⊗[R] O) := (LinearMap.mulLeft R a).baseChange k
  have ht : ∀ y, t (1 ⊗ₜ y) = 1 ⊗ₜ (π * y) := fun y => by simp [t]
  have hT : ∀ y, T (1 ⊗ₜ y) = 1 ⊗ₜ (a * y) := fun y => by simp [T]
  have htp : ∀ (n : ℕ) y, (t ^ n) (1 ⊗ₜ y) = 1 ⊗ₜ (π ^ n * y) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => intro y; rw [pow_succ', Module.End.mul_apply, ih, ht, pow_succ', mul_assoc]
  have hc : Commute t T := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := hsurj x
    simp only [Module.End.mul_apply, ht, hT, mul_left_comm]
  have hte : t ^ e = 0 := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := hsurj x
    rw [htp, LinearMap.zero_apply, hker]
    exact ⟨(u⁻¹ : Oˣ) * y, by rw [hu, mul_assoc, Units.mul_inv_cancel_left]⟩
  have hkt : ∀ x, t x = 0 → x ∈ LinearMap.range (t ^ (e - 1)) := by
    intro x hx
    obtain ⟨y, rfl⟩ := hsurj x
    rw [ht, hker] at hx
    obtain ⟨z, hz⟩ := hx
    obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by omega⟩
    refine ⟨1 ⊗ₜ (u * z), ?_⟩
    rw [htp, Nat.add_sub_cancel]
    congr 1
    apply mul_left_cancel₀ hπ0
    rw [hz, hu]
    ring
  have hTt : LinearMap.range t ≤ (LinearMap.range t).comap T := by
    rintro _ ⟨x, rfl⟩
    exact ⟨T x, LinearMap.congr_fun hc.eq x⟩
  have key := GlobalTheory.NilpFiltration.charpoly_eq_charpoly_mapQ_pow k (k ⊗[R] O) t T hc e he hte hkt hTt
  have hbc : LinearMap.charpoly T = (LinearMap.charpoly (LinearMap.mulLeft R a)).map (residue R) :=
    LinearMap.charpoly_baseChange _ k
  rw [← hbc, key]
  congr 1
  let φ : k ⊗[R] O →ₗ[k] ResidueField O :=
    (Algebra.TensorProduct.lift (Algebra.ofId k (ResidueField O))
      (IsScalarTower.toAlgHom R O (ResidueField O)) (fun _ _ => Commute.all _ _)).toLinearMap
  have hφ : ∀ y, φ (1 ⊗ₜ y) = residue O y := fun y => by simp [φ]
  have hφs : Function.Surjective φ := fun w => by
    obtain ⟨y, rfl⟩ := residue_surjective w
    exact ⟨_, hφ y⟩
  have hφk : LinearMap.range t = LinearMap.ker φ := by
    ext x
    obtain ⟨y, rfl⟩ := hsurj x
    constructor
    · rintro ⟨x', hx'⟩
      obtain ⟨z, rfl⟩ := hsurj x'
      rw [← hx', ht, LinearMap.mem_ker, hφ, residue_eq_zero_iff, hπ]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · intro hy
      rw [LinearMap.mem_ker, hφ, residue_eq_zero_iff, hπ, Ideal.mem_span_singleton] at hy
      obtain ⟨z, rfl⟩ := hy
      exact ⟨_, ht z⟩
  refine GlobalTheory.NilpFiltration.charpoly_eq_of_intertwine
    ((Submodule.quotEquivOfEq _ _ hφk).trans (φ.quotKerEquivOfSurjective hφs)) _ _ ?_
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := hsurj x
  change φ (T (1 ⊗ₜ y)) = residue O a * φ (1 ⊗ₜ y)
  rw [hT, hφ, hφ, map_mul]

theorem exists_ramification_and_generator : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O],
    ∃ (e : ℕ) (π a : O) (u : Oˣ) (h : ℤ_[l][X]), 0 < e ∧ (l : O) = π ^ e * u ∧ h.Monic ∧
      aeval a h ∈ Ideal.span {π} ∧ e * h.natDegree = Module.finrank ℤ_[l] O ∧
      ∀ (κ : Type) [Field κ] [CharP κ l] (ψ : ℤ_[l] →+* κ), (h.map ψ).Separable ∧
        (LinearMap.charpoly (LinearMap.mulLeft ℤ_[l] a)).map ψ = (h.map ψ) ^ e := by
  intro l hl O _ _ _ _ _ _
  set k := ResidueField ℤ_[l]
  haveI : Finite k := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have hlm : (l : ℤ_[l]) ∈ maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
  have hl1 : algebraMap ℤ_[l] O l ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ_[l] O)).2 hl0
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl1 hπ
  have he : 0 < e := by
    refine Nat.pos_of_ne_zero ?_
    rintro rfl
    have h1 : IsUnit (algebraMap ℤ_[l] O l) := by rw [hu]; simp
    exact hlm (isUnit_of_map_unit _ _ h1)
  rw [mul_comm] at hu
  let pb : PowerBasis k (ResidueField O) := Field.powerBasisOfFiniteOfSeparable k (ResidueField O)
  obtain ⟨a, ha⟩ := residue_surjective pb.gen
  have hm : (minpoly k pb.gen).Monic := minpoly.monic pb.isIntegral_gen
  obtain ⟨h, hh, -, hhm⟩ := lifts_and_natDegree_eq_and_monic (f := residue ℤ_[l])
    ((mem_lifts _).2 (map_surjective _ residue_surjective _)) hm
  have hsep : (h.map (residue ℤ_[l])).Separable := by
    rw [hh]; exact Algebra.IsSeparable.isSeparable k pb.gen
  have hch : (LinearMap.charpoly (LinearMap.mulLeft ℤ_[l] a)).map (residue ℤ_[l]) =
      (h.map (residue ℤ_[l])) ^ e := by
    rw [charpoly_map_residue (l : ℤ_[l]) PadicInt.maximalIdeal_eq_span_p π hπ.ne_zero
      hπ.maximalIdeal_eq e he u hu a, hh, ha, ← charpoly_leftMulMatrix pb,
      ← LinearMap.charpoly_toMatrix _ pb.basis]
    rfl
  refine ⟨e, π, a, u, h, he, by simpa using hu, hhm, ?_, ?_, ?_⟩
  · rw [← hπ.maximalIdeal_eq, ← residue_eq_zero_iff]
    have h1 := minpoly.aeval k pb.gen
    rw [← hh, ← ha] at h1
    rw [← h1]
    exact ((aeval_algebraMap_apply (ResidueField O) a h).symm).trans
      (aeval_map_algebraMap k _ h).symm
  · have h1 := congrArg natDegree hch
    rw [(LinearMap.charpoly_monic _).natDegree_map, LinearMap.charpoly_natDegree,
      natDegree_pow, hhm.natDegree_map] at h1
    exact h1.symm
  · intro κ _ _ ψ
    have hψ : ∀ x ∈ maximalIdeal ℤ_[l], ψ x = 0 := by
      intro x hx
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hx
      obtain ⟨y, rfl⟩ := hx
      simp
    let χ : k →+* κ := Ideal.Quotient.lift _ ψ hψ
    have hχ : ψ = χ.comp (residue ℤ_[l]) := RingHom.ext fun _ => rfl
    rw [hχ, ← Polynomial.map_map, ← Polynomial.map_map, hch, Polynomial.map_pow]
    exact ⟨hsep.map, rfl⟩

end GlobalTheory.UnramifiedGenerator
end

open scoped TensorProduct nonZeroDivisors
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformizer_separable_reduction : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O],
    ∃ (e : ℕ) (π a : O) (u : Oˣ) (h : ℤ_[l][X]), 0 < e ∧ (l : O) = π ^ e * u ∧ h.Monic ∧
      aeval a h ∈ Ideal.span {π} ∧ e * h.natDegree = Module.finrank ℤ_[l] O ∧
      ∀ (κ : Type) [Field κ] [CharP κ l] (ψ : ℤ_[l] →+* κ), (h.map ψ).Separable ∧
        (LinearMap.charpoly (LinearMap.mulLeft ℤ_[l] a)).map ψ = (h.map ψ) ^ e := by
  atlas_forward_decl GlobalTheory.UnramifiedGenerator.exists_ramification_and_generator
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

theorem reduction_ker_uniformiser_eq_range_pow : ∀ (p : ℕ) (W k Λ : Type) [CommRing W] [IsDomain W] [Field k] [CommRing Λ] (h e : ℕ) (c : W →+* k) (ρ : Λ →+* Matrix (Fin h) (Fin h) W) (π : Λ) (u : Λˣ), (p : W) ≠ 0 → Function.Surjective c → (∀ w, c w = 0 → (p : W) ∣ w) → c p = 0 → 0 < e → (p : Λ) = π ^ e * u → ((ρ π).map c) ^ e = 0 ∧ ∀ x : Fin h → k, (ρ π).map c *ᵥ x = 0 → ∃ y, x = ((ρ π).map c) ^ (e - 1) *ᵥ y := by
  intro p W k Λ _ _ _ _ h e c ρ π u hp hc hker hcp he hpu
  have hmap : ∀ M : Matrix (Fin h) (Fin h) W, M.map c = c.mapMatrix M := fun M => rfl
  have key : ρ π * ρ (π ^ (e - 1) * ↑u) = (p : Matrix (Fin h) (Fin h) W) := by
    rw [← map_mul, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel he, ← hpu, map_natCast]
  have key' : ρ (π ^ (e - 1) * ↑u) * ρ π = (p : Matrix (Fin h) (Fin h) W) := by
    rw [← map_mul, mul_comm, map_mul, key]
  have hpv : ∀ v : Fin h → W, (p : Matrix (Fin h) (Fin h) W) *ᵥ v = (p : W) • v := by
    intro v
    exact Matrix.natCast_mulVec p v
  have hpk : (p : k) = 0 := by rw [← map_natCast c]; exact hcp
  refine ⟨?_, ?_⟩
  · have hpe : π ^ e = (p : Λ) * ↑u⁻¹ := by
      rw [hpu, mul_assoc, Units.mul_inv, mul_one]
    rw [hmap, ← map_pow, ← map_pow, hpe, map_mul, map_mul, map_natCast, map_natCast,
      ← map_natCast (algebraMap k (Matrix (Fin h) (Fin h) k)) p, hpk, map_zero, zero_mul]
  · intro x hx
    choose xt hxt using fun i => hc (x i)
    have hcx : c ∘ xt = x := funext hxt
    have hdiv : ∀ i, (p : W) ∣ (ρ π *ᵥ xt) i := by
      intro i; apply hker
      rw [RingHom.map_mulVec, hcx, hx]; rfl
    choose z hz using hdiv
    have hinj : ∀ v : Fin h → W, ρ π *ᵥ v = 0 → v = 0 := by
      intro v hv
      have h1 : (p : W) • v = 0 := by
        rw [← hpv, ← key', ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
      exact (smul_eq_zero.mp h1).resolve_left hp
    have hxtz : ρ π *ᵥ xt = (p : W) • z := funext fun i => by rw [hz i]; rfl
    have hxB : xt = (ρ π ^ (e - 1)) *ᵥ (ρ ↑u *ᵥ z) := by
      rw [Matrix.mulVec_mulVec, ← map_pow, ← map_mul]
      apply sub_eq_zero.mp
      apply hinj
      rw [Matrix.mulVec_sub, hxtz, Matrix.mulVec_mulVec, key, hpv, sub_self]
    refine ⟨c ∘ (ρ ↑u *ᵥ z), ?_⟩
    funext i
    rw [hmap, ← map_pow, ← hxt i, hxB, RingHom.map_mulVec]
    rfl

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_uniformizer_nilpotent : ∀ (p : ℕ) (W k Λ : Type) [CommRing W] [IsDomain W] [Field k] [CommRing Λ] (h e : ℕ) (c : W →+* k) (ρ : Λ →+* Matrix (Fin h) (Fin h) W) (π : Λ) (u : Λˣ), (p : W) ≠ 0 → Function.Surjective c → (∀ w, c w = 0 → (p : W) ∣ w) → c p = 0 → 0 < e → (p : Λ) = π ^ e * u → ((ρ π).map c) ^ e = 0 ∧ ∀ x : Fin h → k, (ρ π).map c *ᵥ x = 0 → ∃ y, x = ((ρ π).map c) ^ (e - 1) *ᵥ y := by
  atlas_forward_decl GlobalTheory.reduction_ker_uniformiser_eq_range_pow
end

section
open scoped TensorProduct nonZeroDivisors
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_eq_quotient_charpoly_pow : ∀ (K : Type) [Field K] (X : Type) [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    (t T : Module.End K X) (_ : Commute t T) (e : ℕ) (_ : 0 < e) (_ : t ^ e = 0)
    (_ : ∀ x, t x = 0 → x ∈ LinearMap.range (t ^ (e - 1)))
    (hT : LinearMap.range t ≤ (LinearMap.range t).comap T),
    LinearMap.charpoly T = (LinearMap.charpoly ((LinearMap.range t).mapQ (LinearMap.range t) T hT)) ^ e := by
  first | exact @GlobalTheory.NilpFiltration.charpoly_eq_charpoly_mapQ_pow | exact GlobalTheory.NilpFiltration.charpoly_eq_charpoly_mapQ_pow | (intros; apply GlobalTheory.NilpFiltration.charpoly_eq_charpoly_mapQ_pow <;> assumption)
end

section
section
open scoped TensorProduct nonZeroDivisors
open Polynomial

namespace GlobalTheory

theorem semisimple_charpoly_pow_generators (κ : Type) [Field κ] [IsAlgClosed κ] (G : Type)
    [AddCommGroup G] [Module κ G] [FiniteDimensional κ G] (T : Module.End κ G) (h : κ[X])
    (hm : h.Monic) (hs : h.Separable) (h0 : aeval T h = 0) (N : ℕ)
    (hc : LinearMap.charpoly T = h ^ N) :
    ∃ x : Fin N → G, ∀ v : G, ∃ p : Fin N → κ[X], v = ∑ j, aeval T (p j) (x j) := by
  classical
  have hne : h ≠ 0 := hm.ne_zero
  have hsemi : T.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs.squarefree h0
  have hgen : ∀ μ, T.maxGenEigenspace μ = T.eigenspace μ :=
    fun μ => hsemi.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ

  have hev : ∀ (q : κ[X]) (ν : κ) (v : G), v ∈ T.eigenspace ν → aeval T q v = eval ν q • v := by
    intro q ν v hv
    by_cases hv0 : v = 0
    · simp [hv0]
    · exact Module.End.aeval_apply_of_hasEigenvector (Module.End.hasEigenvector_iff.2 ⟨hv, hv0⟩)
  set R : Finset κ := h.roots.toFinset with hR
  have hmemR : ∀ μ, μ ∈ R ↔ h.IsRoot μ := fun μ => by
    rw [hR, Multiset.mem_toFinset, mem_roots hne]

  have hfr : ∀ μ ∈ R, Module.finrank κ (T.eigenspace μ) = N := by
    intro μ hμ
    have hμ' : μ ∈ h.roots := Multiset.mem_toFinset.1 hμ
    rw [← hgen, LinearMap.finrank_maxGenEigenspace_eq, hc, ← count_roots, roots_pow,
      Multiset.count_nsmul, Multiset.count_eq_one_of_mem (nodup_roots hs) hμ', mul_one]

  have hout : ∀ μ, μ ∉ R → ∀ v ∈ T.eigenspace μ, v = 0 := by
    intro μ hμ v hv
    by_contra hv0
    apply hμ
    rw [hmemR]
    have h1 := hev h μ v hv
    rw [h0] at h1
    have h2 : eval μ h • v = 0 := by simpa using h1.symm
    exact (smul_eq_zero.1 h2).resolve_right hv0
  have hbasis : ∀ μ ∈ R, ∃ b : Fin N → G, (∀ j, b j ∈ T.eigenspace μ) ∧
      ∀ v ∈ T.eigenspace μ, ∃ c : Fin N → κ, v = ∑ j, c j • b j := by
    intro μ hμ
    let B := Module.finBasisOfFinrankEq κ (T.eigenspace μ) (hfr μ hμ)
    refine ⟨fun j => (B j : G), fun j => (B j).2, fun v hv => ⟨B.repr ⟨v, hv⟩, ?_⟩⟩
    have h2 := congrArg Subtype.val (B.sum_repr ⟨v, hv⟩)
    push_cast at h2
    exact h2.symm
  choose! b hbmem hbspan using hbasis
  refine ⟨fun j => ∑ μ ∈ R, b μ j, fun v => ?_⟩
  have hinj : Set.InjOn (id : κ → κ) R := Function.injective_id.injOn

  have hpick : ∀ μ ∈ R, ∀ j, aeval T (Lagrange.basis R id μ) (∑ ν ∈ R, b ν j) = b μ j := by
    intro μ hμ j
    rw [map_sum, Finset.sum_eq_single μ]
    · rw [hev _ μ _ (hbmem μ hμ j)]
      have := Lagrange.eval_basis_self hinj hμ
      simp only [id] at this
      rw [this, one_smul]
    · intro ν hν hne'
      rw [hev _ ν _ (hbmem ν hν j)]
      have := Lagrange.eval_basis_of_ne (v := id) hne'.symm hν
      simp only [id] at this
      rw [this, zero_smul]
    · intro h'
      exact absurd hμ h'
  have htop : v ∈ ⨆ μ, T.eigenspace μ := by
    have : (⨆ μ, T.eigenspace μ) = ⊤ := by
      rw [← Module.End.iSup_maxGenEigenspace_eq_top T]
      exact iSup_congr fun μ => (hgen μ).symm
    rw [this]
    exact Submodule.mem_top
  induction htop using Submodule.iSup_induction' with
  | mem μ w hw =>
    by_cases hμ : μ ∈ R
    · obtain ⟨c, rfl⟩ := hbspan μ hμ w hw
      refine ⟨fun j => C (c j) * Lagrange.basis R id μ, ?_⟩
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, aeval_C, Module.End.mul_apply, hpick μ hμ j]
      simp [Module.algebraMap_end_apply]
    · rw [hout μ hμ w hw]
      exact ⟨0, by simp⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨p, rfl⟩ := hy
    obtain ⟨q, rfl⟩ := hz
    refine ⟨p + q, ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [map_add, Finset.sum_add_distrib]

end GlobalTheory
end

open scoped TensorProduct nonZeroDivisors
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclic_generators_separable_min : ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (G : Type) [AddCommGroup G] [Module κ G]
    [FiniteDimensional κ G] (T : Module.End κ G) (h : κ[X]) (_ : h.Monic) (_ : h.Separable)
    (_ : aeval T h = 0) (N : ℕ) (_ : LinearMap.charpoly T = h ^ N),
    ∃ x : Fin N → G, ∀ v : G, ∃ p : Fin N → κ[X], v = ∑ j, aeval T (p j) (x j) := by
  atlas_forward_decl GlobalTheory.semisimple_charpoly_pow_generators
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

open Polynomial in

theorem GlobalTheory.DetInv.exists_generators_of_charpoly_eq_pow : ∀ (k : Type) [Field k] [IsAlgClosed k] (n e N : ℕ) (t T : Matrix (Fin n) (Fin n) k) (h : Polynomial k), 0 < e → h.Monic → h.Separable → t * T = T * t → t ^ e = 0 → (∀ x, t *ᵥ x = 0 → ∃ y, x = t ^ (e - 1) *ᵥ y) → (∀ x, ∃ y, Polynomial.aeval T h *ᵥ x = t *ᵥ y) → T.charpoly = h ^ (e * N) → ∃ x : Fin N → Fin n → k, ∀ U : Submodule k (Fin n → k), (∀ i, x i ∈ U) → (∀ z ∈ U, t *ᵥ z ∈ U) → (∀ z ∈ U, T *ᵥ z ∈ U) → U = ⊤ := by
  intro k _ _ n e N t T h he hmon hsep htT hte hker himg hchar
  obtain ⟨t', ht'⟩ : ∃ t' : Module.End k (Fin n → k), t' = Matrix.toLin' t := ⟨_, rfl⟩
  obtain ⟨T', hT'⟩ : ∃ T' : Module.End k (Fin n → k), T' = Matrix.toLin' T := ⟨_, rfl⟩
  have htz : ∀ z, t' z = t *ᵥ z := fun z => by rw [ht', Matrix.toLin'_apply]
  have hTz : ∀ z, T' z = T *ᵥ z := fun z => by rw [hT', Matrix.toLin'_apply]
  have hcz : ∀ z, t' (T' z) = T' (t' z) := fun z => by
    simp only [htz, hTz, Matrix.mulVec_mulVec, htT]
  have hcomm : Commute t' T' := LinearMap.ext fun z => hcz z
  have hpow : ∀ (m : ℕ) z, (t' ^ m) z = t ^ m *ᵥ z := by
    intro m
    induction m with
    | zero => intro z; simp
    | succ m ih =>
      intro z
      rw [pow_succ, pow_succ, Module.End.mul_apply, ih, htz, Matrix.mulVec_mulVec]
  have hte' : t' ^ e = 0 := LinearMap.ext fun z => by rw [hpow, hte]; simp
  have hker' : ∀ x, t' x = 0 → x ∈ LinearMap.range (t' ^ (e - 1)) := by
    intro x hx
    obtain ⟨y, hy⟩ := hker x (by rw [← htz]; exact hx)
    exact ⟨y, by rw [hpow, hy]⟩
  have hTW : LinearMap.range t' ≤ (LinearMap.range t').comap T' := by
    rintro _ ⟨y, rfl⟩
    exact ⟨T' y, hcz y⟩
  have hc := GlobalTheory.T.charpoly_eq_quotient_charpoly_pow k (Fin n → k) t' T' hcomm e he hte' hker' hTW
  obtain ⟨Tb, hTb⟩ : ∃ Tb : Module.End k ((Fin n → k) ⧸ LinearMap.range t'),
      Tb = (LinearMap.range t').mapQ (LinearMap.range t') T' hTW := ⟨_, rfl⟩
  rw [← hTb] at hc
  have hcT : LinearMap.charpoly T' = T.charpoly := by rw [hT', Matrix.charpoly_toLin']
  have hroot : (LinearMap.charpoly Tb) ^ e = (h ^ N) ^ e := by
    rw [← hc, hcT, hchar, mul_comm, pow_mul]
  have hchb : LinearMap.charpoly Tb = h ^ N :=
    Polynomial.eq_of_monic_of_associated (LinearMap.charpoly_monic Tb) (hmon.pow N)
      (associated_of_dvd_dvd
        ((IsIntegrallyClosed.pow_dvd_pow_iff he.ne').mp hroot.dvd)
        ((IsIntegrallyClosed.pow_dvd_pow_iff he.ne').mp hroot.symm.dvd))
  have hb1 : ∀ x, Tb ((LinearMap.range t').mkQ x) = (LinearMap.range t').mkQ (T' x) := by
    intro x
    rw [hTb]
    rfl
  have hbm : ∀ (m : ℕ) x, (Tb ^ m) ((LinearMap.range t').mkQ x)
      = (LinearMap.range t').mkQ ((T' ^ m) x) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, hb1, ih]
  have hmk : ∀ (p : k[X]) x, aeval Tb p ((LinearMap.range t').mkQ x)
      = (LinearMap.range t').mkQ (aeval T' p x) := by
    intro p x
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
    | monomial m c =>
      rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
        Module.algebraMap_end_apply, Module.algebraMap_end_apply, hbm, map_smul]
  have hA : ∀ x, aeval T' h x = aeval T h *ᵥ x := by
    intro x
    have h1 : T' = Matrix.toLinAlgEquiv' T := hT'
    rw [h1, Polynomial.aeval_algHom_apply]
    exact Matrix.toLin'_apply _ _
  have hTbh : aeval Tb h = 0 := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := (LinearMap.range t').mkQ_surjective v
    rw [hmk, LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hA]
    obtain ⟨y, hy⟩ := himg x
    exact ⟨y, by rw [htz, hy]⟩
  obtain ⟨xb, hgen⟩ := GlobalTheory.T.exists_cyclic_generators_separable_min k _ Tb h hmon hsep hTbh N hchb
  choose xs hxs using fun j => (LinearMap.range t').mkQ_surjective (xb j)
  refine ⟨xs, fun U hU htU hTU => ?_⟩
  have hstab : ∀ f : Module.End k (Fin n → k), (∀ z ∈ U, f z ∈ U) →
      ∀ (m : ℕ), ∀ z ∈ U, (f ^ m) z ∈ U := by
    intro f hf m
    induction m with
    | zero => intro z hz; simpa using hz
    | succ m ih =>
      intro z hz
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (hf z hz)
  have htm := hstab t' fun z hz => by rw [htz]; exact htU z hz
  have hTm := hstab T' fun z hz => by rw [hTz]; exact hTU z hz
  have hUa : ∀ (p : k[X]), ∀ z ∈ U, aeval T' p z ∈ U := by
    intro p z hz
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add, LinearMap.add_apply]
      exact U.add_mem hp hq
    | monomial m c =>
      rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
      exact U.smul_mem c (hTm m z hz)
  have step : ∀ v, ∃ u ∈ U, ∃ w, v = u + t' w := by
    intro v
    obtain ⟨p, hp⟩ := hgen ((LinearMap.range t').mkQ v)
    refine ⟨∑ j, aeval T' (p j) (xs j), U.sum_mem fun j _ => hUa _ _ (hU j), ?_⟩
    have h0 : (LinearMap.range t').mkQ (v - ∑ j, aeval T' (p j) (xs j)) = 0 := by
      rw [map_sub, map_sum, hp, sub_eq_zero]
      exact Finset.sum_congr rfl fun j _ => by rw [← hmk, hxs]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨w, hw⟩ := h0
    exact ⟨w, by rw [hw]; abel⟩
  have iter : ∀ (m : ℕ) v, ∃ u ∈ U, ∃ w, v = u + (t' ^ m) w := by
    intro m
    induction m with
    | zero => intro v; exact ⟨0, U.zero_mem, v, by simp⟩
    | succ m ih =>
      intro v
      obtain ⟨u, hu, w, rfl⟩ := ih v
      obtain ⟨u', hu', w', rfl⟩ := step w
      refine ⟨u + (t' ^ m) u', U.add_mem hu (htm m u' hu'), w', ?_⟩
      rw [map_add, pow_succ, Module.End.mul_apply, add_assoc]
  refine eq_top_iff.mpr fun v _ => ?_
  obtain ⟨u, hu, w, rfl⟩ := iter e v
  rw [hte']
  simpa using hu
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclic_generators_invariant_top : ∀ (k : Type) [Field k] [IsAlgClosed k] (n e N : ℕ) (t T : Matrix (Fin n) (Fin n) k) (h : Polynomial k), 0 < e → h.Monic → h.Separable → t * T = T * t → t ^ e = 0 → (∀ x, t *ᵥ x = 0 → ∃ y, x = t ^ (e - 1) *ᵥ y) → (∀ x, ∃ y, Polynomial.aeval T h *ᵥ x = t *ᵥ y) → T.charpoly = h ^ (e * N) → ∃ x : Fin N → Fin n → k, ∀ U : Submodule k (Fin n → k), (∀ i, x i ∈ U) → (∀ z ∈ U, t *ᵥ z ∈ U) → (∀ z ∈ U, T *ᵥ z ∈ U) → U = ⊤ := by
  atlas_forward_decl GlobalTheory.DetInv.exists_generators_of_charpoly_eq_pow
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem special_fibre_generators : ∀ (p : ℕ) [Fact p.Prime] (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Free ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (h d N : ℕ) (b : Module.Basis (Fin d) ℤ_[p] Λ) (s : ℤ_[p] →+* WittVector p k) (ρ : Λ →+* Matrix (Fin h) (Fin h) (WittVector p k)), (∀ c : ℤ_[p], ρ (algebraMap ℤ_[p] Λ c) = s c • (1 : Matrix (Fin h) (Fin h) (WittVector p k))) → (∀ a : Λ, (ρ a).charpoly = ((LinearMap.mulLeft ℤ_[p] a).charpoly ^ N).map s) → ∃ x : Fin N → Fin h → k, Submodule.span k (Set.range fun ij : Fin N × Fin d => (ρ (b ij.2)).map WittVector.constantCoeff *ᵥ x ij.1) = ⊤ := by
  intro p _ Λ _ _ _ _ _ _ k _ _ _ h d N b s ρ hρ hch
  obtain ⟨e, π, a, u, h0, he, hp, hmon, hmem, -, hψ⟩ := GlobalTheory.T.exists_uniformizer_separable_reduction p Λ
  let c : WittVector p k →+* k := WittVector.constantCoeff
  let ψ : ℤ_[p] →+* k := c.comp s
  let Φ : Λ →+* Matrix (Fin h) (Fin h) k := c.mapMatrix.comp ρ
  have hΦ : ∀ l, Φ l = (ρ l).map c := fun l => rfl
  obtain ⟨hsep, hcp⟩ := hψ k ψ
  have hsurj : Function.Surjective c := fun r =>
    ⟨WittVector.teichmuller p r, by
      simp only [c, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩
  have hker : ∀ w, c w = 0 → (p : WittVector p k) ∣ w := fun w hw =>
    Ideal.mem_span_singleton.1 ((WittVector.mem_span_p_iff_coeff_zero_eq_zero w).2 hw)
  have hcp0 : c p = 0 := by rw [map_natCast, CharP.cast_eq_zero]
  obtain ⟨ht0, htk⟩ := GlobalTheory.T.reduction_uniformizer_nilpotent p (WittVector p k) k Λ h e c ρ π u
    (WittVector.p_nonzero p k) hsurj hker hcp0 he hp
  have hscal : Φ.comp (algebraMap ℤ_[p] Λ) = (algebraMap k (Matrix (Fin h) (Fin h) k)).comp ψ := by
    refine RingHom.ext fun z => ?_
    change Φ (algebraMap ℤ_[p] Λ z) = algebraMap k (Matrix (Fin h) (Fin h) k) (ψ z)
    rw [hΦ, hρ, Algebra.algebraMap_eq_smul_one]
    ext i j
    by_cases hij : i = j <;> simp [ψ, hij, Matrix.one_apply]
  have hscal' : ∀ z (l : Λ), Φ (z • l) = ψ z • Φ l := by
    intro z l
    have : Φ (algebraMap ℤ_[p] Λ z) = algebraMap k (Matrix (Fin h) (Fin h) k) (ψ z) :=
      RingHom.congr_fun hscal z
    rw [Algebra.smul_def, map_mul, this, ← Algebra.smul_def]
  have haev : Polynomial.aeval (Φ a) (h0.map ψ) = Φ (Polynomial.aeval a h0) := by
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map,
      hscal]
  obtain ⟨m, hm⟩ := Ideal.mem_span_singleton.1 hmem
  have hT : (Φ a).charpoly = (h0.map ψ) ^ (e * N) := by
    rw [hΦ, Matrix.charpoly_map, hch, Polynomial.map_map, Polynomial.map_pow, pow_mul, ← hcp]
  obtain ⟨x, hx⟩ := GlobalTheory.T.cyclic_generators_invariant_top k h e N (Φ π) (Φ a) (h0.map ψ) he (hmon.map ψ) hsep
    (by rw [← map_mul, ← map_mul, mul_comm]) ht0 htk
    (fun x => ⟨Φ m *ᵥ x, by rw [haev, hm, map_mul, Matrix.mulVec_mulVec]⟩) hT
  refine ⟨x, ?_⟩
  set U := Submodule.span k (Set.range fun ij : Fin N × Fin d =>
    (ρ (b ij.2)).map WittVector.constantCoeff *ᵥ x ij.1) with hU
  have key : ∀ (l : Λ) i, Φ l *ᵥ x i ∈ U := by
    intro l i
    rw [← b.sum_repr l, map_sum, Matrix.sum_mulVec]
    refine U.sum_mem fun j _ => ?_
    rw [hscal', Matrix.smul_mulVec]
    exact U.smul_mem _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  have stab : ∀ (l : Λ), ∀ z ∈ U, Φ l *ᵥ z ∈ U := by
    intro l z hz
    have : U ≤ U.comap (Φ l).mulVecLin := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨i, j⟩, rfl⟩
      change Φ l *ᵥ (Φ (b j) *ᵥ x i) ∈ U
      rw [Matrix.mulVec_mulVec, ← map_mul]
      exact key _ _
    exact this hz
  refine hx U (fun i => ?_) (stab π) (stab a)
  simpa using key 1 i

end GlobalTheory.DetInv
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_rep_reduction_structure : ∀ (p : ℕ) [Fact p.Prime] (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Free ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (h d N : ℕ) (b : Module.Basis (Fin d) ℤ_[p] Λ) (s : ℤ_[p] →+* WittVector p k) (ρ : Λ →+* Matrix (Fin h) (Fin h) (WittVector p k)), (∀ c : ℤ_[p], ρ (algebraMap ℤ_[p] Λ c) = s c • (1 : Matrix (Fin h) (Fin h) (WittVector p k))) → (∀ a : Λ, (ρ a).charpoly = ((LinearMap.mulLeft ℤ_[p] a).charpoly ^ N).map s) → ∃ x : Fin N → Fin h → k, Submodule.span k (Set.range fun ij : Fin N × Fin d => (ρ (b ij.2)).map WittVector.constantCoeff *ᵥ x ij.1) = ⊤ := by
  atlas_forward_decl GlobalTheory.DetInv.special_fibre_generators
end

section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem span_top_of_residue_span_top :
    ∀ (A k ι : Type) [CommRing A] [IsLocalRing A] [Field k] [Fintype ι] (h : ℕ) (c : A →+* k)
      (g : ι → Fin h → A), Function.Surjective c →
      Submodule.span k (Set.range fun i => fun j => c (g i j)) = ⊤ →
      Submodule.span A (Set.range g) = ⊤ := by
  intro A k ι _ _ _ _ h c g hc hspan
  have hker : RingHom.ker c = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective c hc)
  set N : Submodule A (Fin h → A) := Submodule.span A (Set.range g) with hN

  have hlift : ∀ w : Fin h → k, w ∈ Submodule.span k (Set.range fun i => fun j => c (g i j)) →
      ∃ v ∈ N, ∀ j, c (v j) = w j := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨g i, Submodule.subset_span ⟨i, rfl⟩, fun _ => rfl⟩
    | zero => exact ⟨0, N.zero_mem, fun j => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨b, hb, hb'⟩ := hy
      exact ⟨a + b, N.add_mem ha hb, fun j => by simp [ha', hb']⟩
    | smul t x _ hx =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨s, rfl⟩ := hc t
      exact ⟨s • a, N.smul_mem s ha, fun j => by simp [ha']⟩
  have hm : ∀ x : Fin h → A, (∀ j, x j ∈ IsLocalRing.maximalIdeal A) →
      x ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A (Fin h → A)) := by
    intro x hx
    have hx' : x = ∑ j, x j • (Pi.single j 1 : Fin h → A) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hx']
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hx j) Submodule.mem_top
  have hle : (⊤ : Submodule A (Fin h → A)) ≤
      N ⊔ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A (Fin h → A)) := by
    intro v _
    obtain ⟨n, hn, hn'⟩ := hlift (fun j => c (v j)) (by rw [hspan]; trivial)
    have hd : v - n ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A (Fin h → A)) := by
      apply hm
      intro j
      rw [← hker, RingHom.mem_ker]
      simp [hn']
    have : v = n + (v - n) := by abel
    rw [this]
    exact Submodule.add_mem_sup hn hd
  have hjac : IsLocalRing.maximalIdeal A ≤ (⊥ : Ideal A).jacobson :=
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  exact top_le_iff.mp
    (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hjac hle)

end GlobalTheory.DetInv
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.TiltResidue

theorem preTilt_onto_algClosed_residue : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (r : PreTilt O p →+* k), Function.Surjective r := by
  intro p _ C _ _ _ v O _ _ hpu _ hv
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hpm : (p : O) ∈ IsLocalRing.maximalIdeal O := hpu.out

  have hroot : ∀ y : O, ∃ z : O, z ^ p = y := by
    intro y
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C y) (Fact.out : p.Prime).pos
    have hw1 : v w ≤ 1 := by
      have h := hv.map_le_one y
      rw [← hw, map_pow] at h
      exact (pow_le_one_iff_of_nonneg zero_le (Fact.out : p.Prime).ne_zero).1 h
    obtain ⟨z, hz⟩ := hv.exists_of_le_one hw1
    exact ⟨z, hv.hom_inj (by rw [map_pow, hz, hw])⟩
  choose s hs using hroot
  have hcoeff : Function.Surjective (PreTilt.coeff (O := O) (p := p) 0) := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨show Perfection (ModP O p) p from
      ⟨fun n => Ideal.Quotient.mk _ (s^[n] y), fun n => ?_⟩, rfl⟩
    rw [← map_pow, Function.iterate_succ_apply', hs]
  let q : ModP O p →+* IsLocalRing.ResidueField O :=
    Ideal.Quotient.lift _ (IsLocalRing.residue O) (fun a ha =>
      (IsLocalRing.residue_eq_zero_iff a).2
        (Ideal.span_le.2 (Set.singleton_subset_iff.2 hpm) ha))
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  have hchar : CharP (IsLocalRing.ResidueField O) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
      rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]; exact hpm)
  have hac : IsAlgClosed (IsLocalRing.ResidueField O) := by
    refine IsAlgClosed.of_exists_root _ fun g hg hirr => ?_
    have hl : g ∈ Polynomial.lifts (IsLocalRing.residue O) :=
      (Polynomial.mem_lifts _).mpr
        (Polynomial.map_surjective _ IsLocalRing.residue_surjective g)
    obtain ⟨f, rfl, hdeg, hf⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hg
    have hd : (f.map (algebraMap O C)).degree ≠ 0 := by
      rw [Polynomial.degree_map_eq_of_injective hv.hom_inj]
      intro h0
      have := Polynomial.degree_pos_of_irreducible hirr
      rw [Polynomial.degree_eq_natDegree hf.ne_zero, Nat.cast_eq_zero] at h0
      rw [Polynomial.degree_eq_natDegree (hf.map _).ne_zero] at this
      have h1 : (f.map (IsLocalRing.residue O)).natDegree = 0 := by
        rw [← hdeg]; exact h0
      rw [h1] at this; exact lt_irrefl _ this
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root _ hd
    have hi : IsIntegral O a := ⟨f, hf, by rw [← Polynomial.eval_map]; exact ha⟩
    obtain ⟨b, rfl⟩ := hv.exists_of_le_one (r := a) (hv.mem_of_integral hi)
    have hb : f.eval b = 0 := hv.hom_inj (by
      rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map]; exact ha)
    refine ⟨IsLocalRing.residue O b, ?_⟩
    rw [Polynomial.eval_map, Polynomial.eval₂_hom, hb, map_zero]
  exact ⟨IsLocalRing.ResidueField O, inferInstance, hac, hchar, q.comp (PreTilt.coeff 0),
    hq.comp hcoeff⟩

end GlobalTheory.TiltResidue
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residue_field_tilt : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (r : PreTilt O p →+* k), Function.Surjective r := by
  atlas_forward_decl GlobalTheory.TiltResidue.preTilt_onto_algClosed_residue
end

section
section
open ReciprocityTheory.PGsh.Up GlobalTheory.Sandwich Matrix

namespace GlobalTheory.DetInv

theorem exists_span_top_of_datum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ ε : PreTilt O p, IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Free ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ], ∀ (h : ℕ) (D : Datum ε h Λ), ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[p] Λ), ∃ (N : ℕ) (x : Fin N → Fin h → Ainf p O) (y : Fin N → Fin h → ℤ_[p]), h = N * d ∧ Submodule.span (Ainf p O) (Set.range fun ij : Fin N × Fin d => D.ρM (b ij.2) *ᵥ x ij.1) = ⊤ ∧ Submodule.span ℤ_[p] (Set.range fun ij : Fin N × Fin d => D.ρT (b ij.2) *ᵥ y ij.1) = ⊤ := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ h D d b
  obtain ⟨hdom, hloc, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε
  haveI := hdom
  haveI := hloc
  obtain ⟨-, hmu, -⟩ := GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε hε
  obtain ⟨N, y, hN, hy, hcp⟩ := GlobalTheory.T.exists_rep_basis_charpoly p Λ h d b D.ρT
  obtain ⟨k, _, _, _, r, hr⟩ := GlobalTheory.T.exists_residue_field_tilt p C v O hv
  obtain ⟨hscal, -⟩ := GlobalTheory.T.sandwich_datum_scalar_action p C v O hv ε hε Λ h D
  let j : Ainf p O →+* WittVector p k := WittVector.map r
  let s : ℤ_[p] →+* WittVector p k := j.comp (ofPadic p O)
  let ρ : Λ →+* Matrix (Fin h) (Fin h) (WittVector p k) := (RingHom.mapMatrix j).comp D.ρM
  have hρscal : ∀ c : ℤ_[p], ρ (algebraMap ℤ_[p] Λ c) = s c • (1 : Matrix (Fin h) (Fin h) (WittVector p k)) := by
    intro c
    simp only [ρ, s, RingHom.comp_apply, hscal c, RingHom.mapMatrix_apply]
    ext i l
    by_cases hil : i = l <;> simp [hil]
  have hcpM : ∀ a : Λ, (D.ρM a).charpoly = ((LinearMap.mulLeft ℤ_[p] a).charpoly ^ N).map (ofPadic p O) := by
    intro a
    rw [GlobalTheory.DetInv.charpoly_eq_of_intertwined (Ainf p O) h (mu ε) D.F D.G ((D.ρT a).map (ofPadic p O)) (D.ρM a) hmu D.G_mul_F (D.F_act a), Matrix.charpoly_map, hcp a]
  have hcpρ : ∀ a, (ρ a).charpoly = ((LinearMap.mulLeft ℤ_[p] a).charpoly ^ N).map s := by
    intro a
    show ((D.ρM a).map j).charpoly = _
    rw [Matrix.charpoly_map, hcpM a, Polynomial.map_map]
  obtain ⟨xb, hxb⟩ := GlobalTheory.T.witt_rep_reduction_structure p Λ k h d N b s ρ hρscal hcpρ
  let c : Ainf p O →+* k := WittVector.constantCoeff.comp j
  have hc : Function.Surjective c := by
    intro z
    obtain ⟨w, rfl⟩ := hr z
    refine ⟨WittVector.teichmuller p w, ?_⟩
    simp [c, j, WittVector.map_teichmuller, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  choose lift hlift using hc
  refine ⟨N, fun i l => lift (xb i l), y, hN, ?_, hy⟩
  apply GlobalTheory.DetInv.span_top_of_residue_span_top (Ainf p O) k (Fin N × Fin d) h c _ (fun z => ⟨lift z, hlift z⟩)
  convert hxb using 3
  funext ij l
  rw [RingHom.map_mulVec]
  congr 1
  funext m
  exact hlift _

end GlobalTheory.DetInv
end

open ReciprocityTheory.PGsh.Up GlobalTheory.Sandwich Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_span_rhoM_rhoT_mulVec_eq_top : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ ε : PreTilt O p, IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Free ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ], ∀ (h : ℕ) (D : Datum ε h Λ), ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[p] Λ), ∃ (N : ℕ) (x : Fin N → Fin h → Ainf p O) (y : Fin N → Fin h → ℤ_[p]), h = N * d ∧ Submodule.span (Ainf p O) (Set.range fun ij : Fin N × Fin d => D.ρM (b ij.2) *ᵥ x ij.1) = ⊤ ∧ Submodule.span ℤ_[p] (Set.range fun ij : Fin N × Fin d => D.ρT (b ij.2) *ᵥ y ij.1) = ⊤ := by
  atlas_forward_decl GlobalTheory.DetInv.exists_span_top_of_datum
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem frames_exist : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ) , h = Module.finrank ℤ_[p] Λ * N → ∀ D : Datum ε h Λ, ∃ eT eM : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O), IsFrame (rhoTA D) eT ∧ IsFrame D.ρM eM ∧ ∀ (i : Fin N) (l : Λ), ∃ t : Fin h → ℤ_[p], eT (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l)) = fun j => ofPadic p O (t j) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ N h hh D
  haveI : Module.IsTorsionFree ℤ_[p] Λ :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective ℤ_[p] Λ)
  haveI : Module.Free ℤ_[p] Λ := inferInstance
  set d := Module.finrank ℤ_[p] Λ with hd
  have dpos : 0 < d := Module.finrank_pos
  obtain ⟨N', x, y, hN', hx, hy⟩ :=
    GlobalTheory.T.exists_span_rhoM_rhoT_mulVec_eq_top p C v O hv ε hε Λ h D d (Module.finBasis ℤ_[p] Λ)
  have hNN : N' = N := by
    have : d * N' = d * N := by rw [mul_comm, ← hN', hh]
    exact Nat.eq_of_mul_eq_mul_left dpos this
  subst hNN
  have hh' : h = N' * d := hN'

  have sM := (GlobalTheory.T.sandwich_datum_scalar_action p C v O hv ε hε Λ h D).1
  obtain ⟨eM, heM, -⟩ := GlobalTheory.T.ainf_frame_span_generation p O Λ N' d h (Module.finBasis ℤ_[p] Λ) D.ρM x sM hh' hx

  let ρ : Λ →+* Matrix (Fin h) (Fin h) (Ainf p O) :=
    (RingHom.mapMatrix (ofPadic p O)).comp D.ρT.toRingHom
  have hρ : ∀ l, ρ l = rhoTA D l := fun l => rfl
  have sT : ∀ c : ℤ_[p], ρ (algebraMap ℤ_[p] Λ c) = ofPadic p O c • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) := by
    intro c
    rw [hρ, rhoTA, AlgHom.commutes, Matrix.algebraMap_eq_diagonal]
    ext1 i j
    by_cases hij : i = j <;> simp [hij, Matrix.diagonal_apply, Matrix.one_apply]
  let L : (Fin h → ℤ_[p]) →ₗ[ℤ_[p]] (Fin h → Ainf p O) :=
    (Algebra.linearMap ℤ_[p] (Ainf p O)).compLeft (Fin h)
  have hL : ∀ w j, L w j = ofPadic p O (w j) := fun w j => rfl
  have hLmul : ∀ (l : Λ) (w : Fin h → ℤ_[p]), L (D.ρT l *ᵥ w) = ρ l *ᵥ (fun j => ofPadic p O (w j)) := by
    intro l w; funext j
    rw [hL, hρ, rhoTA, RingHom.map_mulVec]
    rfl
  have hxT : Submodule.span (Ainf p O) (Set.range fun ij : Fin N' × Fin d =>
      ρ (Module.finBasis ℤ_[p] Λ ij.2) *ᵥ (fun j => ofPadic p O (y ij.1 j))) = ⊤ := by
    set S := Set.range fun ij : Fin N' × Fin d =>
      ρ (Module.finBasis ℤ_[p] Λ ij.2) *ᵥ (fun j => ofPadic p O (y ij.1 j))
    have hle : Submodule.span ℤ_[p] (Set.range fun ij : Fin N' × Fin d =>
        D.ρT (Module.finBasis ℤ_[p] Λ ij.2) *ᵥ y ij.1) ≤
        ((Submodule.span (Ainf p O) S).restrictScalars ℤ_[p]).comap L := by
      rw [Submodule.span_le]
      rintro _ ⟨ij, rfl⟩
      show L _ ∈ Submodule.span (Ainf p O) S
      rw [hLmul]
      exact Submodule.subset_span ⟨ij, rfl⟩
    rw [eq_top_iff, ← (Pi.basisFun (Ainf p O) (Fin h)).span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have hk := hle (hy ▸ Submodule.mem_top : Pi.single k (1 : ℤ_[p]) ∈ _)
    have e1 : L (Pi.single k 1) = Pi.basisFun (Ainf p O) (Fin h) k := by
      funext j
      rw [hL, Pi.basisFun_apply]
      by_cases hkj : j = k
      · subst hkj; simp
      · simp [Pi.single_apply, hkj]
    rw [← e1]
    exact hk
  obtain ⟨eT, heT, heT1⟩ := GlobalTheory.T.ainf_frame_span_generation p O Λ N' d h (Module.finBasis ℤ_[p] Λ) ρ
    (fun i j => ofPadic p O (y i j)) sT hh' hxT
  refine ⟨eT, eM, heT, heM, fun i l => ⟨D.ρT l *ᵥ y i, ?_⟩⟩
  rw [heT1, ← hLmul]
  rfl

end GlobalTheory.DetInv
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_frame_comparison : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ) , h = Module.finrank ℤ_[p] Λ * N → ∀ D : Datum ε h Λ, ∃ eT eM : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O), IsFrame (rhoTA D) eT ∧ IsFrame D.ρM eM ∧ ∀ (i : Fin N) (l : Λ), ∃ t : Fin h → ℤ_[p], eT (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l)) = fun j => ofPadic p O (t j) := by
  atlas_forward_decl GlobalTheory.DetInv.frames_exist
end
