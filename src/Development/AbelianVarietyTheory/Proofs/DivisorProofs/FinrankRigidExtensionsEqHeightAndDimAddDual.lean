import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusDualAddFinrankKerVerschiebung
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusKernelIdealEqKernelRelativeFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppOneEqZeroOfKernelIdealOfCompEqPrimeSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFrobeniusKernelIdealLeFrobeniusKernelIde
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMapEqSelfOfInjectiveFiniteHopf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal

section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv.FrobKerOrder

theorem finrank_le_pow_of_aeval_surjective {n d : ℕ} {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] (x : Fin d → A) (hsurj : Function.Surjective (MvPolynomial.aeval (R := K) x))
    (hpow : ∀ i, x i ^ n = 0) :
    Module.finrank K A ≤ n ^ d := by
  classical
  let e : (Fin d → Fin n) → (Fin d →₀ ℕ) := fun a => Finsupp.equivFunOnFinite.symm fun i => a i
  let v : (Fin d → Fin n) → A := fun a => MvPolynomial.aeval (R := K) x (MvPolynomial.monomial (e a) 1)
  have hmono : ∀ m : Fin d →₀ ℕ,
      MvPolynomial.aeval (R := K) x (MvPolynomial.monomial m 1) ∈ Submodule.span K (Set.range v) := by
    intro m
    by_cases hm : ∀ i, m i < n
    · refine Submodule.subset_span ⟨fun i => ⟨m i, hm i⟩, ?_⟩
      have : e (fun i => ⟨m i, hm i⟩) = m := by
        ext i; simp [e]
      simp only [v, this]
    · push_neg at hm
      obtain ⟨i, hi⟩ := hm
      have h0 : MvPolynomial.aeval (R := K) x (MvPolynomial.monomial m 1) = 0 := by
        rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod]
        by_cases hmi : m i = 0
        · have hn : n = 0 := by omega
          subst hn
          have h10 : (1 : A) = 0 := by simpa using hpow i
          rw [← mul_one (∏ j ∈ m.support, x j ^ m j), h10, mul_zero]
        · apply Finset.prod_eq_zero (i := i) (by simpa using hmi)
          obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hi
          rw [hr, pow_add, hpow i, zero_mul]
      rw [h0]; exact Submodule.zero_mem _
  have htop : Submodule.span K (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨P, rfl⟩ := hsurj y
    rw [P.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    have : MvPolynomial.monomial m (MvPolynomial.coeff m P) =
        MvPolynomial.coeff m P • MvPolynomial.monomial m (1 : K) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Submodule.smul_mem _ _ (hmono m)
  have h1 := finrank_range_le_card (R := K) v
  rw [Set.finrank, htop, finrank_top] at h1
  simpa using h1

theorem finrank_le_pow_finrank_cot (p : ℕ) [hp : Fact p.Prime] (K H : Type) [Field K] [CharP K p]
    [CommRing H] [HopfAlgebra K H] [Module.Finite K H] :
    Module.finrank K (H ⧸ frobKerIdeal p K H) ≤ p ^ Module.finrank K (Cot K H) := by
  haveI := isHopfIdeal p K H
  set J := frobKerIdeal p K H with hJ
  let π := Ideal.Quotient.mkₐ K J
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective K J
  have hε : (counitAlgHom K (H ⧸ J)).comp π = counitAlgHom K H := rfl
  have hbij : Function.Bijective (AugCot.map π hε) := by
    refine ⟨?_, AugCot.map_surjective π hε hπ⟩
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, rfl⟩ := (AugCot.exact_kerMap_map π hε hπ y).1 hy
    rw [AugCot.kerMap_apply, AugCot.d_of_mem _ (AugCot.ker_le π hε z.2),
      Ideal.toCotangent_eq_zero]
    exact le_sq p K H (Ideal.Quotient.eq_zero_iff_mem.1 z.2)
  rw [(LinearEquiv.ofBijective _ hbij).finrank_eq]
  set ε := counitAlgHom K (H ⧸ J) with hεdef
  let b := Module.finBasis K (AugCot ε)
  choose x hx using fun i => (RingHom.ker ε).toCotangent_surjective (b i)
  have hsum : ∀ l : Fin (Module.finrank K (AugCot ε)) → K,
      AugCot.d ε (∑ i, l i • (x i : H ⧸ J)) = ∑ i, l i • b i := by
    intro l
    simp [map_sum, hx]
  have hmem : ∀ l : Fin (Module.finrank K (AugCot ε)) → K,
      (∑ i, l i • (x i : H ⧸ J)) ∈ RingHom.ker ε := by
    intro l
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (x i).2
  have hpow : ∀ f ∈ RingHom.ker ε, f ^ p = 0 := by
    intro f hf
    obtain ⟨a, rfl⟩ := hπ f
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal (R := K) hf)
  have : IsNoetherianRing (H ⧸ J) := isNoetherian_of_tower K inferInstance
  have hnil : IsNilpotent (RingHom.ker ε) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro f hf
    exact ⟨p, hpow f hf⟩
  have hspan : ∀ y ∈ RingHom.ker ε, ∃ l : Fin (Module.finrank K (AugCot ε)) → K,
      y - ∑ i, l i • (x i : H ⧸ J) ∈ RingHom.ker ε ^ 2 := by
    intro y hy
    refine ⟨b.repr (AugCot.d ε y), ?_⟩
    have h1 : AugCot.d ε (y - ∑ i, b.repr (AugCot.d ε y) i • (x i : H ⧸ J)) = 0 := by
      rw [map_sub, hsum, b.sum_repr, sub_self]
    rwa [AugCot.d_of_mem _ (sub_mem hy (hmem _)), Ideal.toCotangent_eq_zero] at h1
  exact finrank_le_pow_of_aeval_surjective (fun i => (x i : H ⧸ J))
    (GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent ε hnil _ (fun i => (x i).2) hspan)
    (fun i => hpow _ (x i).2)

end GlobalTheory.PDiv.FrobKerOrder
end
end

section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_frobenius_kernel_hopf_le_pow_cotangent : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H] [HopfAlgebra K H] [Module.Finite K H], Module.finrank K (H ⧸ frobKerIdeal p K H) ≤ p ^ Module.finrank K (Cot K H) := by
  first | exact @GlobalTheory.PDiv.FrobKerOrder.finrank_le_pow_finrank_cot | exact GlobalTheory.PDiv.FrobKerOrder.finrank_le_pow_finrank_cot | (intros; apply GlobalTheory.PDiv.FrobKerOrder.finrank_le_pow_finrank_cot <;> assumption)
end

section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem GlobalTheory.PDivGroup.height_le_finrank_cot_add_finrank_cot_dual (p : ℕ) [Fact p.Prime] (K : Type)
    [Field K] (h : (p : K) = 0) (G : PDivGroup p K) :
    G.height ≤ Module.finrank K (Cot K (G.A 1)) + Module.finrank K (Cot K (G.dual.A 1)) := by
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 h
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdimD : Module.finrank K (G.dual.A 1) = p ^ G.dual.height := by
    obtain ⟨q⟩ : Nonempty (PrimeSpectrum K) := inferInstance
    have e := G.dual.rank_eq 1 q
    rw [Module.rankAtStalk_eq_finrank_of_free] at e
    simpa using e
  have hhD : G.dual.height = G.height := by simp
  have hord := finrank_eq_ker_mul_range K (G.dual.A 1) _ ((relFrob h G.dual).app 1)
  have hD : Module.finrank K (G.dual.A 1 ⧸ kerIdeal ((relFrob h G.dual).app 1)) ≤
      p ^ Module.finrank K (Cot K (G.dual.A 1)) := by
    rw [← GlobalTheory.T.frobeniusKernelIdeal_eq_kernel_relativeFrobenius p K h G.dual 1]
    exact GlobalTheory.T.finrank_frobenius_kernel_hopf_le_pow_cotangent p K (G.dual.A 1)
  have hA : Module.finrank K (G.A 1 ⧸ kerIdeal ((relFrob h G).app 1)) ≤
      p ^ Module.finrank K (Cot K (G.A 1)) := by
    rw [← GlobalTheory.T.frobeniusKernelIdeal_eq_kernel_relativeFrobenius p K h G 1]
    exact GlobalTheory.T.finrank_frobenius_kernel_hopf_le_pow_cotangent p K (G.A 1)
  have hker : (kerIdeal ((relFrob h G).app 1)).restrictScalars K ≤
      LinearMap.ker ((verschiebung h G).app 1 :
        G.A 1 →ₐ[K] (frobTwist h G).A 1).toLinearMap := fun a ha =>
    GlobalTheory.T.app_one_eq_zero_of_kernel_ideal_of_comp_eq_prime_smul p K G (frobTwist h G) (relFrob h G) (verschiebung h G)
      (verschiebung_comp_relFrob h G) a ha
  have hV := GlobalTheory.T.finrank_frobeniusDual_add_finrank_ker_verschiebung p K h G
  have hq := Submodule.finrank_quotient_add_finrank
    ((kerIdeal ((relFrob h G).app 1)).restrictScalars K)
  rw [(Submodule.Quotient.restrictScalarsEquiv K (kerIdeal ((relFrob h G).app 1))).finrank_eq] at hq
  have hmono := Submodule.finrank_mono hker
  have hr : Module.finrank K (LinearMap.range ((relFrob h G.dual).app 1 :
        (frobTwist h G.dual).A 1 →ₐ[K] G.dual.A 1).toLinearMap) ≤
      p ^ Module.finrank K (Cot K (G.A 1)) := by omega
  have key : p ^ G.height ≤
      p ^ (Module.finrank K (Cot K (G.A 1)) + Module.finrank K (Cot K (G.dual.A 1))) := by
    rw [pow_add, mul_comm, ← hhD, ← hdimD, hord]
    exact Nat.mul_le_mul hD hr
  exact (Nat.pow_le_pow_iff_right hp2).1 key
end
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_le_cotangent_dim_add_dual_cotangent_dim : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), G.height ≤ Module.finrank K (Cot K (G.A 1)) + Module.finrank K (Cot K (G.dual.A 1)) := by
  atlas_forward_decl GlobalTheory.PDivGroup.height_le_finrank_cot_add_finrank_cot_dual
end

section
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_finrank_cotangent_le_finrank_frobeniusKernelQuotient : ∀ (p : ℕ) [Fact p.Prime] (k H : Type) [Field k] [CharP k p] [CommRing H] [HopfAlgebra k H] [Module.Finite k H], p ^ Module.finrank k (Cot k H) ≤ Module.finrank k (H ⧸ frobKerIdeal p k H) := by
  first | exact @GlobalTheory.PDiv.FrobKerOrder.pow_finrank_cot_le | exact GlobalTheory.PDiv.FrobKerOrder.pow_finrank_cot_le | (intros; apply GlobalTheory.PDiv.FrobKerOrder.pow_finrank_cot_le <;> assumption)
end

section
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ), kerIdeal ((relFrob h G).app n) ≤ frobKerIdeal p R (G.A n) := by
  first | exact @GlobalTheory.PDiv.kerIdeal_relFrob_le_frobKerIdeal | exact GlobalTheory.PDiv.kerIdeal_relFrob_le_frobKerIdeal | (intros; apply GlobalTheory.PDiv.kerIdeal_relFrob_le_frobKerIdeal <;> assumption)
end

section
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comap_map_eq_self_of_injective_finiteHopf : ∀ (k A B : Type) [Field k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A), Function.Injective f → ∀ J : Ideal B, Ideal.comap (f : B →ₐ[k] A) (Ideal.map (f : B →ₐ[k] A) J) = J := by
  first | exact @GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective | exact GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective | (intros; apply GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective <;> assumption)
end

section
section
set_option autoImplicit false

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra

namespace GlobalTheory.PDivGroup

theorem mulP_mem_kerIdeal_of_verschiebung_eq_zero (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (a : G.A 1) (ha : (verschiebung h G).app 1 a = 0) :
    G.mulP 1 a ∈ kerIdeal ((G.mulP 1).comp ((relFrob h G).app 1)) := by
  set K := kerIdeal ((G.mulP 1).comp ((relFrob h G).app 1)) with hK
  let x := Ideal.Quotient.mkₐ R K
  have hx := (kerIdeal_le_ker_iff ((G.mulP 1).comp ((relFrob h G).app 1)) x).1
    fun c hc => Ideal.Quotient.eq_zero_iff_mem.2 hc
  let y := x.comp ((relFrob h G).app 2 : (frobTwist h G).A 2 →ₐ[R] G.A 2)
  have hy : torsionIdeal R ((frobTwist h G).A 2) p ≤ RingHom.ker y :=
    (kerIdeal_le_ker_iff _ y).2 fun z => by
      have e : (relFrob h G).app 2 (mulBy R _ p z) =
          G.mulP 1 ((relFrob h G).app 1 ((frobTwist h G).res 1 z)) := by
        rw [map_mulBy, ← PDivGroup.res_app, mulP_res]
      have := hx ((frobTwist h G).res 1 z)
      rw [CoalgHomClass.counit_comp_apply] at this
      exact (congrArg x e).trans this
  obtain ⟨b, rfl⟩ := G.res_surjective 1 a
  rw [← PDivGroup.res_app] at ha
  have hb : (verschiebung h G).app 2 b ∈ torsionIdeal R ((frobTwist h G).A 2) p := by
    have : (verschiebung h G).app 2 b ∈ torsionIdeal R ((frobTwist h G).A 2) (p ^ 1) := by
      rw [← (frobTwist h G).ker_res 1]
      exact ha
    rwa [pow_one] at this
  have h1 : x ((relFrob h G).app 2 ((verschiebung h G).app 2 b)) = 0 := hy hb
  rw [relFrob_app_verschiebung_app] at h1
  rw [mulP_res]
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1

end GlobalTheory.PDivGroup
end

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mulP_mem_kerIdeal_comp_relFrob_of_verschiebung_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0) (G : PDivGroup p R) (a : G.A 1), (verschiebung h G).app 1 a = 0 → G.mulP 1 a ∈ kerIdeal ((G.mulP 1).comp ((relFrob h G).app 1)) := by
  atlas_forward_decl GlobalTheory.PDivGroup.mulP_mem_kerIdeal_of_verschiebung_eq_zero
end

section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PDivGroup.CotDim

theorem quot_finrank_le {k A : Type} [Field k] [CommRing A] [Algebra k A] [Module.Finite k A]
    {I J : Ideal A} (hIJ : I ≤ J) : Module.finrank k (A ⧸ J) ≤ Module.finrank k (A ⧸ I) := by
  let f : (A ⧸ I) →ₗ[k] (A ⧸ J) := (Ideal.Quotient.factorₐ k hIJ).toLinearMap
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hIJ
  have := LinearMap.finrank_range_le f
  rwa [LinearMap.range_eq_top.2 hf, finrank_top] at this

theorem finrank_level_one {p : ℕ} {k : Type} [Field k] (G : PDivGroup p k) :
    Module.finrank k (G.A 1) = p ^ G.height := by
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum k) := inferInstance
  have h := G.rank_eq 1 q
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  simpa using h

end GlobalTheory.PDivGroup.CotDim

open GlobalTheory.PDivGroup.CotDim in

theorem GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [IsAlgClosed k] [CharP k p] (Γ : PDivGroup p k) :
    Module.finrank k (Cot k (Γ.A 1)) + Module.finrank k (Cot k (Γ.dual.A 1)) ≤ Γ.height := by
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdimD := finrank_level_one Γ.dual
  have hmulP : Function.Injective (Γ.mulP 1) := fun a b e => by
    refine CartierDual.eq_of_forall_apply (R := k) fun φ => ?_
    obtain ⟨ψ, rfl⟩ := Γ.dual_mulP_surjective 1 φ
    change ψ.ofConv (Γ.mulP 1 a) = ψ.ofConv (Γ.mulP 1 b)
    rw [e]

  have hord := finrank_eq_ker_mul_range k (Γ.dual.A 1) _ ((relFrob hp Γ.dual).app 1)
  have haD : p ^ Module.finrank k (Cot k (Γ.dual.A 1)) ≤
      Module.finrank k (Γ.dual.A 1 ⧸ kerIdeal ((relFrob hp Γ.dual).app 1)) :=
    (GlobalTheory.T.pow_finrank_cotangent_le_finrank_frobeniusKernelQuotient p k (Γ.dual.A 1)).trans (quot_finrank_le (GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal p k hp Γ.dual 1))

  have hker : LinearMap.ker ((verschiebung hp Γ).app 1 :
        Γ.A 1 →ₐ[k] (frobTwist hp Γ).A 1).toLinearMap ≤
      (kerIdeal ((relFrob hp Γ).app 1)).restrictScalars k := fun a ha => by
    have h1 := GlobalTheory.T.mulP_mem_kerIdeal_comp_relFrob_of_verschiebung_eq_zero p k hp Γ a ha
    rw [kerIdeal_comp] at h1
    rw [Submodule.restrictScalars_mem,
      ← GlobalTheory.T.comap_map_eq_self_of_injective_finiteHopf k _ _ (Γ.mulP 1) hmulP (kerIdeal ((relFrob hp Γ).app 1))]
    exact h1
  have hV := GlobalTheory.T.finrank_frobeniusDual_add_finrank_ker_verschiebung p k hp Γ
  have hq := Submodule.finrank_quotient_add_finrank
    ((kerIdeal ((relFrob hp Γ).app 1)).restrictScalars k)
  rw [(Submodule.Quotient.restrictScalarsEquiv k (kerIdeal ((relFrob hp Γ).app 1))).finrank_eq] at hq
  have hmono := Submodule.finrank_mono hker
  have haA : p ^ Module.finrank k (Cot k (Γ.A 1)) ≤
      Module.finrank k (Γ.A 1 ⧸ kerIdeal ((relFrob hp Γ).app 1)) :=
    (GlobalTheory.T.pow_finrank_cotangent_le_finrank_frobeniusKernelQuotient p k (Γ.A 1)).trans (quot_finrank_le (GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal p k hp Γ 1))
  have hrD : Module.finrank k (Γ.A 1 ⧸ kerIdeal ((relFrob hp Γ).app 1)) ≤
      Module.finrank k (LinearMap.range ((relFrob hp Γ.dual).app 1 :
        (frobTwist hp Γ.dual).A 1 →ₐ[k] Γ.dual.A 1).toLinearMap) := by omega
  have key : p ^ (Module.finrank k (Cot k (Γ.A 1)) + Module.finrank k (Cot k (Γ.dual.A 1))) ≤
      p ^ Γ.height := by
    rw [pow_add, mul_comm, ← hdimD, hord]
    exact Nat.mul_le_mul haD (haA.trans hrD)
  exact (Nat.pow_le_pow_iff_right hp2).1 key
end
end

section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.PDivGroup.CotDim in

theorem GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le_of_cast_eq_zero (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] (hp : (p : k) = 0) (Γ : PDivGroup p k) :
    Module.finrank k (Cot k (Γ.A 1)) + Module.finrank k (Cot k (Γ.dual.A 1)) ≤ Γ.height := by
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 hp
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdimD := finrank_level_one Γ.dual
  have hmulP : Function.Injective (Γ.mulP 1) := fun a b e => by
    refine CartierDual.eq_of_forall_apply (R := k) fun φ => ?_
    obtain ⟨ψ, rfl⟩ := Γ.dual_mulP_surjective 1 φ
    change ψ.ofConv (Γ.mulP 1 a) = ψ.ofConv (Γ.mulP 1 b)
    rw [e]

  have hord := finrank_eq_ker_mul_range k (Γ.dual.A 1) _ ((relFrob hp Γ.dual).app 1)
  have haD : p ^ Module.finrank k (Cot k (Γ.dual.A 1)) ≤
      Module.finrank k (Γ.dual.A 1 ⧸ kerIdeal ((relFrob hp Γ.dual).app 1)) :=
    (GlobalTheory.T.pow_finrank_cotangent_le_finrank_frobeniusKernelQuotient p k (Γ.dual.A 1)).trans (quot_finrank_le (GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal p k hp Γ.dual 1))

  have hker : LinearMap.ker ((verschiebung hp Γ).app 1 :
        Γ.A 1 →ₐ[k] (frobTwist hp Γ).A 1).toLinearMap ≤
      (kerIdeal ((relFrob hp Γ).app 1)).restrictScalars k := fun a ha => by
    have h1 := GlobalTheory.T.mulP_mem_kerIdeal_comp_relFrob_of_verschiebung_eq_zero p k hp Γ a ha
    rw [kerIdeal_comp] at h1
    rw [Submodule.restrictScalars_mem,
      ← GlobalTheory.T.comap_map_eq_self_of_injective_finiteHopf k _ _ (Γ.mulP 1) hmulP (kerIdeal ((relFrob hp Γ).app 1))]
    exact h1
  have hV := GlobalTheory.T.finrank_frobeniusDual_add_finrank_ker_verschiebung p k hp Γ
  have hq := Submodule.finrank_quotient_add_finrank
    ((kerIdeal ((relFrob hp Γ).app 1)).restrictScalars k)
  rw [(Submodule.Quotient.restrictScalarsEquiv k (kerIdeal ((relFrob hp Γ).app 1))).finrank_eq] at hq
  have hmono := Submodule.finrank_mono hker
  have haA : p ^ Module.finrank k (Cot k (Γ.A 1)) ≤
      Module.finrank k (Γ.A 1 ⧸ kerIdeal ((relFrob hp Γ).app 1)) :=
    (GlobalTheory.T.pow_finrank_cotangent_le_finrank_frobeniusKernelQuotient p k (Γ.A 1)).trans (quot_finrank_le (GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal p k hp Γ 1))
  have hrD : Module.finrank k (Γ.A 1 ⧸ kerIdeal ((relFrob hp Γ).app 1)) ≤
      Module.finrank k (LinearMap.range ((relFrob hp Γ.dual).app 1 :
        (frobTwist hp Γ.dual).A 1 →ₐ[k] Γ.dual.A 1).toLinearMap) := by omega
  have key : p ^ (Module.finrank k (Cot k (Γ.A 1)) + Module.finrank k (Cot k (Γ.dual.A 1))) ≤
      p ^ Γ.height := by
    rw [pow_add, mul_comm, ← hdimD, hord]
    exact Nat.mul_le_mul haD (haA.trans hrD)
  exact (Nat.pow_le_pow_iff_right hp2).1 key
end
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cotangent_dim_add_dual_cotangent_dim_le_height : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), Module.finrank K (Cot K (G.A 1)) + Module.finrank K (Cot K (G.dual.A 1)) ≤ G.height := by
  atlas_forward_decl GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le_of_cast_eq_zero
end

section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem finite_omega_of_eq_zero {p : ℕ} {K : Type} [Field K] (h : (p : K) = 0)
    (G : PDivGroup p K) : Module.Finite K G.omega := by
  haveI : Module.Finite K (Cot K (G.A 1)) :=
    Module.Finite.of_surjective (AugCot.d (counitAlgHom K (G.A 1))) (AugCot.d_surjective _)
  exact Module.Finite.equiv (LinearEquiv.ofBijective _ (G.omegaLevel_one_bijective h)).symm

theorem finrank_rigExt_omega (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0)
    (G : PDivGroup p K) :
    Module.Finite K G.omega ∧ Module.Finite K G.RigExt ∧ Module.finrank K G.RigExt = G.height ∧
      Module.finrank K G.omega + Module.finrank K G.dual.omega = G.height := by
  have h1 := finite_omega_of_eq_zero h G
  have h2 := finite_omega_of_eq_zero h G.dual
  have e1 : Module.finrank K G.omega = Module.finrank K (Cot K (G.A 1)) :=
    (LinearEquiv.ofBijective _ (G.omegaLevel_one_bijective h)).finrank_eq
  have e2 : Module.finrank K G.dual.omega = Module.finrank K (Cot K (G.dual.A 1)) :=
    (LinearEquiv.ofBijective _ (G.dual.omegaLevel_one_bijective h)).finrank_eq
  have hsum : Module.finrank K G.omega + Module.finrank K G.dual.omega = G.height := by
    rw [e1, e2]
    exact le_antisymm (GlobalTheory.T.cotangent_dim_add_dual_cotangent_dim_le_height p K h G) (GlobalTheory.T.height_le_cotangent_dim_add_dual_cotangent_dim p K h G)

  have hr := (G.rigToLie h).rank_range_add_rank_ker
  rw [LinearMap.range_eq_top.2 (G.rigToLie_surjective h), rank_top,
    LinearMap.exact_iff.1 (G.exact_rigOfOmega_rigToLie h),
    (LinearEquiv.ofInjective _ (G.rigOfOmega_injective_of_eq_zero h)).rank_eq.symm] at hr
  have hfin : Module.Finite K G.RigExt := by
    haveI : Module.Free K G.RigExt := Module.Free.of_divisionRing K _
    rw [← Module.rank_lt_aleph0_iff, ← hr]
    exact Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 K _) (Module.rank_lt_aleph0 K _)
  refine ⟨h1, hfin, ?_, hsum⟩
  have e := (G.rigToLie h).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 (G.rigToLie_surjective h), finrank_top,
    LinearMap.exact_iff.1 (G.exact_rigOfOmega_rigToLie h),
    LinearMap.finrank_range_of_inj (G.rigOfOmega_injective_of_eq_zero h)] at e
  rw [← e, ← hsum, add_comm, Subspace.dual_finrank_eq]

end GlobalTheory.PDivGroup
end
