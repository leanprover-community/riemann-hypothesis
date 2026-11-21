import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertUniformization
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NotWeilIsGrpPullbackNoncomm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
import GroundTheory.GlobalFields.Adele.Approximation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFMulPosPrincipal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSectionIntegralFiniteIdeleUpToUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFFiniteIdeleUpToExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicCompactDensity.ExistsNatLocal

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.CMRiem

open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter

theorem exp_herm_swap {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (hL : L.IsLB)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) (l m : u.Λ) :
    Complex.exp (Real.pi * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)))) =
      Complex.exp (Real.pi * ((m : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) := by
  obtain ⟨i, hi⟩ := exists_chart u valueRules hL 0
  have hl : ⊤ ≤ (u.ex (0 + (l : Fin g → ℂ))).left ⁻¹ᵁ L.U i := by rwa [ex_add_period u 0 _ l.2]
  have hm : ⊤ ≤ (u.ex (0 + (m : Fin g → ℂ))).left ⁻¹ᵁ L.U i := by rwa [ex_add_period u 0 _ m.2]
  have hlm : ⊤ ≤ (u.ex (0 + (l : Fin g → ℂ) + m)).left ⁻¹ᵁ L.U i := by
    rwa [ex_add_period u _ _ m.2, ex_add_period u 0 _ l.2]
  have e1 := h.2.2.2 l i 0 hi
  have e2 := h.2.2.2 m i _ hl
  have e3 := h.2.2.2 m i 0 hi
  have e4 := h.2.2.2 l i _ hm
  have hc : (0 : Fin g → ℂ) + m + l = 0 + l + m := by abel
  rw [hc] at e4
  have hne := u.fr_ne i _ hlm
  rw [zero_add] at hne
  have hχl : χ l ≠ 0 := fun h0 ↦ by simpa [h0] using h.2.2.1 l
  have hχm : χ m ≠ 0 := fun h0 ↦ by simpa [h0] using h.2.2.1 m
  simp only [zero_add, zero_dotProduct, mul_zero, Complex.exp_add, Complex.exp_zero, one_mul] at e1 e2 e3 e4
  set X := Complex.exp (Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))
  set Y := Complex.exp (Real.pi / 2 * ((m : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))))
  have hX : X ≠ 0 := Complex.exp_ne_zero _
  have hY : Y ≠ 0 := Complex.exp_ne_zero _
  have key : (χ l * χ m * X * Y * u.fr i ((l : Fin g → ℂ) + m)) *
      Complex.exp (Real.pi * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)))) =
      (χ l * χ m * X * Y * u.fr i ((l : Fin g → ℂ) + m)) *
      Complex.exp (Real.pi * ((m : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) := by
    linear_combination (-1 : ℂ) * e1 - χ l * X * e2 + e3 + χ m * Y * e4
  exact mul_left_cancel₀ (by simp [hχl, hχm, hX, hY, hne]) key

end GlobalTheory.CMRiem

namespace GlobalTheory.CMRiem

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]

theorem cmEmb_bijective (φ : I → E →+* ℂ) (hφ : IsCMType φ) :
    Function.Bijective (Sum.elim φ fun i ↦ NumberField.ComplexEmbedding.conjugate (φ i)) := by
  have hnr : ∀ i, NumberField.ComplexEmbedding.conjugate (φ i) ≠ φ i := fun i h ↦
    (NumberField.InfinitePlace.isComplex_mk_iff.1 (NumberField.IsTotallyComplex.isComplex
      (NumberField.InfinitePlace.mk (φ i)))) (NumberField.ComplexEmbedding.isReal_iff.2 h)
  refine ⟨?_, ?_⟩
  · rintro (i | i) (j | j) h
    · simp only [Sum.elim_inl] at h
      obtain ⟨k, -, hk⟩ := hφ (φ i)
      rw [hk i (Or.inl rfl), hk j (Or.inl h)]
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      obtain ⟨k, -, hk⟩ := hφ (φ i)
      have := (hk i (Or.inl rfl)).trans (hk j (Or.inr h)).symm
      subst this
      exact absurd h.symm (hnr i)
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      obtain ⟨k, -, hk⟩ := hφ (φ j)
      have := (hk i (Or.inr h.symm)).trans (hk j (Or.inl rfl)).symm
      subst this
      exact absurd h (hnr i)
    · simp only [Sum.elim_inr] at h
      have h' : φ i = φ j := by
        simpa using congrArg NumberField.ComplexEmbedding.conjugate h
      obtain ⟨k, -, hk⟩ := hφ (φ i)
      rw [hk i (Or.inl rfl), hk j (Or.inl h')]
  · intro σ
    obtain ⟨i, hi, -⟩ := hφ σ
    rcases hi with h | h
    · exact ⟨Sum.inl i, h.symm⟩
    · exact ⟨Sum.inr i, h.symm⟩

theorem trace_eq_sum_cm (φ : I → E →+* ℂ) (hφ : IsCMType φ) (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ i, (φ i x + starRingEnd ℂ (φ i x)) := by
  have h1 := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := x)
  rw [eq_ratCast] at h1
  rw [h1, ← Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun σ : E →+* ℂ ↦ σ x) (fun σ ↦ σ x)
    (fun σ ↦ rfl), ← Fintype.sum_bijective _ (cmEmb_bijective φ hφ) (fun s ↦ (Sum.elim φ
      (fun i ↦ NumberField.ComplexEmbedding.conjugate (φ i)) s) x) (fun σ : E →+* ℂ ↦ σ x) (fun s ↦ rfl),
    Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  simp [NumberField.ComplexEmbedding.conjugate_coe_eq]

theorem cmEmb_linearIndependent (φ : I → E →+* ℂ) (hφ : IsCMType φ) :
    LinearIndependent ℂ (fun s : I ⊕ I ↦
      ((Sum.elim φ fun i ↦ NumberField.ComplexEmbedding.conjugate (φ i)) s : E → ℂ)) := by
  have h := linearIndependent_monoidHom E ℂ
  have hinj : Function.Injective (fun s : I ⊕ I ↦
      ((Sum.elim φ fun i ↦ NumberField.ComplexEmbedding.conjugate (φ i)) s : E →* ℂ)) := by
    intro s t hst
    apply (cmEmb_bijective φ hφ).1
    ext x
    exact DFunLike.congr_fun hst x
  exact h.comp _ hinj

end GlobalTheory.CMRiem

namespace GlobalTheory.CMRiem

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]

theorem span_eq_top_of_full (φ : I → E →+* ℂ) (hφ : IsCMType φ) {g : ℕ} (e : Fin g ≃ I) (L : Set E)
    (Λ : Submodule ℤ (Fin g → ℂ)) (hfull : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (hlat : ∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ φ (e j) x) : Submodule.span ℚ L = ⊤ := by
  set W := Submodule.span ℚ L
  let Φ : E →ₗ[ℚ] (Fin g → ℂ) :=
    (AddMonoidHom.mk' (fun x j ↦ φ (e j) x) (fun a b ↦ by funext j; simp)).toRatLinearMap
  let b := Module.finBasis ℚ W
  let v : Fin (Module.finrank ℚ W) → (Fin g → ℂ) := fun k ↦ Φ (b k)
  have hle : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) ≤ Submodule.span ℝ (Set.range v) := by
    rw [Submodule.span_le]
    intro w hw
    obtain ⟨x, hx, rfl⟩ := (hlat w).1 hw
    have hxW : x ∈ W := Submodule.subset_span hx
    have h1 : (fun j ↦ φ (e j) x) = Φ ((⟨x, hxW⟩ : W) : E) := rfl
    rw [h1, ← b.sum_repr ⟨x, hxW⟩]
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
    refine Submodule.sum_mem _ fun k _ ↦ ?_
    rw [← Rat.cast_smul_eq_qsmul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have h2g : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
    rw [Module.finrank_pi_fintype]; simp [Complex.finrank_real_complex, mul_comm]
  have hrank : 2 * g ≤ Module.finrank ℚ W := by
    calc 2 * g = Module.finrank ℝ (⊤ : Submodule ℝ (Fin g → ℂ)) := by rw [finrank_top, h2g]
      _ = Module.finrank ℝ (Submodule.span ℝ (Λ : Set (Fin g → ℂ))) := by rw [hfull]
      _ ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range v)) := Submodule.finrank_mono hle
      _ ≤ Fintype.card (Fin (Module.finrank ℚ W)) := finrank_range_le_card v
      _ = Module.finrank ℚ W := Fintype.card_fin _
  have hE : Module.finrank ℚ E = 2 * g := by
    rw [← NumberField.Embeddings.card E ℂ, ← Fintype.card_of_bijective (cmEmb_bijective φ hφ),
      Fintype.card_sum, ← Fintype.card_congr e, Fintype.card_fin]
    ring
  exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le W) (hE ▸ hrank))

theorem rat_of_span {L : Set E} (hL : Submodule.span ℚ L = ⊤) (f : E →+ ℝ)
    (hf : ∀ x ∈ L, ∃ q : ℚ, f x = q) (x : E) : ∃ q : ℚ, f x = q := by
  let S : Submodule ℚ E := (LinearMap.range (Algebra.linearMap ℚ ℝ)).comap f.toRatLinearMap
  have hLS : L ⊆ S := fun x hx ↦ by
    obtain ⟨q, hq⟩ := hf x hx
    exact ⟨q, by simp [hq]⟩
  have hS : S = ⊤ := eq_top_iff.2 (hL ▸ Submodule.span_le.2 hLS)
  have hx : x ∈ S := hS ▸ Submodule.mem_top
  obtain ⟨q, hq⟩ := hx
  exact ⟨q, by simpa using hq.symm⟩

end GlobalTheory.CMRiem

namespace GlobalTheory.CMRiem

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

def hermE (φ : I → E →+* ℂ) (h : I → ℝ) (x x' : E) : ℂ := ∑ i, (h i : ℂ) * (φ i x * starRingEnd ℂ (φ i x'))

theorem hermE_add_left (φ : I → E →+* ℂ) (h : I → ℝ) (a b x' : E) :
    hermE φ h (a + b) x' = hermE φ h a x' + hermE φ h b x' := by
  simp only [hermE, map_add, add_mul, mul_add, Finset.sum_add_distrib]

theorem hermE_add_right (φ : I → E →+* ℂ) (h : I → ℝ) (x a b : E) :
    hermE φ h x (a + b) = hermE φ h x a + hermE φ h x b := by
  simp only [hermE, map_add, add_mul, mul_add, Finset.sum_add_distrib]

theorem hermE_swap (φ : I → E →+* ℂ) (h : I → ℝ) (x x' : E) :
    hermE φ h x' x = starRingEnd ℂ (hermE φ h x x') := by
  simp only [hermE, map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

theorem hermE_one_im (φ : I → E →+* ℂ) (h : I → ℝ) (w : E) :
    (hermE φ h w 1).im = ∑ i, h i * (φ i w).im := by
  simp [hermE, Complex.im_sum]

end GlobalTheory.CMRiem

open GlobalTheory.CMRiem in

theorem GlobalTheory.cmPoint_herm_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)),
      ∃ β : E, ∀ i, (T.U.h i : ℂ) = 2 * Complex.I * φ i β := by
  intro E _ _ _ I _ φ hφ c y hc 𝔠 T
  obtain ⟨χ, hAH⟩ := T.U.ah
  have hLB : (T.X.diag T.U.c).IsLB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB (T.X.isLB T.U.c) _
  have hlatΛ : ∀ w, w ∈ T.U.u.Λ ↔ ∃ x ∈ lattice c y, w = fun j ↦ φ (T.U.e j) x := by
    intro w; rw [T.U.lat]; simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]
  have hH : ∀ x x', ((fun j ↦ φ (T.U.e j) x) ⬝ᵥ (Matrix.diagonal fun j ↦ (T.U.h (T.U.e j) : ℂ)).mulVec
      (star fun j ↦ φ (T.U.e j) x')) = hermE φ T.U.h x x' := by
    intro x x'
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, hermE]
    rw [Equiv.sum_comp T.U.e (fun i ↦ φ i x * ((T.U.h i : ℂ) * star (φ i x')))]
    exact Finset.sum_congr rfl fun i _ ↦ by simp only [Complex.star_def]; ring
  have hint : ∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, ∃ n : ℤ, (hermE φ T.U.h x x').im = n := by
    intro x hx x' hx'
    have hl : (fun j ↦ φ (T.U.e j) x) ∈ T.U.u.Λ := (hlatΛ _).2 ⟨x, hx, rfl⟩
    have hm : (fun j ↦ φ (T.U.e j) x') ∈ T.U.u.Λ := (hlatΛ _).2 ⟨x', hx', rfl⟩
    have hs := exp_herm_swap T.U.u hLB hAH ⟨_, hl⟩ ⟨_, hm⟩
    simp only [hH] at hs
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 hs
    refine ⟨n, ?_⟩
    have him := congrArg Complex.im hn
    rw [hermE_swap φ T.U.h x x'] at him
    simp at him
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have h2 : Real.pi * (2 * ((hermE φ T.U.h x x').im - n)) = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hπ
    · linarith
  have hspan := span_eq_top_of_full φ hφ T.U.e (lattice c y) T.U.u.Λ T.U.u.full hlatΛ
  let Bf : E → E →+ ℝ := fun x' ↦ AddMonoidHom.mk' (fun x ↦ (hermE φ T.U.h x x').im)
    (fun a b ↦ by simp only [hermE_add_left, Complex.add_im])
  let Cf : E → E →+ ℝ := fun x ↦ AddMonoidHom.mk' (fun x' ↦ (hermE φ T.U.h x x').im)
    (fun a b ↦ by simp only [hermE_add_right, Complex.add_im])
  have hrat1 : ∀ x' ∈ lattice c y, ∀ x, ∃ q : ℚ, (hermE φ T.U.h x x').im = q := fun x' hx' x ↦
    rat_of_span hspan (Bf x') (fun x hx ↦ by
      obtain ⟨n, hn⟩ := hint x hx x' hx'
      exact ⟨n, by simp [Bf, hn]⟩) x
  have hrat : ∀ x x', ∃ q : ℚ, (hermE φ T.U.h x x').im = q := fun x x' ↦
    rat_of_span hspan (Cf x) (fun x' hx' ↦ hrat1 x' hx' x) x'
  choose q hq using fun w ↦ hrat w 1
  let f : Module.Dual ℚ E :=
    { toFun := q
      map_add' := fun a b ↦ Rat.cast_injective (α := ℝ) (by
        rw [Rat.cast_add, ← hq, ← hq, ← hq]; exact (Bf 1).map_add a b)
      map_smul' := fun r a ↦ Rat.cast_injective (α := ℝ) (by
        rw [RingHom.id_apply, smul_eq_mul, Rat.cast_mul, ← hq, ← hq]
        have := (Bf 1).toRatLinearMap.map_smul r a
        simp only [AddMonoidHom.coe_toRatLinearMap, Rat.smul_def] at this
        rw [Rat.smul_def]
        exact this) }
  set β := ((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm f
  have htr : ∀ w, Algebra.trace ℚ E (β * w) = q w := fun w ↦ by
    rw [← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]; rfl
  let gc : I ⊕ I → ℂ := Sum.elim (fun i ↦ φ i β + Complex.I * T.U.h i / 2)
    (fun i ↦ starRingEnd ℂ (φ i β) - Complex.I * T.U.h i / 2)
  have hrel : ∑ s, gc s • ((Sum.elim φ fun i ↦ NumberField.ComplexEmbedding.conjugate (φ i)) s : E → ℂ) = 0 := by
    funext w
    simp only [Finset.sum_apply, Pi.smul_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, smul_eq_mul,
      NumberField.ComplexEmbedding.conjugate_coe_eq, Pi.zero_apply, gc]
    have ht := trace_eq_sum_cm φ hφ (β * w)
    rw [htr w] at ht
    have hqw : ((q w : ℚ) : ℂ) = ∑ i, ((T.U.h i : ℂ) * ((φ i w).im : ℂ)) := by
      have := hq w
      rw [hermE_one_im] at this
      rw [← Complex.ofReal_ratCast, ← this]
      push_cast; rfl
    rw [← Finset.sum_add_distrib]
    have hterm : ∀ i, (φ i β + Complex.I * T.U.h i / 2) * φ i w +
        (starRingEnd ℂ (φ i β) - Complex.I * T.U.h i / 2) * starRingEnd ℂ (φ i w) =
        (φ i (β * w) + starRingEnd ℂ (φ i (β * w))) - (T.U.h i : ℂ) * ((φ i w).im : ℂ) := by
      intro i
      have hz := Complex.sub_conj (φ i w)
      push_cast at hz
      rw [map_mul, map_mul]
      linear_combination (Complex.I * T.U.h i / 2) * hz + ((T.U.h i : ℂ) * ((φ i w).im : ℂ)) * Complex.I_sq
    rw [Finset.sum_congr rfl fun i _ ↦ hterm i, Finset.sum_sub_distrib, ← ht, ← hqw, sub_self]
  refine ⟨β, fun i ↦ ?_⟩
  have h0 := Fintype.linearIndependent_iff.1 (cmEmb_linearIndependent φ hφ) gc hrel (Sum.inl i)
  simp only [gc, Sum.elim_inl] at h0
  linear_combination (-2 * Complex.I) * h0 + (T.U.h i : ℂ) * Complex.I_sq
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_point_hodge_period_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)),
      ∃ β : E, ∀ i, (T.U.h i : ℂ) = 2 * Complex.I * φ i β := by
  atlas_forward_decl GlobalTheory.cmPoint_herm_eq
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_pairing_torsion_points : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB →
    ∀ (n : ℕ) (u : HolUnif A L n) (Hm : Matrix (Fin n) (Fin n) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ →
      ∀ (k : ℕ) (a b : Fin n → ℂ) (c : ℂˣ), 0 < k → a ∈ u.Λ → b ∈ u.Λ →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((a ⬝ᵥ Hm.mulVec (star b)).im : ℝ) : ℂ) / k) →
        Out.WeilIs A L k (u.ex ((k : ℂ)⁻¹ • a)) (u.ex ((k : ℂ)⁻¹ • b)) (unitOn c) := by
  first | exact @GlobalTheory.AHWeilAny.weilIs_exp_riemannForm | exact GlobalTheory.AHWeilAny.weilIs_exp_riemannForm | (intros; apply GlobalTheory.AHWeilAny.weilIs_exp_riemannForm <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjWeil

theorem unitOn_spMap (g : ℂ →+* ℂ) (c : ℂˣ) :
    Units.map (spMap g).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map g.toMonoidHom c) := by
  apply Units.ext
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g)
  exact (congrArg (fun q => q.hom (c : ℂ)) this).symm

theorem diag_lbIso {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} {X : Obj F 𝔠 S}
    {X' : Obj F 𝔠 S'} {b : S' ⟶ S} {p : X'.A.left ⟶ X.A.left} (hX : X'.IsPullBy X b p) (c : 𝔠.elt) :
    LBIso (X'.diag c) ((X.diag c).pull p) := by
  obtain ⟨φ₂, hsq, hiso⟩ := hX.pol
  have e : (lift (𝟙 X'.A) (𝟙 X'.A)).left ≫ φ₂ = p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left := by
    apply pullback.hom_ext
    · change _ ≫ (fst X.A X.A).left = _ ≫ (fst X.A X.A).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst]
      simp
    · change _ ≫ (snd X.A X.A).left = _ ≫ (snd X.A X.A).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd]
      simp
  have hI : LBIso (X'.diag c) ((X.P c).pull (p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso (hiso c) _ e.symm
  exact LBIso.trans (pull_isLB (X'.isLB c) _) (pull_isLB (X.isLB c) _) (pull_isLB (pull_isLB (X.isLB c) _) _) hI
    (GlobalTheory.GenSpread.lbIso_pull_pull (X.isLB c) p rfl)

theorem weil_transport : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (t : (Af K)ˣ)
    (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (g : ℂ ≃+* ℂ) (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
      X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
      ∀ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)), (∀ w, w ∈ u'.Λ ↔ ∃ x ∈ lattice c (y * (upIdele K E t)⁻¹), w = fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) →
        (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) →
        ∀ (u₀ : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E))) (Hm : Matrix (Fin (Module.finrank ℚ (FR E))) (Fin (Module.finrank ℚ (FR E))) ℂ) (χ : u₀.Λ → ℂ),
          u₀.ex = u'.ex → u₀.IsAH Hm χ →
          ∀ (k : ℕ) (w w' z z' : E), 0 < k → w ∈ lattice c y → w' ∈ lattice c y →
            z ∈ lattice c (y * (upIdele K E t)⁻¹) → z' ∈ lattice c (y * (upIdele K E t)⁻¹) →
            ((upIdele K E t : Af E) * algebraMap E (Af E) (z / k) - algebraMap E (Af E) (w / k)) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            ((upIdele K E t : Af E) * algebraMap E (Af E) (z' / k) - algebraMap E (Af E) (w' / k)) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            g (Complex.exp (-(2 * Real.pi * Complex.I) * ((∑ i, T.U.h i * (φ i w * starRingEnd ℂ (φ i w')).im : ℝ) : ℂ) / k)) =
              Complex.exp (-(2 * Real.pi * Complex.I) * ((((fun j ↦ g (φ (T.U.e j) z)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) z'))).im : ℝ) : ℂ) / k) := by
  intro _ _ _ K _ _ t E _ _ _ _ I _ φ g c y _ 𝔠 T X' p hp u' hlat hex u₀ Hm χ hex₀ hAH k w w' z z' hk hw hw' hz hz' hwz hwz'
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hL : (T.X.diag T.U.c).IsLB := pull_isLB (T.X.isLB T.U.c) _
  have hL' : (X'.diag T.U.c).IsLB := pull_isLB (X'.isLB T.U.c) _

  obtain ⟨χX, hχX⟩ := T.U.ah
  have mem : ∀ v, v ∈ lattice c y → (fun j ↦ φ (T.U.e j) v) ∈ T.U.u.Λ := fun v hv ↦
    (T.U.lat _).2 ⟨v, hv, funext fun j ↦ by simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]⟩
  have divk : ∀ v : E, (fun j ↦ φ (T.U.e j) (v / k)) = (k : ℂ)⁻¹ • fun j ↦ φ (T.U.e j) v := by
    intro v; funext j; simp [map_div₀, div_eq_inv_mul]
  set c₁ : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) *
    ((((fun j ↦ φ (T.U.e j) w) ⬝ᵥ (Matrix.diagonal fun j ↦ (T.U.h (T.U.e j) : ℂ)).mulVec
      (star fun j ↦ φ (T.U.e j) w')).im : ℝ) : ℂ) / k)) with hc₁
  have H1 := GlobalTheory.T.weil_pairing_torsion_points T.X.A T.X.ab _ hL _ T.U.u _ χX hχX k _ _ c₁ hk (mem w hw) (mem w' hw') rfl
  rw [← divk, ← divk] at H1

  let T₁ : Over (Sp ℂ) := Over.mk (𝟙 (Sp ℂ) ≫ spMap (g : ℂ →+* ℂ))
  let h : T₁ ⟶ 𝟙_ (Over (Sp ℂ)) := Over.homMk (spMap (g : ℂ →+* ℂ)) (by simp [T₁])
  have H2 := GlobalTheory.CommPairing.weilIs_pull globalFns_holds T.X.ab hL h H1
  rw [show h.left = spMap (g : ℂ →+* ℂ) from rfl, unitOn_spMap] at H2

  have H3 := (GlobalTheory.weilIs_baseChange_of_comm (Sp ℂ) (Sp ℂ) T.X.A X'.A (spMap (g : ℂ →+* ℂ)) p hp.grp _ _ hL hL'
    (diag_lbIso hp T.U.c) ℂ (𝟙 (Sp ℂ)) k (u'.ex (fun j ↦ g (φ (T.U.e j) (z / k))))
    (u'.ex (fun j ↦ g (φ (T.U.e j) (z' / k)))) _ _ _ (hex _ _ hwz).symm (hex _ _ hwz').symm).2 H2

  have memg : ∀ v, v ∈ lattice c (y * (upIdele K E t)⁻¹) → (fun j ↦ g (φ (T.U.e j) v)) ∈ u₀.Λ := by
    intro v hv
    rw [← u₀.ker, hex₀, u'.ker]
    exact (hlat _).2 ⟨v, hv, funext fun j ↦ by simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]⟩
  have divg : ∀ v : E, (fun j ↦ g (φ (T.U.e j) (v / k))) = (k : ℂ)⁻¹ • fun j ↦ g (φ (T.U.e j) v) := by
    intro v; funext j; simp [map_div₀, div_eq_inv_mul]
  set c₂ : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) *
    ((((fun j ↦ g (φ (T.U.e j) z)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) z'))).im : ℝ) : ℂ) / k)) with hc₂
  have H4 := GlobalTheory.T.weil_pairing_torsion_points X'.A X'.ab _ hL' _ u₀ Hm χ hAH k _ _ c₂ hk (memg z hz) (memg z' hz') rfl
  rw [hex₀, ← divg, ← divg] at H4
  have e := congrArg Units.val (GlobalTheory.weilIs_unique_fieldPoint (Sp ℂ) X'.A _ hL' ℂ (𝟙 (Sp ℂ)) k _ _ _ _ H4 H3)
  simp only [hc₁, hc₂, Units.val_mk0, Units.coe_map, MonoidHom.coe_coe] at e
  have hs : ((fun j ↦ φ (T.U.e j) w) ⬝ᵥ (Matrix.diagonal fun j ↦ (T.U.h (T.U.e j) : ℂ)).mulVec
      (star fun j ↦ φ (T.U.e j) w')).im = ∑ i, T.U.h i * (φ i w * starRingEnd ℂ (φ i w')).im := by
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, RCLike.star_def, Complex.im_sum]
    rw [← Equiv.sum_comp T.U.e]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mul_left_comm, Complex.im_ofReal_mul]
  rw [hs] at e
  exact e.symm

end GlobalTheory.ConjWeil
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_conjugate_cm_point : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (t : (Af K)ˣ)
    (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (g : ℂ ≃+* ℂ) (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
      X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
      ∀ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)), (∀ w, w ∈ u'.Λ ↔ ∃ x ∈ lattice c (y * (upIdele K E t)⁻¹), w = fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) →
        (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) →
        ∀ (u₀ : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E))) (Hm : Matrix (Fin (Module.finrank ℚ (FR E))) (Fin (Module.finrank ℚ (FR E))) ℂ) (χ : u₀.Λ → ℂ),
          u₀.ex = u'.ex → u₀.IsAH Hm χ →
          ∀ (k : ℕ) (w w' z z' : E), 0 < k → w ∈ lattice c y → w' ∈ lattice c y →
            z ∈ lattice c (y * (upIdele K E t)⁻¹) → z' ∈ lattice c (y * (upIdele K E t)⁻¹) →
            ((upIdele K E t : Af E) * algebraMap E (Af E) (z / k) - algebraMap E (Af E) (w / k)) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            ((upIdele K E t : Af E) * algebraMap E (Af E) (z' / k) - algebraMap E (Af E) (w' / k)) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            g (Complex.exp (-(2 * Real.pi * Complex.I) * ((∑ i, T.U.h i * (φ i w * starRingEnd ℂ (φ i w')).im : ℝ) : ℂ) / k)) =
              Complex.exp (-(2 * Real.pi * Complex.I) * ((((fun j ↦ g (φ (T.U.e j) z)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) z'))).im : ℝ) : ℂ) / k) := by
  atlas_forward_decl GlobalTheory.ConjWeil.weil_transport
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.ConjArith

theorem int_of_coprime_denoms (x : ℝ)
    (h : ∀ k : ℕ, 0 < k → ∃ b : ℕ, 0 < b ∧ Nat.Coprime b k ∧ ∃ n : ℤ, (b : ℝ) * x = n) :
    ∃ n : ℤ, x = n := by
  obtain ⟨b₁, hb₁, -, n₁, h₁⟩ := h 1 one_pos
  obtain ⟨b, hb, hcop, n, hn⟩ := h b₁ hb₁
  have hb₁R : (b₁ : ℝ) ≠ 0 := by exact_mod_cast hb₁.ne'
  have key : (n₁ : ℤ) * b = n * b₁ := by
    have : (n₁ : ℝ) * b = n * b₁ := by rw [← h₁, ← hn]; ring
    exact_mod_cast this
  have hdvd : (b₁ : ℤ) ∣ n₁ * b := ⟨n, by rw [key]; ring⟩
  have hc : IsCoprime (b₁ : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  obtain ⟨t, ht⟩ := hc.dvd_of_dvd_mul_right hdvd
  refine ⟨t, ?_⟩
  have : (b₁ : ℝ) * x = b₁ * t := by rw [h₁, ht]; push_cast; ring
  exact mul_left_cancel₀ hb₁R this

theorem int_core {S : Type} (m n : S → ℤ)
    (h : ∀ k : ℕ, 0 < k → ∃ a : ℤ, ∃ b : ℕ, Nat.Coprime b k ∧ IsCoprime a (k : ℤ) ∧
      ∀ s, (k : ℤ) ∣ n s - a * b * m s)
    (s₀ : S) (hm : m s₀ ≠ 0) (hpos : 0 < m s₀ * n s₀) : ∀ s, n s = m s := by
  have hn : n s₀ ≠ 0 := by
    rintro h0; rw [h0, mul_zero] at hpos; exact lt_irrefl _ hpos
  have h1 : m s₀ ∣ n s₀ := by
    obtain ⟨a, b, -, -, hk⟩ := h (m s₀).natAbs (Int.natAbs_pos.mpr hm)
    have h2 : ((m s₀).natAbs : ℤ) ∣ a * b * m s₀ :=
      Dvd.dvd.mul_left (Int.natAbs_dvd.mpr dvd_rfl) _
    have h3 := dvd_add (hk s₀) h2
    rw [sub_add_cancel] at h3
    exact Int.natAbs_dvd.mp h3
  have h2 : n s₀ ∣ m s₀ := by
    obtain ⟨a, b, hb, ha, hk⟩ := h (n s₀).natAbs (Int.natAbs_pos.mpr hn)
    have hself : ((n s₀).natAbs : ℤ) ∣ n s₀ := Int.natAbs_dvd.mpr dvd_rfl
    have h3 := dvd_sub hself (hk s₀)
    rw [sub_sub_cancel, _root_.mul_assoc] at h3
    have h4 : ((n s₀).natAbs : ℤ) ∣ b * m s₀ := ha.symm.dvd_of_dvd_mul_left h3
    have hbc : IsCoprime ((n s₀).natAbs : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hb.symm
    exact Int.natAbs_dvd.mp (hbc.dvd_of_dvd_mul_left h4)
  have heq : n s₀ = m s₀ := by
    have h5 := Int.natAbs_eq_of_dvd_dvd h1 h2
    rcases Int.natAbs_eq_natAbs_iff.mp h5 with h6 | h6
    · exact h6.symm
    · rw [h6] at hpos; nlinarith [mul_self_nonneg (m s₀)]
  intro s
  have hD : ∀ k : ℕ, 0 < k → (k : ℤ) ∣ n s * m s₀ - n s₀ * m s := by
    intro k hk
    obtain ⟨a, b, -, -, hks⟩ := h k hk
    have e : n s * m s₀ - n s₀ * m s
        = (n s - a * b * m s) * m s₀ - (n s₀ - a * b * m s₀) * m s := by ring
    rw [e]; exact dvd_sub ((hks s).mul_right _) ((hks s₀).mul_right _)
  have hD0 : n s * m s₀ - n s₀ * m s = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd (hD _ (Nat.succ_pos (n s * m s₀ - n s₀ * m s).natAbs))
    rw [Int.abs_eq_natAbs]; push_cast; omega
  rw [heq] at hD0
  have h7 : n s * m s₀ = m s * m s₀ := by linarith
  exact mul_right_cancel₀ hm h7

theorem form_eq_div : ∀ (S : Type) (f f' : S → ℝ) (A : ℝ), 0 < A → (∀ s, ∃ n : ℤ, f' s = n) →
    (∀ k : ℕ, 0 < k → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ Nat.Coprime b k ∧ IsCoprime a (k : ℤ) ∧
      ∀ s, (∃ n : ℤ, (b : ℝ) / A * f s = n) ∧ ∃ n : ℤ, f' s - a * ((b : ℝ) / A * f s) = k * n) →
    (∃ s, f s ≠ 0 ∧ 0 < f s * f' s) → ∀ s, f' s = f s / A := by
  intro S f f' A hA hint hk hex
  have hF : ∀ s, ∃ n : ℤ, f s / A = n := by
    intro s
    apply int_of_coprime_denoms
    intro k hk0
    obtain ⟨a, b, hb, hc, -, hs⟩ := hk k hk0
    obtain ⟨n, hn⟩ := (hs s).1
    exact ⟨b, hb, hc, n, by rw [← hn]; ring⟩
  choose m hm using hF
  choose n hn using hint
  have hcore : ∀ k : ℕ, 0 < k → ∃ a : ℤ, ∃ b : ℕ, Nat.Coprime b k ∧ IsCoprime a (k : ℤ) ∧
      ∀ s, (k : ℤ) ∣ n s - a * b * m s := by
    intro k hk0
    obtain ⟨a, b, -, hc, ha, hs⟩ := hk k hk0
    refine ⟨a, b, hc, ha, fun s => ?_⟩
    obtain ⟨t, ht⟩ := (hs s).2
    refine ⟨t, ?_⟩
    have : ((n s - a * b * m s : ℤ) : ℝ) = ((k * t : ℤ) : ℝ) := by
      push_cast
      rw [← hn s, ← ht, ← hm s]; ring
    exact_mod_cast this
  obtain ⟨s₀, hf0, hpos⟩ := hex
  have hmR : ((m s₀ : ℤ) : ℝ) * (n s₀ : ℝ) = f s₀ * f' s₀ / A := by
    rw [← hm s₀, ← hn s₀]; ring
  have hposZ : 0 < m s₀ * n s₀ := by
    have : (0 : ℝ) < ((m s₀ * n s₀ : ℤ) : ℝ) := by
      push_cast; rw [hmR]; exact div_pos hpos hA
    exact_mod_cast this
  have hm0 : m s₀ ≠ 0 := by
    rintro h0; rw [h0, zero_mul] at hposZ; exact lt_irrefl _ hposZ
  intro s
  rw [hn s, hm s]
  exact_mod_cast int_core m n hcore s₀ hm0 hposZ s

end GlobalTheory.ConjArith
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_function_ratio_determined : ∀ (S : Type) (f f' : S → ℝ) (A : ℝ), 0 < A → (∀ s, ∃ n : ℤ, f' s = n) →
    (∀ k : ℕ, 0 < k → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ Nat.Coprime b k ∧ IsCoprime a (k : ℤ) ∧
      ∀ s, (∃ n : ℤ, (b : ℝ) / A * f s = n) ∧ ∃ n : ℤ, f' s - a * ((b : ℝ) / A * f s) = k * n) →
    (∃ s, f s ≠ 0 ∧ 0 < f s * f' s) → ∀ s, f' s = f s / A := by
  atlas_forward_decl GlobalTheory.ConjArith.form_eq_div
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory

theorem cyclotomic_character_of_ringEquiv : ∀ (g : ℂ ≃+* ℂ) (k : ℕ), 0 < k → ∃ a : ℤ, IsCoprime a (k : ℤ) ∧
    ∀ n : ℤ, g (Complex.exp (2 * Real.pi * Complex.I * n / k)) = Complex.exp (2 * Real.pi * Complex.I * (a * n) / k) := by
  intro g k hk
  have hk0 : k ≠ 0 := hk.ne'
  haveI : NeZero k := ⟨hk0⟩
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / k) with hζ
  have hprim : IsPrimitiveRoot ζ k := Complex.isPrimitiveRoot_exp k hk0
  have hg : IsPrimitiveRoot (g ζ) k := hprim.map_of_injective g.injective
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hg.pow_eq_one
  have hcop : i.Coprime k := (hprim.pow_iff_coprime hk i).1 (hi ▸ hg)
  refine ⟨(i : ℤ), Nat.isCoprime_iff_coprime.2 hcop, fun n => ?_⟩
  have key : ∀ m : ℤ, Complex.exp (2 * Real.pi * Complex.I * m / k) = ζ ^ m := by
    intro m
    rw [hζ, ← Complex.exp_int_mul]
    congr 1
    ring
  calc g (Complex.exp (2 * Real.pi * Complex.I * n / k)) = g (ζ ^ n) := by rw [key n]
    _ = (ζ ^ i) ^ n := by rw [map_zpow₀, hi]
    _ = ζ ^ ((i : ℤ) * n) := by rw [← zpow_natCast, ← zpow_mul]
    _ = _ := by
      rw [← key]
      congr 1
      push_cast
      ring

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_action_roots_of_unity : ∀ (g : ℂ ≃+* ℂ) (k : ℕ), 0 < k → ∃ a : ℤ, IsCoprime a (k : ℤ) ∧
    ∀ n : ℤ, g (Complex.exp (2 * Real.pi * Complex.I * n / k)) = Complex.exp (2 * Real.pi * Complex.I * (a * n) / k) := by
  atlas_forward_decl GlobalTheory.cyclotomic_character_of_ringEquiv
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option autoImplicit false

namespace GlobalTheory

theorem normSq_embedding_eq_abs_norm_of_imagQuad {K : Type} [Field K] [NumberField K] (d : ℕ)
    (δ : K) (io : K →+* ℂ) (hK : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K))
    (x : K) : Complex.normSq (io x) = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  classical
  have hnoreal : ∀ w : InfinitePlace K, ¬ InfinitePlace.IsReal w := by
    intro w hw
    have h := InfinitePlace.conjugate_embedding_eq_of_isReal hw
    have h1 : w.embedding δ ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ]; simp
    have h2 : (starRingEnd ℂ) (w.embedding δ) = w.embedding δ := by
      have := congrArg (fun f : K →+* ℂ => f δ) h
      simpa [ComplexEmbedding.conjugate_coe_eq] using this
    obtain ⟨r, hr⟩ : ∃ r : ℝ, w.embedding δ = r :=
      ⟨(w.embedding δ).re, (Complex.conj_eq_iff_re.mp h2).symm⟩
    rw [hr] at h1
    have h3 : (r ^ 2 : ℝ) = -(d : ℝ) := by exact_mod_cast h1
    have h4 : (0 : ℝ) < d := Nat.cast_pos.mpr hd
    nlinarith [sq_nonneg r]
  have hR : InfinitePlace.nrRealPlaces K = 0 :=
    Fintype.card_eq_zero_iff.mpr ⟨fun w => hnoreal w.1 w.2⟩
  have hC : InfinitePlace.nrComplexPlaces K = 1 := by
    have := InfinitePlace.card_add_two_mul_card_eq_rank K; omega
  have hcard : Fintype.card (InfinitePlace K) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hR, hC]
  have huniv : (Finset.univ : Finset (InfinitePlace K)) = {InfinitePlace.mk io} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    exact ⟨Finset.mem_univ _, fun w _ => Fintype.card_le_one_iff.mp hcard.le w _⟩
  have h := InfinitePlace.prod_eq_abs_norm x
  rw [huniv, Finset.prod_singleton,
    (InfinitePlace.not_isReal_iff_isComplex.mp (hnoreal _)).mult_eq_two,
    InfinitePlace.apply] at h
  rw [Complex.normSq_eq_norm_sq, h]
  push_cast
  rfl

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option autoImplicit false

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sq_embedding_imag_quadratic : ∀ {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ x : K, Complex.normSq (io x) = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  atlas_forward_decl GlobalTheory.normSq_embedding_eq_abs_norm_of_imagQuad
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option autoImplicit false

namespace GlobalTheory.CMVal.NormCongr

variable {K : Type} [Field K] [NumberField K]

theorem natCast_mem_of_prime_dvd (P : HeightOneSpectrum (𝓞 K)) {q : ℕ}
    (hq : q.Prime) (h : q ∣ Ideal.absNorm P.asIdeal) : (q : 𝓞 K) ∈ P.asIdeal := by
  have : Fact q.Prime := ⟨hq⟩
  have := P.isPrime
  have : Finite (𝓞 K ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 K ⧸ P.asIdeal) q h
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hq.one_lt.ne hx
  have h1 : q • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
  rw [nsmul_eq_mul] at h1
  have h2 : ((q : ℕ) : 𝓞 K ⧸ P.asIdeal) = 0 := (mul_eq_zero.1 h1).resolve_right hx0
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h2

theorem coprime_absNorm_of_not_mem (P : HeightOneSpectrum (𝓞 K)) {k : ℕ} (hk : (k : 𝓞 K) ∉ P.asIdeal) :
    Nat.Coprime (Ideal.absNorm P.asIdeal) k := by
  refine Nat.coprime_of_dvd fun q hq h1 h2 => hk ?_
  obtain ⟨c, rfl⟩ := h2
  rw [Nat.cast_mul]
  exact P.asIdeal.mul_mem_right _ (natCast_mem_of_prime_dvd P hq h1)

theorem val_natCast (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Valued.v ((algebraMap K (Af K) (n : K)) v) = v.valuation K (algebraMap (𝓞 K) K (n : 𝓞 K)) := by
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← map_natCast (algebraMap (𝓞 K) K) n]

theorem val_natCast_le_one (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Valued.v ((algebraMap K (Af K) (n : K)) v) ≤ 1 := by
  rw [val_natCast]; exact v.valuation_le_one _

theorem val_natCast_lt_one (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (h : (n : 𝓞 K) ∈ v.asIdeal) :
    Valued.v ((algebraMap K (Af K) (n : K)) v) < 1 := by
  rw [val_natCast]; exact (v.valuation_lt_one_iff_mem _).2 h

end GlobalTheory.CMVal.NormCongr

open GlobalTheory.CMVal.IdeleIdeal GlobalTheory.CMVal.Euler in

theorem GlobalTheory.CMVal.NormCongr.absNorm_eq_div_modF : ∀ {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (k n : ℕ), 0 < n → k ∣ n → ∀ m : K, m ≠ 0 →
    (∀ v : HeightOneSpectrum (𝓞 K),
      (algebraMap K (Af K) (n : K)⁻¹ * (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m - 1)) v ∈
        v.adicCompletionIntegers K) →
    ∃ b : ℕ, 0 < b ∧ Nat.Coprime b k ∧ |((Algebra.norm ℚ m : ℚ) : ℝ)| = b / modF t := by
  intro K _ _ t k n hn hkn m hm hyp
  set p : (Af K)ˣ := Units.map (algebraMap K (Af K)).toMonoidHom (Units.mk0 m hm) with hp
  set a : (Af K)ˣ := t⁻¹ * p with ha
  have haval : (a : Af K) = ((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m := by
    simp [ha, hp]
  have hn0 : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'

  have hdiff : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v ((a : Af K) v - 1) ≤ Valued.v ((algebraMap K (Af K) (n : K)) v) := by
    intro v
    have h1 := hyp v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1
    have e : (a : Af K) - 1 = algebraMap K (Af K) (n : K) *
        (algebraMap K (Af K) (n : K)⁻¹ * (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m - 1)) := by
      rw [← _root_.mul_assoc, ← map_mul, mul_inv_cancel₀ hn0, map_one, _root_.one_mul, haval]
    have e2 : (a : Af K) v - 1 = ((a : Af K) - 1) v := by rw [sub_coord, one_coord]
    rw [e2, e, mul_coord, map_mul]
    exact mul_le_of_le_one_right' h1
  have hint : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v ((a : Af K) v) ≤ 1 := by
    intro v
    have e : (a : Af K) v = ((a : Af K) v - 1) + 1 := by ring
    rw [e]
    refine (Valued.v.map_add _ _).trans (max_le ?_ (by rw [map_one]))
    exact (hdiff v).trans (NormCongr.val_natCast_le_one v n)
  have hunit : ∀ v : HeightOneSpectrum (𝓞 K), (k : 𝓞 K) ∈ v.asIdeal → Valued.v ((a : Af K) v) = 1 := by
    intro v hk
    have hnv : (n : 𝓞 K) ∈ v.asIdeal := by
      obtain ⟨c, rfl⟩ := hkn
      rw [Nat.cast_mul]; exact v.asIdeal.mul_mem_right _ hk
    have hlt := (hdiff v).trans_lt (NormCongr.val_natCast_lt_one v hnv)
    have e : (a : Af K) v = 1 + ((a : Af K) v - 1) := by ring
    rw [e]
    exact Valuation.map_one_add_of_lt _ hlt

  have hmod : modF p = modF t * modF a := by
    rw [← IdeleModule.modF_mul, ha, _root_.mul_inv_cancel_left]
  have hpr := IdeleModule.modF_princ (Units.mk0 m hm)
  rw [← hp, Units.val_mk0] at hpr
  have hb := modF_eq hint
  refine ⟨Ideal.absNorm (idealOf a), ?_, ?_, ?_⟩
  · have hpos := IdeleModule.modF_pos a
    rw [hb] at hpos
    rcases Nat.eq_zero_or_pos (Ideal.absNorm (idealOf a)) with h0 | h0
    · rw [h0] at hpos; simp at hpos
    · exact h0
  · unfold idealOf
    rw [map_finprod Ideal.absNorm (finite_pow a)]
    refine finprod_induction (fun x : ℕ => Nat.Coprime x k) (Nat.coprime_one_left k)
      (fun x y hx hy => Nat.Coprime.mul hx hy) fun w => ?_
    rw [map_pow]
    rcases Nat.eq_zero_or_pos (ordAt a w) with h0 | h0
    · rw [h0, pow_zero]; exact Nat.coprime_one_left k
    · refine Nat.Coprime.pow_left _ (NormCongr.coprime_absNorm_of_not_mem w fun hk => ?_)
      have h1 := hunit w hk
      have : ordAt a w = 0 := by simp [ordAt, h1]
      omega
  · have htpos := IdeleModule.modF_pos t
    rw [hmod, hb] at hpr
    have e : |((Algebra.norm ℚ m : ℚ) : ℝ)| = (|((Algebra.norm ℚ m : ℚ) : ℝ)|)⁻¹⁻¹ := (inv_inv _).symm
    rw [e, ← hpr, mul_inv, inv_inv, div_eq_mul_inv, _root_.mul_comm]
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option autoImplicit false

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_coprime_idele_approximation : ∀ {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (k n : ℕ), 0 < n → k ∣ n → ∀ m : K, m ≠ 0 →
    (∀ v : HeightOneSpectrum (𝓞 K),
      (algebraMap K (Af K) (n : K)⁻¹ * (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m - 1)) v ∈
        v.adicCompletionIntegers K) →
    ∃ b : ℕ, 0 < b ∧ Nat.Coprime b k ∧ |((Algebra.norm ℚ m : ℚ) : ℝ)| = b / modF t := by
  atlas_forward_decl GlobalTheory.CMVal.NormCongr.absNorm_eq_div_modF
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.ConjApprox

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (finiteAdeleMap finiteCompletionMap finiteCompletionMap_mapsTo)

theorem exists_approx {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (n : ℕ) :
    ∃ m : K, m ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 K),
      (algebraMap K (Af K) (n : K)⁻¹ * (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m - 1)) v ∈
        v.adicCompletionIntegers K := by
  set a : Af K := algebraMap K (Af K) (n : K)⁻¹
  set ti : Af K := ((t⁻¹ : (Af K)ˣ) : Af K)
  set U : Set (Af K) := {x | ∀ v : HeightOneSpectrum (𝓞 K), (a * (ti * x - 1)) v ∈ v.adicCompletionIntegers K}
  have hO : IsOpen {z : Af K | ∀ v : HeightOneSpectrum (𝓞 K), z v ∈ v.adicCompletionIntegers K} :=
    RestrictedProduct.isOpen_forall_mem
      (A := fun v : HeightOneSpectrum (𝓞 K) => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
      fun _ => Valued.isOpen_valuationSubring _
  have hU : IsOpen U :=
    hO.preimage (continuous_const.mul ((continuous_const.mul continuous_id).sub continuous_const))
  have hV : IsOpen (U ∩ {0}ᶜ) := hU.inter isClosed_singleton.isOpen_compl
  obtain ⟨m0, hm0⟩ := Ideal.exists_maximal (𝓞 K)
  let v0 : HeightOneSpectrum (𝓞 K) :=
    ⟨m0, hm0.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm0 (RingOfIntegers.not_isField K)⟩
  haveI : Nontrivial (Af K) := ⟨⟨0, 1, fun h => by
    have h' := congrArg (fun x : Af K => x v0) h
    exact zero_ne_one h'⟩⟩
  have ht : (t : Af K) ∈ U ∩ {0}ᶜ := by
    refine ⟨fun v => ?_, t.ne_zero⟩
    have : ti * (t : Af K) - 1 = 0 := by simp [ti]
    rw [this, mul_zero]
    exact zero_mem _
  obtain ⟨m, hm1, hm2⟩ := GlobalTheory.AdeleCharTwist.denseRange_fin.exists_mem_open hV ⟨_, ht⟩
  refine ⟨m, fun h => hm2 (by simp [h]), hm1⟩

theorem finiteAdeleMap_algebraMap {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (x : K) : finiteAdeleMap K E (algebraMap K (Af K) x) = algebraMap E (Af E) (algebraMap K E x) :=
  FiniteAdeleRing.ext _ fun w => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_coe K E w x

theorem mem_of_approx {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (t : (Af K)ˣ) (c : Ideal (OF E)) (y : (Af E)ˣ) (k j : ℕ) (hk : 0 < k) (hj : 0 < j) (hjc : ((j : ℕ) : OF E) ∈ c) (m : K)
    (hm : ∀ v : HeightOneSpectrum (𝓞 K),
      (algebraMap K (Af K) ((k * j : ℕ) : K)⁻¹ * (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m - 1)) v ∈
        v.adicCompletionIntegers K) :
    ∀ u ∈ lattice c (y * (upIdele K E t)⁻¹), algebraMap K E m * u ∈ lattice c y ∧
        ((upIdele K E t : Af E) * algebraMap E (Af E) (u / k) - algebraMap E (Af E) (algebraMap K E m * u / k)) *
          ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
  intro u hu
  set zK : Af K := algebraMap K (Af K) ((k * j : ℕ) : K)⁻¹ * (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m - 1)
    with hzK
  set Z : Af E := finiteAdeleMap K E zK with hZ
  have hZi : ∀ w : HeightOneSpectrum (𝓞 E), Z w ∈ w.adicCompletionIntegers E := fun w =>
    finiteCompletionMap_mapsTo K E w (hm (w.under (𝓞 K)))
  have hjZ : (j : Af E) * Z ∈ hatO c := by
    have := GlobalTheory.CMVal.PicFin.mul_mem_hatO hjc hZi
    simpa only [map_natCast] using this
  set U' : Af E := ((upIdele K E t : (Af E)ˣ) : Af E) with hU'
  set Ui : Af E := (((upIdele K E t)⁻¹ : (Af E)ˣ) : Af E) with hUi
  set Yi : Af E := ((y⁻¹ : (Af E)ˣ) : Af E) with hYi
  set M : Af E := algebraMap E (Af E) (algebraMap K E m) with hM
  set Uu : Af E := algebraMap E (Af E) u with hUu
  set Kinv : Af E := algebraMap E (Af E) (k : E)⁻¹ with hKinv
  have e1 : U' * Ui = 1 := Units.mul_inv _
  have e3 : (k : Af E) * Kinv = 1 := by
    rw [hKinv, ← map_natCast (algebraMap E (Af E)), ← map_mul, mul_inv_cancel₀ (by exact_mod_cast hk.ne'), map_one]
  have eK : ((k * j : ℕ) : Af K) * algebraMap K (Af K) ((k * j : ℕ) : K)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap K (Af K)), ← map_mul,
      mul_inv_cancel₀ (by exact_mod_cast (Nat.mul_pos hk hj).ne'), map_one]
  have e2K : ((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m = 1 + ((k * j : ℕ) : Af K) * zK := by
    rw [hzK]; linear_combination (-(((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m - 1)) * eK
  have e2 : Ui * M = 1 + (k : Af E) * ((j : Af E) * Z) := by
    have := congrArg (finiteAdeleMap K E) e2K
    rw [map_mul, map_add, map_one, map_mul, map_natCast, finiteAdeleMap_algebraMap] at this
    have hUi' : Ui = finiteAdeleMap K E ((t⁻¹ : (Af K)ˣ) : Af K) := by rw [hUi, ← map_inv]; rfl
    rw [hUi', hM, this, hZ]
    push_cast
    ring
  have hA : Ui * M ∈ hatO c := by
    rw [e2]
    refine add_mem (one_mem _) (mul_mem ?_ hjZ)
    exact_mod_cast natCast_mem (hatO c) k
  have hu' : Uu * U' * Yi ∈ hatO c := by
    have h := hu
    simp only [lattice, Set.mem_setOf_eq, mul_inv_rev, inv_inv, Units.val_mul] at h
    rw [hUu, hU', hYi, _root_.mul_assoc]; exact h
  constructor
  · show algebraMap E (Af E) (algebraMap K E m * u) * Yi ∈ hatO c
    have : algebraMap E (Af E) (algebraMap K E m * u) * Yi = (Ui * M) * (Uu * U' * Yi) := by
      rw [map_mul]; linear_combination (-(M * Uu * Yi)) * e1
    rw [this]; exact mul_mem hA hu'
  · have : (U' * algebraMap E (Af E) (u / k) - algebraMap E (Af E) (algebraMap K E m * u / k)) * Yi =
        -((j : Af E) * Z) * (Uu * U' * Yi) := by
      simp only [div_eq_mul_inv, map_mul]
      rw [← hKinv, ← hM, ← hUu]
      linear_combination (Kinv * Uu * Yi * M) * e1 - (Kinv * Uu * Yi * U') * e2 - ((j : Af E) * Z * Uu * U' * Yi) * e3
    rw [this]; exact mul_mem (neg_mem hjZ) hu'

theorem approx_idele : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (t : (Af K)ˣ) (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ k : ℕ, 0 < k → ∃ (m : K) (b : ℕ), 0 < b ∧ Nat.Coprime b k ∧ Complex.normSq (io m) = b / modF t ∧
      ∀ u ∈ lattice c (y * (upIdele K E t)⁻¹), algebraMap K E m * u ∈ lattice c y ∧
        ((upIdele K E t : Af E) * algebraMap E (Af E) (u / k) - algebraMap E (Af E) (algebraMap K E m * u / k)) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
  intro K _ _ d δ io hK hd hδ E _ _ _ _ t c y hc k hk
  set N : ℕ := Ideal.absNorm c with hNdef
  have hN : 0 < N := Nat.pos_of_ne_zero (by rwa [hNdef, Ne, Ideal.absNorm_eq_zero_iff])
  have hNc : ((N : ℕ) : OF E) ∈ c := Ideal.absNorm_mem c
  obtain ⟨m, hm0, hm⟩ := exists_approx t (k * N)
  obtain ⟨b, hb0, hbk, hb⟩ := GlobalTheory.T.norm_coprime_idele_approximation t k (k * N) (Nat.mul_pos hk hN) (dvd_mul_right k N) m hm0 hm
  exact ⟨m, b, hb0, hbk, by rw [GlobalTheory.T.norm_sq_embedding_imag_quadratic d δ io hK hd hδ, hb], mem_of_approx t c y k N hk hN hNc m hm⟩

end GlobalTheory.ConjApprox
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_coprime_lattice_multiplier : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (t : (Af K)ˣ) (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ k : ℕ, 0 < k → ∃ (m : K) (b : ℕ), 0 < b ∧ Nat.Coprime b k ∧ Complex.normSq (io m) = b / modF t ∧
      ∀ u ∈ lattice c (y * (upIdele K E t)⁻¹), algebraMap K E m * u ∈ lattice c y ∧
        ((upIdele K E t : Af E) * algebraMap E (Af E) (u / k) - algebraMap E (Af E) (algebraMap K E m * u / k)) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
  atlas_forward_decl GlobalTheory.ConjApprox.approx_idele
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.ConjRiemannPos

theorem exists_ne_zero_mem_lattice {E : Type} [Field E] [NumberField E] (c : Ideal (OF E)) (y : (Af E)ˣ)
    (hc : c ≠ ⊥) : ∃ u ∈ lattice c y, u ≠ 0 := by
  set N : ℕ := Ideal.absNorm c with hNdef
  have hN : N ≠ 0 := by rwa [hNdef, Ne, Ideal.absNorm_eq_zero_iff]
  have hNc : (N : OF E) ∈ c := Ideal.absNorm_mem c
  obtain ⟨m, hm, hym⟩ := PI.AdCpctDenWork.exists_nat_adele (F := E) ((y⁻¹ : (Af E)ˣ) : Af E)
  have key := GlobalTheory.CMVal.PicFin.mul_mem_hatO hNc (y := (m : Af E) * ((y⁻¹ : (Af E)ˣ) : Af E)) (fun v => hym v)
  refine ⟨(N : E) * m, ?_, ?_⟩
  · show algebraMap E (Af E) ((N : E) * m) * _ ∈ hatO c
    rw [map_natCast, map_natCast] at key
    rw [map_mul, map_natCast, map_natCast, _root_.mul_assoc]
    exact key
  · exact mul_ne_zero (Nat.cast_ne_zero.mpr hN) (Nat.cast_ne_zero.mpr hm.ne')

theorem exists_pos_pair : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ g : ℂ ≃+* ℂ, (∀ x, g (io x) = io x) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ), (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (h : I → ℝ) (Hm : Matrix (Fin n) (Fin n) ℂ), 0 < n →
      (∀ z : Fin n → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ (Matrix.diagonal fun j ↦ (h (e j) : ℂ)).mulVec (star z)).re) → Hm.IsHermitian →
      (∀ z : Fin n → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
      ∃ u ∈ lattice c y, ∃ u' ∈ lattice c y, (∑ i, h i * (φ i u * starRingEnd ℂ (φ i u')).im) ≠ 0 ∧
        0 < (∑ i, h i * (φ i u * starRingEnd ℂ (φ i u')).im) * ((fun j ↦ g (φ (e j) u)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (e j) u'))).im := by
  intro K _ _ d δ io _ hd hδ g hg E _ _ _ _ I _ φ hφ c y hc n e h Hm hn hdiag _ hH
  obtain ⟨u, hu, hu0⟩ := exists_ne_zero_mem_lattice c y hc
  set N : ℕ := Ideal.absNorm c with hNdef
  have hN : N ≠ 0 := by rwa [hNdef, Ne, Ideal.absNorm_eq_zero_iff]
  have hNc : (N : OF E) ∈ c := Ideal.absNorm_mem c
  set δ' : E := algebraMap K E δ with hδ'
  have hδ'2 : δ' ^ 2 = -(d : E) := by rw [hδ', ← map_pow, hδ]; simp
  have hint : IsIntegral ℤ δ' := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    have e1 : algebraMap ℤ E (-(d : ℤ)) = -(d : E) := by simp
    rw [hδ'2, ← e1]
    exact isIntegral_algebraMap
  let b : 𝓞 E := ⟨δ', hint⟩
  have hb : algebraMap (𝓞 E) E b = δ' := rfl
  have hmem : (N : E) * δ' ∈ orderC c := mem_orderC.2 ⟨0, algebraMap (OF E) (𝓞 E) (N : OF E) * b,
    Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hNc), by simp [hb]⟩
  have hu' : (N : E) * δ' * u ∈ lattice c y := by
    show algebraMap E (Af E) _ * _ ∈ hatO c
    rw [map_mul, _root_.mul_assoc]
    exact mul_mem (algebraMap_mem_hatO hmem) hu
  refine ⟨u, hu, (N : E) * δ' * u, hu', ?_⟩
  set w : ℂ := io δ with hw
  have hφδ : ∀ i, φ i δ' = w := fun i => by rw [hδ', ← RingHom.comp_apply, hφ i]
  have hw2 : w ^ 2 = -(d : ℂ) := by rw [hw, ← map_pow, hδ]; simp
  have hre := congrArg Complex.re hw2
  have him := congrArg Complex.im hw2
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at hre him
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hwre : w.re = 0 := by
    by_contra hne
    have h0 : w.im = 0 := by
      have : 2 * w.re * w.im = 0 := by linarith
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd (by linarith : w.re = 0) hne
      · exact h1
    rw [h0] at hre
    nlinarith [mul_self_nonneg w.re]
  have hwim : w.im ^ 2 = d := by rw [hwre] at hre; nlinarith
  have hφu' : ∀ i, φ i ((N : E) * δ' * u) = (N : ℂ) * w * φ i u := fun i => by
    rw [map_mul, map_mul, map_natCast, hφδ]

  set P : ℝ := ∑ i, h i * Complex.normSq (φ i u) with hP
  have hS : (∑ i, h i * (φ i u * starRingEnd ℂ (φ i ((N : E) * δ' * u))).im) = -((N : ℝ) * w.im) * P := by
    rw [hP, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hφu']
    simp only [map_mul, Complex.conj_natCast, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.natCast_re, Complex.natCast_im, hwre, Complex.normSq_apply]
    ring
  have hPpos : 0 < P := by
    have hz : (fun j => φ (e j) u) ≠ 0 := by
      intro h0
      have := congrFun h0 ⟨0, hn⟩
      exact (map_ne_zero (φ (e ⟨0, hn⟩))).2 hu0 this
    have := hdiag _ hz
    convert this using 1
    simp only [Matrix.mulVec_diagonal, dotProduct, Complex.re_sum, Pi.star_apply]
    rw [hP, ← e.sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.mul_im, Complex.normSq_apply]
    ring

  set W : Fin n → ℂ := fun j => g (φ (e j) u) with hWdef
  have hW' : (star fun j => g (φ (e j) ((N : E) * δ' * u))) = (starRingEnd ℂ ((N : ℂ) * w)) • star W := by
    funext j
    simp only [Pi.star_apply, Pi.smul_apply, smul_eq_mul, hWdef, hφu', map_mul, map_natCast, hw, hg δ, star_mul',
      Complex.star_def]
  have hWne : W ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨0, hn⟩
    exact (map_ne_zero g).2 ((map_ne_zero (φ (e ⟨0, hn⟩))).2 hu0) this
  have hQ := hH W hWne
  set Q : ℂ := W ⬝ᵥ Hm.mulVec (star W) with hQdef
  have hQ' : (W ⬝ᵥ Hm.mulVec (star fun j => g (φ (e j) ((N : E) * δ' * u)))).im = -((N : ℝ) * w.im) * Q.re := by
    rw [hW', Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, ← hQdef]
    simp only [map_mul, Complex.conj_natCast, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.natCast_re, Complex.natCast_im, hwre]
    ring
  have hwim0 : w.im ≠ 0 := by
    intro h0; rw [h0] at hwim; nlinarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  refine ⟨?_, ?_⟩
  · rw [hS]
    exact mul_ne_zero (neg_ne_zero.2 (mul_ne_zero hNR.ne' hwim0)) hPpos.ne'
  · rw [hS, hQ']
    have hk : 0 < ((N : ℝ) * w.im) ^ 2 := by positivity
    have : -((N : ℝ) * w.im) * P * (-((N : ℝ) * w.im) * Q.re) = ((N : ℝ) * w.im) ^ 2 * (P * Q.re) := by ring
    rw [this]
    exact mul_pos hk (mul_pos hPpos hQ)

end GlobalTheory.ConjRiemannPos
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_riemann_form_galois_conjugate : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ g : ℂ ≃+* ℂ, (∀ x, g (io x) = io x) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ), (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (h : I → ℝ) (Hm : Matrix (Fin n) (Fin n) ℂ), 0 < n →
      (∀ z : Fin n → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ (Matrix.diagonal fun j ↦ (h (e j) : ℂ)).mulVec (star z)).re) → Hm.IsHermitian →
      (∀ z : Fin n → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
      ∃ u ∈ lattice c y, ∃ u' ∈ lattice c y, (∑ i, h i * (φ i u * starRingEnd ℂ (φ i u')).im) ≠ 0 ∧
        0 < (∑ i, h i * (φ i u * starRingEnd ℂ (φ i u')).im) * ((fun j ↦ g (φ (e j) u)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (e j) u'))).im := by
  atlas_forward_decl GlobalTheory.ConjRiemannPos.exists_pos_pair
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.ConjRiemann

theorem im_conj_form_eq : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
        X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
        ∀ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)), (∀ w, w ∈ u'.Λ ↔ ∃ x ∈ lattice c (y * (upIdele K E t)⁻¹), w = fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) →
          (∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
            v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
              u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') →
          (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) →
          ∀ (u₀ : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E))) (Hm : Matrix (Fin (Module.finrank ℚ (FR E))) (Fin (Module.finrank ℚ (FR E))) ℂ) (χ : u₀.Λ → ℂ),
            u₀.ex = u'.ex → u₀.IsAH Hm χ →
            ∀ x ∈ lattice c (y * (upIdele K E t)⁻¹), ∀ x' ∈ lattice c (y * (upIdele K E t)⁻¹),
              ((fun j ↦ g (φ (T.U.e j) x)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) x'))).im =
                (modF t)⁻¹ * ∑ i, T.U.h i * (φ i x * starRingEnd ℂ (φ i x')).im := by
  intro hPC hADR hADC K _ _ d δ io hK2 hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ _hΩ hTT E _ _ _ _ I _ φ _hφ hφK c y hc 𝔠 T X' p hp u' hlat
    _hdiff htors u₀ Hm χ hex hAH
  have W := GlobalTheory.T.galois_conjugate_cm_point hPC hADR hADC K t E I φ g c y hc 𝔠 T X' p hp u' hlat htors u₀ Hm χ hex hAH
  have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hexp : ∀ (r r' : ℝ) (k : ℕ), 0 < k →
      Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (r' : ℂ) / k) →
        ∃ n : ℤ, r' - r = k * n := by
    intro r r' k hk h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
    refine ⟨n, ?_⟩
    have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    have e1 : (2 * (Real.pi : ℂ) * Complex.I) * (((r' - r : ℝ) : ℂ) - ((k * n : ℝ) : ℂ)) = 0 := by
      have hn' := congrArg (fun z => z * (k : ℂ)) hn
      simp only [add_mul, div_mul_cancel₀ _ hk'] at hn'
      push_cast
      linear_combination hn'
    rcases mul_eq_zero.1 e1 with h0 | h0
    · exact absurd h0 h2pi
    · exact_mod_cast sub_eq_zero.1 h0
  have h0L : (0 : E) ∈ lattice c y := by
    show algebraMap E (Af E) 0 * _ ∈ hatO c
    rw [map_zero, zero_mul]; exact (hatO c).zero_mem
  have h0L' : (0 : E) ∈ lattice c (y * (upIdele K E t)⁻¹) := by
    show algebraMap E (Af E) 0 * _ ∈ hatO c
    rw [map_zero, zero_mul]; exact (hatO c).zero_mem
  have htrz : ∀ z ∈ lattice c (y * (upIdele K E t)⁻¹),
      ((upIdele K E t : Af E) * algebraMap E (Af E) (z / ((1 : ℕ) : E)) - algebraMap E (Af E) ((0 : E) / ((1 : ℕ) : E))) *
        ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
    intro z hz
    have hz' : algebraMap E (Af E) z * (((y * (upIdele K E t)⁻¹)⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := hz
    convert hz' using 1
    simp only [Nat.cast_one, div_one, zero_div, map_zero, sub_zero, mul_inv_rev, inv_inv, Units.val_mul]
    ring
  have htrw : ∀ w ∈ lattice c y,
      ((upIdele K E t : Af E) * algebraMap E (Af E) ((0 : E) / ((1 : ℕ) : E)) - algebraMap E (Af E) (w / ((1 : ℕ) : E))) *
        ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
    intro w hw
    have hw' : algebraMap E (Af E) w * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := hw
    have e : ((upIdele K E t : Af E) * algebraMap E (Af E) ((0 : E) / ((1 : ℕ) : E)) - algebraMap E (Af E) (w / ((1 : ℕ) : E))) *
        ((y⁻¹ : (Af E)ˣ) : Af E) = -(algebraMap E (Af E) w * ((y⁻¹ : (Af E)ˣ) : Af E)) := by
      simp only [Nat.cast_one, div_one, zero_div, map_zero, mul_zero, zero_sub, neg_mul]
    rw [e]; exact (hatO c).neg_mem hw'
  have hEg : ∀ z ∈ lattice c (y * (upIdele K E t)⁻¹), ∀ z' ∈ lattice c (y * (upIdele K E t)⁻¹), ∃ n : ℤ,
      ((fun j ↦ g (φ (T.U.e j) z)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) z'))).im = n := by
    intro z hz z' hz'
    have h := W 1 0 0 z z' one_pos h0L h0L hz hz' (htrz z hz) (htrz z' hz')
    have hl : (∑ i, T.U.h i * (φ i 0 * starRingEnd ℂ (φ i 0)).im) = 0 := by simp
    rw [hl] at h
    obtain ⟨n, hn⟩ := hexp 0 _ 1 one_pos (by rw [← h]; simp)
    exact ⟨n, by simpa using hn⟩
  have hEf : ∀ w ∈ lattice c y, ∀ w' ∈ lattice c y, ∃ n : ℤ,
      (∑ i, T.U.h i * (φ i w * starRingEnd ℂ (φ i w')).im) = n := by
    intro w hw w' hw'
    have h := W 1 w w' 0 0 one_pos hw hw' h0L' h0L' (htrw w hw) (htrw w' hw')
    have hl : ((fun j ↦ g (φ (T.U.e j) 0)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) 0))).im = 0 := by
      simp
    rw [hl] at h
    have h1 : Complex.exp (-(2 * Real.pi * Complex.I) * (((∑ i, T.U.h i * (φ i w * starRingEnd ℂ (φ i w')).im : ℝ)) : ℂ) /
        ((1 : ℕ) : ℂ)) = Complex.exp (-(2 * Real.pi * Complex.I) * ((0 : ℝ) : ℂ) / ((1 : ℕ) : ℂ)) :=
      g.injective (by rw [h]; simp)
    obtain ⟨n, hn⟩ := hexp _ 0 1 one_pos h1
    exact ⟨-n, by push_cast at hn ⊢; linarith⟩
  have hsc : ∀ (m : K) (u u' : E), (∑ i, T.U.h i * (φ i (algebraMap K E m * u) * starRingEnd ℂ (φ i (algebraMap K E m * u'))).im) =
      Complex.normSq (io m) * ∑ i, T.U.h i * (φ i u * starRingEnd ℂ (φ i u')).im := by
    intro m u u'
    have hφm : ∀ i, φ i (algebraMap K E m) = io m := fun i => by rw [← hφK i]; rfl
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, hφm, map_mul]
    have e : io m * φ i u * (starRingEnd ℂ (io m) * starRingEnd ℂ (φ i u')) =
        (Complex.normSq (io m) : ℂ) * (φ i u * starRingEnd ℂ (φ i u')) := by
      rw [Complex.normSq_eq_conj_mul_self]; ring
    rw [e, Complex.im_ofReal_mul]; ring
  have hApos : 0 < modF t :=
    finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun v => zpow_pos (by
      have : Ideal.absNorm v.asIdeal ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
      positivity) _
  have hcong : ∀ k : ℕ, 0 < k → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ Nat.Coprime b k ∧ IsCoprime a (k : ℤ) ∧
      ∀ s : {q : E × E // q.1 ∈ lattice c (y * (upIdele K E t)⁻¹) ∧ q.2 ∈ lattice c (y * (upIdele K E t)⁻¹)},
        (∃ n : ℤ, (b : ℝ) / modF t * (∑ i, T.U.h i * (φ i s.1.1 * starRingEnd ℂ (φ i s.1.2)).im) = n) ∧
        ∃ n : ℤ, ((fun j ↦ g (φ (T.U.e j) s.1.1)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) s.1.2))).im -
          a * ((b : ℝ) / modF t * (∑ i, T.U.h i * (φ i s.1.1 * starRingEnd ℂ (φ i s.1.2)).im)) = k * n := by
    intro k hk
    obtain ⟨a, ha, hga⟩ := GlobalTheory.T.galois_action_roots_of_unity g k hk
    obtain ⟨m, b, hb, hbk, hnorm, hm⟩ := GlobalTheory.T.norm_coprime_lattice_multiplier K d δ io hK2 hd hδ E t c y hc k hk
    refine ⟨a, b, hb, hbk, ha, ?_⟩
    rintro ⟨⟨u, u'⟩, hu, hu'⟩
    have hmu := (hm u hu).1
    have hmu' := (hm u' hu').1
    have hbA : (b : ℝ) / modF t * (∑ i, T.U.h i * (φ i u * starRingEnd ℂ (φ i u')).im) =
        ∑ i, T.U.h i * (φ i (algebraMap K E m * u) * starRingEnd ℂ (φ i (algebraMap K E m * u'))).im := by
      rw [hsc, hnorm]
    obtain ⟨n₀, hn₀⟩ := hEf _ hmu _ hmu'
    refine ⟨⟨n₀, by rw [hbA, hn₀]⟩, ?_⟩
    have h := W k (algebraMap K E m * u) (algebraMap K E m * u') u u' hk hmu hmu' hu hu' (hm u hu).2 (hm u' hu').2
    rw [hn₀] at h
    have e3 : Complex.exp (-(2 * Real.pi * Complex.I) * (((n₀ : ℝ)) : ℂ) / k) =
        Complex.exp (2 * Real.pi * Complex.I * ((-n₀ : ℤ) : ℂ) / k) := by
      congr 1; push_cast; ring
    rw [e3, hga (-n₀)] at h
    have e4 : Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * ((-n₀ : ℤ) : ℂ)) / k) =
        Complex.exp (-(2 * Real.pi * Complex.I) * ((((a * n₀ : ℤ) : ℝ)) : ℂ) / k) := by
      congr 1; push_cast; ring
    rw [e4] at h
    obtain ⟨n, hn⟩ := hexp _ _ k hk h
    refine ⟨n, ?_⟩
    show _ - _ * ((b : ℝ) / modF t * (∑ i, T.U.h i * (φ i u * starRingEnd ℂ (φ i u')).im)) = _
    rw [hbA, hn₀]
    push_cast at hn ⊢
    linarith
  have hpos : ∃ s : {q : E × E // q.1 ∈ lattice c (y * (upIdele K E t)⁻¹) ∧ q.2 ∈ lattice c (y * (upIdele K E t)⁻¹)},
      (∑ i, T.U.h i * (φ i s.1.1 * starRingEnd ℂ (φ i s.1.2)).im) ≠ 0 ∧
      0 < (∑ i, T.U.h i * (φ i s.1.1 * starRingEnd ℂ (φ i s.1.2)).im) *
        ((fun j ↦ g (φ (T.U.e j) s.1.1)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) s.1.2))).im := by
    obtain ⟨χT, hT⟩ := T.U.ah
    obtain ⟨u, hu, u', hu', hne, hp⟩ := GlobalTheory.T.cm_riemann_form_galois_conjugate K d δ io hK2 hd hδ g hTT.2.2.1 E I φ hφK c (y * (upIdele K E t)⁻¹) hc _ T.U.e
      T.U.h Hm Module.finrank_pos hT.2.1 hAH.1 hAH.2.1
    exact ⟨⟨(u, u'), hu, hu'⟩, hne, hp⟩
  intro x hx x' hx'
  have key := GlobalTheory.T.rational_function_ratio_determined {q : E × E // q.1 ∈ lattice c (y * (upIdele K E t)⁻¹) ∧ q.2 ∈ lattice c (y * (upIdele K E t)⁻¹)}
    (fun s => ∑ i, T.U.h i * (φ i s.1.1 * starRingEnd ℂ (φ i s.1.2)).im)
    (fun s => ((fun j ↦ g (φ (T.U.e j) s.1.1)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) s.1.2))).im)
    (modF t) hApos (fun s => hEg _ s.2.1 _ s.2.2) hcong hpos ⟨(x, x'), hx, hx'⟩
  rw [inv_mul_eq_div]
  exact key

end GlobalTheory.ConjRiemann
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_transport_cm_period : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
        X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
        ∀ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)), (∀ w, w ∈ u'.Λ ↔ ∃ x ∈ lattice c (y * (upIdele K E t)⁻¹), w = fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) →
          (∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
            v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
              u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') →
          (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) →
          ∀ (u₀ : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E))) (Hm : Matrix (Fin (Module.finrank ℚ (FR E))) (Fin (Module.finrank ℚ (FR E))) ℂ) (χ : u₀.Λ → ℂ),
            u₀.ex = u'.ex → u₀.IsAH Hm χ →
            ∀ x ∈ lattice c (y * (upIdele K E t)⁻¹), ∀ x' ∈ lattice c (y * (upIdele K E t)⁻¹),
              ((fun j ↦ g (φ (T.U.e j) x)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) x'))).im =
                (modF t)⁻¹ * ∑ i, T.U.h i * (φ i x * starRingEnd ℂ (φ i x')).im := by
  atlas_forward_decl GlobalTheory.ConjRiemann.im_conj_form_eq
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HermDiagCM

open ComplexConjugate

theorem matrix_eq_zero_of_im_form {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (Λ : Submodule ℤ (Fin n → ℂ)) (hs : Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤)
    (h0 : ∀ v ∈ Λ, ∀ v' ∈ Λ, (v ⬝ᵥ M.mulVec (star v')).im = 0) : M = 0 := by
  let B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun v v' => (v ⬝ᵥ M.mulVec (star v')).im)
      (fun a b c => by simp [add_dotProduct])
      (fun r a b => by simp [smul_dotProduct])
      (fun a b c => by simp [star_add, Matrix.mulVec_add, dotProduct_add])
      (fun r a b => by simp [star_smul, Matrix.mulVec_smul, dotProduct_smul])
  have h1 : ∀ v ∈ Λ, B v = 0 := fun v hv =>
    LinearMap.ext_on hs (fun v' hv' => by simpa [B] using h0 v hv v' hv')
  have hB : B = 0 := LinearMap.ext_on hs (fun v hv => by simpa using h1 v hv)
  have him : ∀ z w : Fin n → ℂ, (z ⬝ᵥ M.mulVec (star w)).im = 0 := fun z w => by
    have := congrArg (fun f => f z w) hB
    simpa [B] using this
  have hall : ∀ z w : Fin n → ℂ, z ⬝ᵥ M.mulVec (star w) = 0 := fun z w => by
    apply Complex.ext
    · have := him (Complex.I • z) w
      simpa [smul_dotProduct] using this
    · simpa using him z w
  ext i j
  have := hall (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec_single, single_dotProduct] using this

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sum_embeddings_eq {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : GlobalTheory.CMVal.IsCMType φ)
    (w : E) : ∑ σ : E →+* ℂ, σ w = ∑ i, (φ i w + conj (φ i w)) := by
  let f : I × Bool → (E →+* ℂ) := fun p => cond p.2 (ComplexEmbedding.conjugate (φ p.1)) (φ p.1)
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, a⟩ ⟨j, b⟩ hij
      have uniq : ∀ k l, φ k = φ l ∨ φ k = ComplexEmbedding.conjugate (φ l) → k = l := by
        intro k l hkl
        obtain ⟨m, -, hm⟩ := hφ (φ k)
        exact (hm k (Or.inl rfl)).trans (hm l hkl).symm
      cases a <;> cases b <;> simp only [f, cond_true, cond_false] at hij
      · simp [uniq i j (Or.inl hij)]
      · have hij' := uniq i j (Or.inr hij)
        subst hij'
        exact absurd (ComplexEmbedding.isReal_iff.mpr hij.symm)
          (IsTotallyComplex.complexEmbedding_not_isReal (φ i))
      · have hij' := uniq j i (Or.inr hij.symm)
        subst hij'
        exact absurd (ComplexEmbedding.isReal_iff.mpr hij)
          (IsTotallyComplex.complexEmbedding_not_isReal (φ j))
      · have : φ i = φ j := by
          have := congrArg ComplexEmbedding.conjugate hij
          simpa using this
        simp [uniq i j (Or.inl this)]
    · intro σ
      obtain ⟨i, hi, -⟩ := hφ σ
      rcases hi with h | h
      · exact ⟨(i, false), h.symm⟩
      · exact ⟨(i, true), h.symm⟩
  rw [← Fintype.sum_bijective f hf (fun p => f p w) (fun σ => σ w) (fun _ => rfl),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Fintype.sum_bool]
  simp [f, ComplexEmbedding.conjugate_coe_eq, add_comm]

theorem sum_embeddings_map (g : ℂ ≃+* ℂ) (w : E) :
    ∑ σ : E →+* ℂ, g (σ w) = ∑ σ : E →+* ℂ, σ w := by
  let eq : (E →+* ℂ) ≃ (E →+* ℂ) :=
    { toFun := fun σ => (g : ℂ →+* ℂ).comp σ
      invFun := fun σ => (g.symm : ℂ →+* ℂ).comp σ
      left_inv := fun σ => by ext x; simp
      right_inv := fun σ => by ext x; simp }
  exact Fintype.sum_equiv eq _ _ (fun σ => by simp [eq])

theorem term_eq (σ : E →+* ℂ) (β x x' : E) (hβ : conj (σ β) = -σ β) :
    (2 * Complex.I * σ β) * (((σ x * conj (σ x')).im : ℝ) : ℂ) =
      σ (β * x * IsCMField.complexConj E x') + conj (σ (β * x * IsCMField.complexConj E x')) := by
  have e1 : σ (β * x * IsCMField.complexConj E x') = σ β * (σ x * conj (σ x')) := by
    rw [map_mul, map_mul, IsCMField.complexEmbedding_complexConj]; ring
  rw [e1, map_mul, hβ]
  have hs := Complex.sub_conj (σ x * conj (σ x'))
  push_cast at hs
  linear_combination (-σ β) * hs

end CM

end GlobalTheory.HermDiagCM

open ComplexConjugate in

theorem GlobalTheory.HermDiagCM.diagonal_of_conj_form : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), 0 < d → δ ^ 2 = -(d : K) →
    ∀ g : ℂ ≃+* ℂ, (∀ x, g (io x) = io x) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) →
      ∀ (n : ℕ) (e : Fin n ≃ I) (Λ : Submodule ℤ (Fin n → ℂ)) (L : Set E),
        Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ → (∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ g (φ (e j) x)) →
      ∀ (h : I → ℝ) (β : E), (∀ i, (h i : ℂ) = 2 * Complex.I * φ i β) → ∀ N : ℝ, 0 < N →
      ∀ Hm : Matrix (Fin n) (Fin n) ℂ, Hm.IsHermitian →
        (∀ x ∈ L, ∀ x' ∈ L, ((fun j ↦ g (φ (e j) x)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (e j) x'))).im =
          N⁻¹ * ∑ i, h i * (φ i x * starRingEnd ℂ (φ i x')).im) →
        ∃ h' : I → ℝ, Hm = Matrix.diagonal (fun j ↦ (h' (e j) : ℂ)) ∧
          ∀ i, g ((h i : ℂ) * (Real.sqrt d : ℝ)) = (N : ℂ) * ((h' i : ℂ) * (Real.sqrt d : ℝ)) := by
  intro K _ _ d δ io hd hδ g hg E _ _ _ _ I _ φ hφ hio n e Λ L hs hΛ h β hh N hN Hm hHm hform
  have hconj : ∀ (σ : E →+* ℂ) (y : E), conj (σ y) = σ (IsCMField.complexConj E y) :=
    fun σ y => (IsCMField.complexEmbedding_complexConj E σ y).symm
  have hgcomp : ∀ i y, ((g : ℂ →+* ℂ).comp (φ i)) y = g (φ i y) := fun i y => rfl
  have hβi : ∀ i, conj (φ i β) = -(φ i β) := by
    intro i
    have h2 : conj ((h i : ℂ)) = (h i : ℂ) := Complex.conj_ofReal _
    rw [hh i, map_mul, map_mul, Complex.conj_I, map_ofNat] at h2
    have h3 : (2 * Complex.I : ℂ) ≠ 0 := by simp
    have h4 : (2 * Complex.I) * conj (φ i β) = (2 * Complex.I) * (-(φ i β)) := by
      linear_combination -h2
    exact mul_left_cancel₀ h3 h4
  have hcβ : ∀ i, IsCMField.complexConj E β = -β := fun i =>
    (φ i).injective (by rw [← hconj, hβi, map_neg])
  have hgc : ∀ i y, conj (g (φ i y)) = g (conj (φ i y)) := by
    intro i y
    rw [← hgcomp, hconj, hconj, hgcomp]
  have hgβ : ∀ i, conj (g (φ i β)) = -(g (φ i β)) := by
    intro i
    rw [hgc, hβi, map_neg]
  set h' : I → ℝ := fun i => ((2 * Complex.I * g (φ i β)) / N).re with hh'def
  have hh' : ∀ i, (h' i : ℂ) = 2 * Complex.I * g (φ i β) / N := by
    intro i
    exact Complex.conj_eq_iff_re.mp (by
      rw [map_div₀, map_mul, map_mul, Complex.conj_I, hgβ i, map_ofNat, Complex.conj_ofReal]; ring)
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨h', ?_, ?_⟩
  · set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun j ↦ (h' (e j) : ℂ)) with hD
    suffices Hm - D = 0 from sub_eq_zero.mp this
    apply matrix_eq_zero_of_im_form (Hm - D) Λ hs
    intro v hv v' hv'
    obtain ⟨x, hx, rfl⟩ := (hΛ v).mp hv
    obtain ⟨x', hx', rfl⟩ := (hΛ v').mp hv'
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_im, hform x hx x' hx', sub_eq_zero]
    have hDv : ((fun j ↦ g (φ (e j) x)) ⬝ᵥ D.mulVec (star fun j ↦ g (φ (e j) x'))).im =
        ∑ i, h' i * (g (φ i x) * conj (g (φ i x'))).im := by
      rw [dotProduct, Complex.im_sum]
      rw [← Equiv.sum_comp e (fun i => h' i * (g (φ i x) * conj (g (φ i x'))).im)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [hD, Matrix.mulVec_diagonal, Pi.star_apply, Complex.star_def]
      rw [mul_left_comm, Complex.im_ofReal_mul]
    rw [hDv]
    apply Complex.ofReal_injective
    push_cast
    simp only [hh, hh']
    set w := β * x * IsCMField.complexConj E x' with hw
    have A : ∀ i, 2 * Complex.I * g (φ i β) / N * (((g (φ i x) * conj (g (φ i x'))).im : ℝ) : ℂ) =
        (N : ℂ)⁻¹ * (g (φ i w) + conj (g (φ i w))) := by
      intro i
      have := term_eq ((g : ℂ →+* ℂ).comp (φ i)) β x x' (by rw [hgcomp]; exact hgβ i)
      simp only [hgcomp] at this
      rw [div_eq_mul_inv, mul_comm _ (N : ℂ)⁻¹, _root_.mul_assoc, this]
    have B : ∀ i, 2 * Complex.I * φ i β * (((φ i x * conj (φ i x')).im : ℝ) : ℂ) =
        φ i w + conj (φ i w) := fun i => term_eq (φ i) β x x' (hβi i)
    rw [Finset.sum_congr rfl (fun i _ => A i), Finset.sum_congr rfl (fun i _ => B i),
      ← Finset.mul_sum]
    congr 1
    rw [← sum_embeddings_eq φ hφ w, ← sum_embeddings_map g w, ← map_sum, sum_embeddings_eq φ hφ w,
      map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_add, hgc]
  · intro i
    have key : g (Complex.I * (Real.sqrt d : ℂ)) = Complex.I * (Real.sqrt d : ℂ) := by
      have hsq : (Complex.I * (Real.sqrt d : ℂ)) ^ 2 = -(d : ℂ) := by
        rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        push_cast; ring
      have hio2 : (io δ) ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ, map_neg, map_natCast]
      have hprod : (io δ - Complex.I * (Real.sqrt d : ℂ)) * (io δ + Complex.I * (Real.sqrt d : ℂ)) = 0 := by
        linear_combination hio2 - hsq
      rcases mul_eq_zero.mp hprod with h1 | h1
      · have h5 : Complex.I * (Real.sqrt d : ℂ) = io δ := by linear_combination -h1
        rw [h5, hg]
      · have h5 : Complex.I * (Real.sqrt d : ℂ) = -io δ := by linear_combination h1
        rw [h5, map_neg, hg]
    rw [hh i, hh' i]
    have e2 : 2 * Complex.I * φ i β * (Real.sqrt d : ℂ) = 2 * φ i β * (Complex.I * (Real.sqrt d : ℂ)) := by
      ring
    rw [e2, map_mul, map_mul, key, map_ofNat]
    field_simp
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_lattice_spans_real_space : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), 0 < d → δ ^ 2 = -(d : K) →
    ∀ g : ℂ ≃+* ℂ, (∀ x, g (io x) = io x) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) →
      ∀ (n : ℕ) (e : Fin n ≃ I) (Λ : Submodule ℤ (Fin n → ℂ)) (L : Set E),
        Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ → (∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ g (φ (e j) x)) →
      ∀ (h : I → ℝ) (β : E), (∀ i, (h i : ℂ) = 2 * Complex.I * φ i β) → ∀ N : ℝ, 0 < N →
      ∀ Hm : Matrix (Fin n) (Fin n) ℂ, Hm.IsHermitian →
        (∀ x ∈ L, ∀ x' ∈ L, ((fun j ↦ g (φ (e j) x)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (e j) x'))).im =
          N⁻¹ * ∑ i, h i * (φ i x * starRingEnd ℂ (φ i x')).im) →
        ∃ h' : I → ℝ, Hm = Matrix.diagonal (fun j ↦ (h' (e j) : ℂ)) ∧
          ∀ i, g ((h i : ℂ) * (Real.sqrt d : ℝ)) = (N : ℂ) * ((h' i : ℂ) * (Real.sqrt d : ℝ)) := by
  atlas_forward_decl GlobalTheory.HermDiagCM.diagonal_of_conj_form
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.ConjHerm

theorem exists_conj_herm : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
        X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
        ∀ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)), (∀ w, w ∈ u'.Λ ↔ ∃ x ∈ lattice c (y * (upIdele K E t)⁻¹), w = fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) →
          (∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
            v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
              u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') →
          (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) →
          ∃ (u'' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E))) (h' : I → ℝ), u''.ex = u'.ex ∧
            (∃ χ, u''.IsAH (Matrix.diagonal fun j ↦ (h' (T.U.e j) : ℂ)) χ) ∧
            ∀ i, g ((T.U.h i : ℂ) * (Real.sqrt d : ℝ)) = ((modF t : ℝ) : ℂ) * ((h' i : ℂ) * (Real.sqrt d : ℝ)) := by
  intro hPC hADR hADC K _ _ d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E _ _ _ _ I _ φ hφ hres c y hc 𝔠 T X' p hp u' hΛ hdiff hex
  obtain ⟨u₀, Hm, χ, hex₀, hAH⟩ := GlobalTheory.RealMult.Obj.exists_isAH_diag (FR E) 𝔠 X' T.U.c T.U.pos u'
  obtain ⟨β, hβ⟩ := GlobalTheory.T.cm_point_hodge_period_formula E I φ hφ c y hc 𝔠 T
  have hE := GlobalTheory.T.torsion_transport_cm_period hPC hADR hADC K d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E I φ hφ hres c y hc 𝔠 T X' p hp u' hΛ hdiff hex
    u₀ Hm χ hex₀ hAH
  have hmem : ∀ w, w ∈ u₀.Λ ↔ ∃ x ∈ lattice c (y * (upIdele K E t)⁻¹), w = fun j ↦ g (φ (T.U.e j) x) := by
    intro w
    rw [← u₀.ker, hex₀, u'.ker, hΛ]
    simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]
  have hN : 0 < modF t := by
    unfold modF
    refine finprod_induction (fun x => 0 < x) one_pos (fun _ _ => mul_pos) (fun v => ?_)
    have : (0:ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by
      exact_mod_cast Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
    exact zpow_pos this _
  obtain ⟨h', hHm, hid⟩ := GlobalTheory.T.cm_lattice_spans_real_space K d δ io hd hδ g hT.2.2.1 E I φ hφ hres _ T.U.e u₀.Λ _ u₀.full hmem T.U.h β hβ
    (modF t) hN Hm hAH.1 hE
  exact ⟨u₀, h', hex₀, ⟨χ, hHm ▸ hAH⟩, hid⟩

end GlobalTheory.ConjHerm
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_transport_cm_conjugation : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
        X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
        ∀ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)), (∀ w, w ∈ u'.Λ ↔ ∃ x ∈ lattice c (y * (upIdele K E t)⁻¹), w = fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) →
          (∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
            v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
              u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') →
          (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) →
          ∃ (u'' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E))) (h' : I → ℝ), u''.ex = u'.ex ∧
            (∃ χ, u''.IsAH (Matrix.diagonal fun j ↦ (h' (T.U.e j) : ℂ)) χ) ∧
            ∀ i, g ((T.U.h i : ℂ) * (Real.sqrt d : ℝ)) = ((modF t : ℝ) : ℂ) * ((h' i : ℂ) * (Real.sqrt d : ℝ)) := by
  atlas_forward_decl GlobalTheory.ConjHerm.exists_conj_herm
end
