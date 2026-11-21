import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenFormEqFiniteSumAutRepEigenFormsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantZmodLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicFormWeightLevelSmoothAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteBasisAlgebraicForms
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupCharacterKernel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicModularFormMulArchInvariantStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAutomorphicOfWeightOfNonzeroFixedFinPartForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSupercuspidalTypeCharacterZmodPow

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong

namespace GlobalTheory.Cong

theorem eigen_small_sub_finite_approx : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (V X J I : Type) [AddCommGroup V] [Module ℂ V] [Fintype I] (T : J → Module.End ℂ V) (ev : X → V →ₗ[ℂ] ℂ), (∀ (v : V) (R : ℝ), (∀ x, ‖ι.symm (ev x v)‖ ≤ R) → ∀ j x, ‖ι.symm (ev x (T j v))‖ ≤ R) → ∀ (v₀ : V) (θ : J → ℂ) (x₀ : X), (∀ j, T j v₀ = θ j • v₀) → ‖ι.symm (ev x₀ v₀)‖ = 1 → ∀ (v : I → V) (η : I → J → ℂ), (∀ i j, T j (v i) = η i j • v i) → ∀ ε : ℝ, (∀ x, ‖ι.symm (ev x (v₀ + ∑ i, v i))‖ ≤ ε) → ∃ (s : Finset (J → Qbar l)) (c : (J → Qbar l) → Qbar l), (∀ z ∈ s, ∃ i, z = fun j => ι.symm (η i j)) ∧ ∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval (fun j => ι.symm (θ j)) P - ∑ z ∈ s, c z * MvPolynomial.aeval z P‖ ≤ ε := by
  intro l _ ι V X J I _ _ _ T ev hT v₀ θ x₀ hθ hx₀ v η hη ε hε
  classical
  have hmap : ∀ (w : J → ℂ) (P : MvPolynomial J ℤ),
      ι.symm (MvPolynomial.aeval w P) = MvPolynomial.aeval (fun j => ι.symm (w j)) P := by
    intro w P
    induction P using MvPolynomial.induction_on with
    | C n => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p j hp => simp [hp]
  let u : MvPolynomial J ℤ → V := fun P =>
    MvPolynomial.aeval θ P • v₀ + ∑ i, MvPolynomial.aeval (η i) P • v i
  have good : ∀ P, ∀ x, ‖ι.symm (ev x (u P))‖ ≤ ε := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C n =>
      intro x
      have e : u (MvPolynomial.C n) = (n : ℂ) • (v₀ + ∑ i, v i) := by
        simp [u, smul_add, Finset.smul_sum]
      rw [e, map_smul, smul_eq_mul, map_mul, norm_mul, map_intCast]
      have h1 : ‖((n : ℤ) : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one (PadicAlgCl l) n
      have h2 := hε x
      have h3 := norm_nonneg (ι.symm (ev x (v₀ + ∑ i, v i)))
      nlinarith
    | add p q hp hq =>
      intro x
      have e : u (p + q) = u p + u q := by
        simp only [u, map_add, add_smul, Finset.sum_add_distrib]; abel
      rw [e, map_add, map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hp x) (hq x))
    | mul_X p j hp =>
      intro x
      have e : u (p * MvPolynomial.X j) = T j (u p) := by
        simp only [u, map_add, map_sum, map_smul, hθ, hη, map_mul, MvPolynomial.aeval_X, smul_smul]
      rw [e]
      exact hT (u p) ε hp j x
  have hb0 : ι.symm (ev x₀ v₀) ≠ 0 := by
    intro h; rw [h, norm_zero] at hx₀; exact zero_ne_one hx₀
  refine ⟨Finset.univ.image (fun i => fun j => ι.symm (η i j)),
    fun z => - ∑ i ∈ Finset.univ.filter (fun i => (fun j => ι.symm (η i j)) = z),
      ι.symm (ev x₀ (v i)) / ι.symm (ev x₀ v₀), ?_, ?_⟩
  · intro z hz
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
    obtain ⟨i, rfl⟩ := hz
    exact ⟨i, rfl⟩
  · intro P
    have key : ∑ z ∈ Finset.univ.image (fun i => fun j => ι.symm (η i j)),
        (- ∑ i ∈ Finset.univ.filter (fun i => (fun j => ι.symm (η i j)) = z),
          ι.symm (ev x₀ (v i)) / ι.symm (ev x₀ v₀)) * MvPolynomial.aeval z P
        = - ∑ i, ι.symm (ev x₀ (v i)) / ι.symm (ev x₀ v₀) *
            MvPolynomial.aeval (fun j => ι.symm (η i j)) P := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun i => fun j => ι.symm (η i j))
        (t := Finset.univ.image (fun i => fun j => ι.symm (η i j)))
        (fun i hi => Finset.mem_image_of_mem _ hi), ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [neg_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [hi]
    have hexp : ι.symm (ev x₀ (u P)) =
        (MvPolynomial.aeval (fun j => ι.symm (θ j)) P + ∑ i, ι.symm (ev x₀ (v i)) / ι.symm (ev x₀ v₀) *
            MvPolynomial.aeval (fun j => ι.symm (η i j)) P) * ι.symm (ev x₀ v₀) := by
      simp only [u, map_add, map_sum, map_smul, smul_eq_mul, map_mul, hmap, add_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [key, sub_neg_eq_add]
    have h := good P x₀
    rw [hexp, norm_mul, hx₀, mul_one] at h
    exact h

end GlobalTheory.Cong
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenvector_small_sub_finite_eigen_approx_inequality : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (V X J I : Type) [AddCommGroup V] [Module ℂ V] [Fintype I] (T : J → Module.End ℂ V) (ev : X → V →ₗ[ℂ] ℂ), (∀ (v : V) (R : ℝ), (∀ x, ‖ι.symm (ev x v)‖ ≤ R) → ∀ j x, ‖ι.symm (ev x (T j v))‖ ≤ R) → ∀ (v₀ : V) (θ : J → ℂ) (x₀ : X), (∀ j, T j v₀ = θ j • v₀) → ‖ι.symm (ev x₀ v₀)‖ = 1 → ∀ (v : I → V) (η : I → J → ℂ), (∀ i j, T j (v i) = η i j • v i) → ∀ ε : ℝ, (∀ x, ‖ι.symm (ev x (v₀ + ∑ i, v i))‖ ≤ ε) → ∃ (s : Finset (J → Qbar l)) (c : (J → Qbar l) → Qbar l), (∀ z ∈ s, ∃ i, z = fun j => ι.symm (η i j)) ∧ ∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval (fun j => ι.symm (θ j)) P - ∑ z ∈ s, c z * MvPolynomial.aeval z P‖ ≤ ε := by
  first | (exact @GlobalTheory.Cong.eigen_small_sub_finite_approx) | (exact GlobalTheory.Cong.eigen_small_sub_finite_approx) | (intros; apply GlobalTheory.Cong.eigen_small_sub_finite_approx  <;> assumption)
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAutomorphicOfWeight_of_nonzero_fixed_finPart_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (W : Wt E n) (K : Subgroup (UA E n)) (f : algForms W), f ∈ π.finPart W → f ≠ 0 → (∀ k ∈ K, ∀ v g, f.1 v (g * k) = f.1 v g) → OfType (fun τ => W.at τ) K π.V := by
  first | (exact @GlobalTheory.Cong.ofType_of_finPart_fixed) | (exact GlobalTheory.Cong.ofType_of_finPart_fixed) | (intros; apply GlobalTheory.Cong.ofType_of_finPart_fixed  <;> assumption)
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.PRep

noncomputable section

namespace GlobalTheory.CongSc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def zchar {N : ℕ} [NeZero N] (ζ : ℂˣ) (hζ : ζ ^ N = 1) : Multiplicative (ZMod N) →* ℂˣ where
  toFun x := ζ ^ (Multiplicative.toAdd x).val
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul]
    rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hζ]

theorem zchar_apply {N : ℕ} [NeZero N] (ζ : ℂˣ) (hζ : ζ ^ N = 1) (x : Multiplicative (ZMod N)) :
    zchar ζ hζ x = ζ ^ (Multiplicative.toAdd x).val := rfl

theorem sum_roots {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (k : ℕ) (hk : k < N) :
    ∑ i : Fin N, (ζ ^ (i : ℕ)) ^ k = if k = 0 then (N : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (ζ ^ i) ^ k)]
  simp_rw [← pow_mul, mul_comm _ k, pow_mul]
  split_ifs with h
  · subst h; simp
  · have hne : ζ ^ k ≠ 1 := fun e => h (Nat.eq_zero_of_dvd_of_lt ((hζ.pow_eq_one_iff_dvd k).1 e) hk)
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div]

def stab (W : Wt E n) (f : algForms W) : Subgroup (UA E n) where
  carrier := {x | ∀ v g, f.1 v (g * x) = f.1 v g}
  mul_mem' {x y} hx hy v g := by rw [← mul_assoc, hy, hx]
  one_mem' v g := by rw [mul_one]
  inv_mem' {x} hx v g := by
    have := hx v (g * x⁻¹)
    rw [inv_mul_cancel_right] at this
    exact this.symm

theorem stab_level (W : Wt E n) (f : algForms W) (C : Subgroup (UA E n)) (hC : C ≤ finU E n)
    (hc : IsCompact (C : Set (UA E n))) (ho : ∃ N : Set (UA E n), IsOpen N ∧ 1 ∈ N ∧ N ∩ finU E n ⊆ C) :
    IsCompact ((C ⊓ stab W f : Subgroup (UA E n)) : Set (UA E n)) ∧
      ∃ N : Set (UA E n), IsOpen N ∧ 1 ∈ N ∧ N ∩ finU E n ⊆ (C ⊓ stab W f : Subgroup (UA E n)) := by
  obtain ⟨N₁, hN₁, h1, hN₁C⟩ := ho
  have hsm := isSmooth_algRep W f
  obtain ⟨t, ht, hte⟩ := isOpen_induced_iff.1 hsm
  have hfix : ∀ x (hx : x ∈ finU E n), x ∈ t → x ∈ stab W f := by
    intro x hx hxt v g
    have : (⟨x, hx⟩ : finU E n) ∈ {k : finU E n | algRep W k f = f} := by rw [← hte]; exact hxt
    exact congrArg (fun F : algForms W => F.1 v g) this
  have h1t : (1 : UA E n) ∈ t := by
    have : (1 : finU E n) ∈ {k : finU E n | algRep W k f = f} := by simp
    rw [← hte] at this; exact this
  have hN : N₁ ∩ t ∩ finU E n ⊆ (C ⊓ stab W f : Subgroup (UA E n)) := fun x ⟨⟨hx1, hxt⟩, hxf⟩ =>
    ⟨hN₁C ⟨hx1, hxf⟩, hfix x hxf hxt⟩
  refine ⟨?_, N₁ ∩ t, hN₁.inter ht, ⟨h1, h1t⟩, hN⟩
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hc
  have hHo : IsOpen (((C ⊓ stab W f).subgroupOf C : Subgroup C) : Set C) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
      (((hN₁.inter ht).preimage continuous_subtype_val).mem_nhds ⟨h1, h1t⟩) ?_)
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (hN ⟨hx, hC x.2⟩)
  have hHc := Subtype.isCompact_iff.1 (Subgroup.isClosed_of_isOpen _ hHo).isCompact
  convert hHc using 1
  ext x; constructor
  · intro hx; exact ⟨⟨x, hx.1⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact Subgroup.mem_subgroupOf.1 hy

def opL (s : UA E n →₀ ℂ) : Module.End ℂ (UA E n → ℂ) where
  toFun := opOf (RU E n) s
  map_add' φ ψ := by simp [opOf, Finsupp.sum, Finset.sum_add_distrib, smul_add]
  map_smul' c φ := by simp [opOf, Finsupp.sum, Finset.smul_sum, smul_comm c]

end GlobalTheory.CongSc

namespace GlobalTheory.CongSc

end GlobalTheory.CongSc
end
end
