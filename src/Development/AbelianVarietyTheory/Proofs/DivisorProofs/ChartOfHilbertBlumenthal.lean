import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealMultiplicationUniformization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIndependentBasisCoprime
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointDefinedOverBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.FiniteLocalLifts.SmLift

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_real_multiplication_uniformization : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)), ∃ (L : LB X.A.left) (u : HolUnif X.A L (Module.finrank ℚ F)) (Fa : 𝓞 F →+* Module.End ℂ (Fin (Module.finrank ℚ F) → ℂ)), ∀ (a : 𝓞 F) (z : Fin (Module.finrank ℚ F) → ℂ), u.ex (Fa a z) = u.ex z ≫ X.rm.act a := by
  first | exact @GlobalTheory.RealMult.Obj.exists_holUnif_ringHom_lift | exact GlobalTheory.RealMult.Obj.exists_holUnif_ringHom_lift | (intros; apply GlobalTheory.RealMult.Obj.exists_holUnif_ringHom_lift <;> assumption)
end

section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_independent_basis_coprime : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] [Module.Finite ℤ M] [IsAddTorsionFree M] (N : ℕ), 2 ≤ N → ∃ (r : ℕ) (x : Fin r → M), LinearIndependent (𝓞 F) x ∧ ∃ c : 𝓞 F, c ≠ 0 ∧ IsCoprime c (N : 𝓞 F) ∧ ∀ m : M, c • m ∈ Submodule.span (𝓞 F) (Set.range x) := by
  first | exact @GlobalTheory.CoprimeBasis.exists_coprime_basis | exact GlobalTheory.CoprimeBasis.exists_coprime_basis | (intros; apply GlobalTheory.CoprimeBasis.exists_coprime_basis <;> assumption)
end

section
section
open NumberField

namespace GlobalTheory

theorem smul_eq_zero_of_ringOfIntegers {F : Type} [Field F] [NumberField F] {M : Type}
    [AddCommGroup M] [Module (𝓞 F) M] [IsAddTorsionFree M] {a : 𝓞 F} (ha : a ≠ 0) {m : M}
    (h : a • m = 0) : m = 0 := by
  have hmem := Ideal.absNorm_mem (Ideal.span {a})
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨b, hb⟩ := hmem
  have hn : Ideal.absNorm (Ideal.span {a}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact ha
  have h2 : (Ideal.absNorm (Ideal.span {a})) • m = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 F), hb, mul_comm, mul_smul, h, smul_zero]
  exact nsmul_right_injective hn (by simpa using h2)

theorem finrank_int_eq_of_span_smul (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M]
    [Module (𝓞 F) M] [Module.Finite ℤ M] [IsAddTorsionFree M] (r : ℕ) (x : Fin r → M)
    (hx : LinearIndependent (𝓞 F) x) (c : 𝓞 F) (hc : c ≠ 0)
    (hspan : ∀ m : M, c • m ∈ Submodule.span (𝓞 F) (Set.range x)) :
    Module.finrank ℤ M = r * Module.finrank ℚ F := by
  let φ : (Fin r → 𝓞 F) →ₗ[ℤ] M := (Fintype.linearCombination (𝓞 F) x).restrictScalars ℤ
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    funext i
    exact Fintype.linearIndependent_iff.mp hx g (by simpa [φ, Fintype.linearCombination_apply] using hg) i
  have hdom : Module.finrank ℤ (Fin r → 𝓞 F) = r * Module.finrank ℚ F := by
    rw [Module.finrank_pi_fintype]
    simp [RingOfIntegers.rank]
  let ψ : M →ₗ[ℤ] M := (LinearMap.lsmul (𝓞 F) M c).restrictScalars ℤ
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    exact smul_eq_zero_of_ringOfIntegers hc (by simpa [ψ] using hm)
  have hrange : ∀ m, ψ m ∈ LinearMap.range φ := by
    intro m
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 F)).mp (hspan m)
    exact ⟨g, by simpa [φ, ψ, Fintype.linearCombination_apply] using hg⟩
  let ψ' : M →ₗ[ℤ] LinearMap.range φ := ψ.codRestrict _ hrange
  have hψ' : Function.Injective ψ' := by
    intro a b hab
    apply hψ
    simpa [ψ'] using congrArg Subtype.val hab
  have h1 : Module.finrank ℤ (Fin r → 𝓞 F) ≤ Module.finrank ℤ M :=
    LinearMap.finrank_le_finrank_of_injective hφ
  have hfin : Module.Finite ℤ (LinearMap.range φ) := inferInstance
  have h2 : Module.finrank ℤ M ≤ Module.finrank ℤ (LinearMap.range φ) :=
    LinearMap.finrank_le_finrank_of_injective hψ'
  rw [LinearMap.finrank_range_of_inj hφ] at h2
  omega

end GlobalTheory
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_eq_rank_mul_degree : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] [Module.Finite ℤ M] [IsAddTorsionFree M] (r : ℕ) (x : Fin r → M), LinearIndependent (𝓞 F) x → ∀ c : 𝓞 F, c ≠ 0 → (∀ m : M, c • m ∈ Submodule.span (𝓞 F) (Set.range x)) → Module.finrank ℤ M = r * Module.finrank ℚ F := by
  atlas_forward_decl GlobalTheory.finrank_int_eq_of_span_smul
end

section
section
open NumberField

namespace GlobalTheory.LatticeModN

theorem exists_gen_modN : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] [Module.Finite ℤ M] [IsAddTorsionFree M], Module.finrank ℤ M = 2 * Module.finrank ℚ F → ∀ N : ℕ, 1 ≤ N → ∃ x : Fin 2 → M, (∀ m : M, ∃ (a b : 𝓞 F) (m' : M), m = a • x 0 + b • x 1 + N • m') ∧ ∀ a b : 𝓞 F, (∃ m' : M, a • x 0 + b • x 1 = N • m') → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b := by
  intro F _ _ M _ _ _ _ hrk N hN
  rcases Nat.lt_or_ge N 2 with h1 | h2
  · obtain rfl : N = 1 := by omega
    refine ⟨0, fun m => ⟨0, 0, m, by simp⟩, fun a b _ => ⟨by simp, by simp⟩⟩
  obtain ⟨r, x, hli, c, hc0, hcop, hspan⟩ := GlobalTheory.T.exists_independent_basis_coprime F M N h2
  have hr := GlobalTheory.T.finrank_eq_rank_mul_degree F M r x hli c hc0 hspan
  have hf : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hr2 : r = 2 := by
    rw [hrk] at hr
    exact (Nat.eq_of_mul_eq_mul_right hf hr).symm
  subst hr2
  obtain ⟨u, v, huv⟩ := hcop
  have hNs : ∀ y : M, (N : 𝓞 F) • y = N • y := fun y => Nat.cast_smul_eq_nsmul (𝓞 F) N y
  refine ⟨x, fun m => ?_, fun a b ⟨m', hm'⟩ => ?_⟩
  · obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 F)).1 (hspan m)
    rw [Fin.sum_univ_two] at hg
    refine ⟨u * g 0, u * g 1, v • m, ?_⟩
    calc m = (1 : 𝓞 F) • m := (one_smul _ _).symm
      _ = u • (c • m) + (N : 𝓞 F) • (v • m) := by rw [← huv, add_smul, mul_smul, mul_comm v, mul_smul]
      _ = _ := by rw [← hg, hNs, smul_add, mul_smul, mul_smul]
  · obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 F)).1 (hspan m')
    rw [Fin.sum_univ_two] at hg
    have key : (c * a - N * g 0) • x 0 + (c * b - N * g 1) • x 1 = 0 := by
      have e1 : c • (a • x 0 + b • x 1) = (N : 𝓞 F) • (c • m') := by
        rw [hm', ← hNs, smul_comm]
      rw [← hg, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul] at e1
      rw [sub_smul, sub_smul]
      linear_combination (norm := module) e1
    have hz := Fintype.linearIndependent_iff.1 hli ![c * a - N * g 0, c * b - N * g 1]
      (by simpa [Fin.sum_univ_two] using key)
    have ha : c * a = N * g 0 := sub_eq_zero.1 (hz 0)
    have hb : c * b = N * g 1 := sub_eq_zero.1 (hz 1)
    refine ⟨⟨u * g 0 + v * a, ?_⟩, ⟨u * g 1 + v * b, ?_⟩⟩
    · calc a = (u * c + v * N) * a := by rw [huv, one_mul]
        _ = u * (c * a) + N * (v * a) := by ring
        _ = _ := by rw [ha]; ring
    · calc b = (u * c + v * N) * b := by rw [huv, one_mul]
        _ = u * (c * b) + N * (v * b) := by ring
        _ = _ := by rw [hb]; ring

end GlobalTheory.LatticeModN
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rank_two_basis_mod_N : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] [Module.Finite ℤ M] [IsAddTorsionFree M], Module.finrank ℤ M = 2 * Module.finrank ℚ F → ∀ N : ℕ, 1 ≤ N → ∃ x : Fin 2 → M, (∀ m : M, ∃ (a b : 𝓞 F) (m' : M), m = a • x 0 + b • x 1 + N • m') ∧ ∀ a b : 𝓞 F, (∃ m' : M, a • x 0 + b • x 1 = N • m') → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b := by
  atlas_forward_decl GlobalTheory.LatticeModN.exists_gen_modN
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionPoints

theorem exists_torsion_basis : ∀ (F : Type) [Field F] [NumberField F] (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A]
    (rm : OAct (𝓞 F) A) (L : LB A.left) (u : HolUnif A L (Module.finrank ℚ F))
    (Fa : 𝓞 F →+* Module.End ℂ (Fin (Module.finrank ℚ F) → ℂ)),
    (∀ (a : 𝓞 F) (z : Fin (Module.finrank ℚ F) → ℂ), u.ex (Fa a z) = u.ex z ≫ rm.act a) →
    ∀ N : ℕ, 1 ≤ N → ∃ pt : Fin 2 → (𝟙_ (Over (Sp ℂ)) ⟶ A), (∀ i, pt i ^ N = 1) ∧
      (∀ a b : 𝓞 F, (pt 0 ≫ rm.act a) * (pt 1 ≫ rm.act b) = 1 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b) ∧
      ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ A, y ^ N = 1 → ∃ a b : 𝓞 F, y = (pt 0 ≫ rm.act a) * (pt 1 ≫ rm.act b) := by
  intro F _ _ A _ _ rm L u Fa hFa N hN
  have hst : ∀ (a : 𝓞 F) (l : Fin (Module.finrank ℚ F) → ℂ), l ∈ u.Λ → Fa a l ∈ u.Λ := by
    intro a l hl
    rw [← u.ker, hFa, (u.ker l).2 hl, Hom.one_def, Category.assoc, (rm.hom a).one_hom]
  letI : Module (𝓞 F) (Fin (Module.finrank ℚ F) → ℂ) := Module.compHom _ Fa
  have hsmul : ∀ (a : 𝓞 F) (v : Fin (Module.finrank ℚ F) → ℂ), a • v = Fa a v := fun _ _ => rfl
  let Λ' : Submodule (𝓞 F) (Fin (Module.finrank ℚ F) → ℂ) :=
    { carrier := u.Λ
      add_mem' := fun ha hb => u.Λ.add_mem ha hb
      zero_mem' := u.Λ.zero_mem
      smul_mem' := fun a l hl => hst a l hl }
  let e : u.Λ ≃+ Λ' :=
    { toFun := fun l => ⟨l.1, l.2⟩, invFun := fun l => ⟨l.1, l.2⟩, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_add' := fun _ _ => rfl }
  haveI := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  haveI : Module.Finite ℤ u.Λ := ZLattice.module_finite ℝ u.Λ
  haveI : Module.Finite ℤ Λ' := Module.Finite.equiv e.toIntLinearEquiv
  haveI : IsAddTorsionFree Λ' := ⟨fun n hn a b h => by
    apply Subtype.ext
    have h' : n • (a : Fin (Module.finrank ℚ F) → ℂ) = n • (b : Fin (Module.finrank ℚ F) → ℂ) := by
      simpa using congrArg Subtype.val h
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ n] at h'
    exact smul_right_injective _ (Nat.cast_ne_zero.2 hn) h'⟩
  have hrank : Module.finrank ℤ Λ' = 2 * Module.finrank ℚ F := by
    rw [← e.toIntLinearEquiv.finrank_eq, ZLattice.rank ℝ u.Λ]
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  obtain ⟨x, hgen, hfree⟩ := GlobalTheory.T.exists_rank_two_basis_mod_N F Λ' hrank N hN
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hpow : ∀ (z : Fin (Module.finrank ℚ F) → ℂ) (k : ℕ), u.ex (k • z) = u.ex z ^ k := by
    intro z k
    induction k with
    | zero => rw [zero_smul, pow_zero]; exact (u.ker 0).2 u.Λ.zero_mem
    | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]
  have hcancel : ∀ v : Fin (Module.finrank ℚ F) → ℂ, N • ((N : ℂ)⁻¹ • v) = v := by
    intro v
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
  have key : ∀ a b : 𝓞 F, (u.ex ((N : ℂ)⁻¹ • (x 0 : Fin (Module.finrank ℚ F) → ℂ)) ≫ rm.act a) *
      (u.ex ((N : ℂ)⁻¹ • (x 1 : Fin (Module.finrank ℚ F) → ℂ)) ≫ rm.act b) =
      u.ex ((N : ℂ)⁻¹ • ((a • x 0 + b • x 1 : Λ') : Fin (Module.finrank ℚ F) → ℂ)) := by
    intro a b
    rw [← hFa, ← hFa, ← u.ex_add, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, hsmul, hsmul,
      smul_add, map_smul, map_smul]
  refine ⟨fun i => u.ex ((N : ℂ)⁻¹ • (x i : Fin (Module.finrank ℚ F) → ℂ)), ?_, ?_, ?_⟩
  · intro i
    rw [← hpow, hcancel]
    exact (u.ker _).2 (x i).2
  · intro a b h
    rw [key] at h
    refine hfree a b ⟨⟨_, (u.ker _).1 h⟩, Subtype.ext ?_⟩
    exact (hcancel _).symm
  · intro y hy
    obtain ⟨z, rfl⟩ := u.ex_onto y
    have hz : N • z ∈ u.Λ := (u.ker _).1 (by rw [hpow]; exact hy)
    obtain ⟨a, b, m', hm⟩ := hgen ⟨N • z, hz⟩
    refine ⟨a, b, ?_⟩
    rw [key]
    have hm' : N • z = ((a • x 0 + b • x 1 : Λ') : Fin (Module.finrank ℚ F) → ℂ) + N • (m' : Fin (Module.finrank ℚ F) → ℂ) := by
      simpa using congrArg Subtype.val hm
    have hz' : z = (N : ℂ)⁻¹ • ((a • x 0 + b • x 1 : Λ') : Fin (Module.finrank ℚ F) → ℂ) + (m' : Fin (Module.finrank ℚ F) → ℂ) := by
      have h1 : z = (N : ℂ)⁻¹ • (N • z) := by
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN0, one_smul]
      rw [h1, hm', smul_add, ← Nat.cast_smul_eq_nsmul ℂ N (m' : Fin (Module.finrank ℚ F) → ℂ), smul_smul,
        inv_mul_cancel₀ hN0, one_smul]
    conv_lhs => rw [hz']
    rw [u.ex_add, (u.ker _).2 m'.2, _root_.mul_one]

end GlobalTheory.TorsionPoints
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_basis_real_multiplication : ∀ (F : Type) [Field F] [NumberField F] (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (rm : OAct (𝓞 F) A) (L : LB A.left) (u : HolUnif A L (Module.finrank ℚ F)) (Fa : 𝓞 F →+* Module.End ℂ (Fin (Module.finrank ℚ F) → ℂ)), (∀ (a : 𝓞 F) (z : Fin (Module.finrank ℚ F) → ℂ), u.ex (Fa a z) = u.ex z ≫ rm.act a) → ∀ N : ℕ, 1 ≤ N → ∃ pt : Fin 2 → (𝟙_ (Over (Sp ℂ)) ⟶ A), (∀ i, pt i ^ N = 1) ∧ (∀ a b : 𝓞 F, (pt 0 ≫ rm.act a) * (pt 1 ≫ rm.act b) = 1 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b) ∧ ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ A, y ^ N = 1 → ∃ a b : 𝓞 F, y = (pt 0 ≫ rm.act a) * (pt 1 ≫ rm.act b) := by
  atlas_forward_decl GlobalTheory.TorsionPoints.exists_torsion_basis
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_point_defined_over_base : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (N : ℕ), 1 ≤ N → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp ℂ) (y : Over.mk t ⟶ X.A), y ^ N = 1 → ∃ z : 𝟙_ (Over (Sp ℂ)) ⟶ X.A, y = toUnit (Over.mk t) ≫ z := by
  first | exact @GlobalTheory.RealMult.torsion_descends_to_complex | exact GlobalTheory.RealMult.torsion_descends_to_complex | (intros; apply GlobalTheory.RealMult.torsion_descends_to_complex <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.Obj

theorem toUnit_comp_injective {Ω : Type} [Field Ω] (t : Sp Ω ⟶ Sp ℂ) {A : Over (Sp ℂ)}
    {z z' : 𝟙_ (Over (Sp ℂ)) ⟶ A} (h : toUnit (Over.mk t) ≫ z = toUnit (Over.mk t) ≫ z') : z = z' := by
  obtain ⟨_, _⟩ := GlobalTheory.PolIsoDescent.flat_surjective t
  have : Epi t := Flat.epi_of_flat_of_surjective _
  have e : (toUnit (Over.mk t)).left = t := by
    have := Over.w (toUnit (Over.mk t))
    simpa using this
  apply Over.OverMorphism.ext
  apply (cancel_epi t).1
  have := congrArg CommaMorphism.left h
  simpa [e] using this

theorem exists_torsion_basis (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (N : ℕ)
    (hN : 1 ≤ N) :
    ∃ pt : Fin 2 → (𝟙_ (Over (Sp ℂ)) ⟶ X.A), (∀ i, pt i ^ N = 1) ∧
      (∀ a b : 𝓞 F, (pt 0 ≫ X.rm.act a) * (pt 1 ≫ X.rm.act b) = 1 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b) ∧
      ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ X.A, y ^ N = 1 → ∃ a b : 𝓞 F, y = (pt 0 ≫ X.rm.act a) * (pt 1 ≫ X.rm.act b) := by
  obtain ⟨L, u, Fa, h⟩ := GlobalTheory.T.exists_real_multiplication_uniformization F 𝔠 X
  exact GlobalTheory.T.exists_torsion_basis_real_multiplication F X.A X.rm L u Fa h N hN

theorem nonempty_level_complex : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ),
    1 ≤ N → ∀ X : Obj F 𝔠 (Sp ℂ), Nonempty (X.Level N) := by
  intro F _ _ _ 𝔠 N hN X
  obtain ⟨pt, htor, hinj, hsurj⟩ := exists_torsion_basis F 𝔠 X N hN
  refine ⟨{ pt := pt, tors := htor, inj := ?_, surj := ?_ }⟩
  · intro Ω _ _ t a b h
    apply hinj a b
    apply toUnit_comp_injective t
    rw [MonObj.comp_mul, MonObj.comp_one, ← Category.assoc, ← Category.assoc]
    exact h
  · intro Ω _ _ t y hy
    obtain ⟨z, rfl⟩ := GlobalTheory.T.torsion_point_defined_over_base F 𝔠 X N hN Ω t y hy
    have hz : z ^ N = 1 := by
      apply toUnit_comp_injective t
      rw [MonObj.comp_pow, hy, MonObj.comp_one]
    obtain ⟨a, b, rfl⟩ := hsurj z hz
    exact ⟨a, b, by rw [MonObj.comp_mul]⟩

end GlobalTheory.RealMult.Obj
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_level_structure_complex : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 1 ≤ N →
    ∀ X : Obj F 𝔠 (Sp ℂ), Nonempty (X.Level N) := by
  atlas_forward_decl GlobalTheory.RealMult.Obj.nonempty_level_complex
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem TorsionLift.pushPt_pow {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G') :
    ∀ n : ℕ, pushPt h.1.w (x ^ n) = (pushPt h.1.w x) ^ n := by
  have h1 : pushPt h.1.w (1 : T ⟶ G') = 1 := by
    have e := h.2 T 1 1 (pushPt h.1.w 1) (pushPt h.1.w 1) rfl rfl
    have e' : pushPt h.1.w (1 : T ⟶ G') * pushPt h.1.w 1 = pushPt h.1.w 1 :=
      Over.OverMorphism.ext (by rw [e, _root_.mul_one]; rfl)
    exact mul_eq_left.1 e'
  intro n
  induction n with
  | zero => rw [pow_zero, pow_zero, h1]
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih]
    exact (Over.OverMorphism.ext (h.2 T (x ^ n) x (pushPt h.1.w (x ^ n)) (pushPt h.1.w x) rfl rfl)).symm

theorem TorsionLift.exists_torsion_lift : ∀ {R : Type} [CommRing R] [Algebra ℂ R] (π : R →ₐ[ℂ] ℂ), (∀ x ∈ RingHom.ker π, IsNilpotent x) →
    ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (G₀ : Over (Sp ℂ)) [GrpObj G₀] (i : G₀.left ⟶ G.left), IsGrpPullback G₀ G (spMap (π : R →+* ℂ)) i →
    ∀ (N : ℕ), 1 ≤ N → ∀ (p : 𝟙_ (Over (Sp ℂ)) ⟶ G₀), p ^ N = 1 →
    ∃ q : 𝟙_ (Over (Sp R)) ⟶ G, q ^ N = 1 ∧ p.left ≫ i = spMap (π : R →+* ℂ) ≫ q.left := by
  intro R _ _ π hnil G _ _ _ G₀ _ i hG N hN p hp
  have hn : IsUnit (N : Γ(Sp R, ⊤)) := by
    let f : ℂ →+* Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp (algebraMap ℂ R)
    rw [← map_natCast f N]
    exact (IsUnit.mk0 (N : ℂ) (by exact_mod_cast (show N ≠ 0 by omega))).map f
  have := GrpTangent.etale_torsion G hn
  have hP := GrpTangent.isPullback_torsion G N
  have e : ∀ {T : Scheme.{0}} (q : T ⟶ Sp R), (1 : Over.mk q ⟶ G).left = q ≫ η[G].left := by
    intro T q
    rw [Hom.one_def, Over.comp_left]; rfl
  let y₀ := pushPt hG.1.w p
  have hy₀ : y₀ ^ N = 1 := by
    rw [← TorsionLift.pushPt_pow hG p N, hp]
    have := TorsionLift.pushPt_pow hG (1 : 𝟙_ (Over (Sp ℂ)) ⟶ G₀) 0
    rwa [pow_zero, pow_zero] at this
  have w : y₀.left ≫ (mulN G N).left = (𝟙 (Sp ℂ) ≫ spMap (π : R →+* ℂ)) ≫ η[G].left := by
    rw [← Over.comp_left, GrpTangent.comp_mulN, hy₀, e]
    rfl
  let x₀ : Sp ℂ ⟶ (torsion G N).left := hP.lift y₀.left _ w
  have hx₀₁ : x₀ ≫ (torsion G N).hom = 𝟙 (Sp ℂ) ≫ spMap (π : R →+* ℂ) := hP.lift_snd _ _ w
  have hx₀₂ : x₀ ≫ (torsion.ι G N).left = p.left ≫ i := hP.lift_fst _ _ w
  have hsurj : Function.Surjective π := fun c => ⟨algebraMap ℂ R c, by simp⟩
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ :=
    exists_isAffineOpen_pair (torsion G N).hom (x₀ (IsLocalRing.closedPoint ℂ)) (O := ⊤) trivial
  obtain ⟨x, hx₁, hx₂⟩ := exists_lift_of_smooth_of_isAffineOpen (torsion G N).hom (isAffineOpen_top _) hV
    (fun _ _ => trivial) (CommRingCat.ofHom (π : R →+* ℂ)) (𝟙 _) x₀ (by rw [hx₀₁]; rfl)
    (fun _ _ => trivial) (range_subset_opens_of_isLocalRing x₀ hxV) (by
      intro R' A _ _ _ _ _ _ π' hπ' φ
      have : Algebra.FormallySmooth R' A := inferInstance
      exact ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms.exists_lift_nil π'
        (fun c => (hsurj c).imp fun b hb => (hπ' b).trans hb)
        (fun a ha => hnil a (by rw [RingHom.mem_ker] at ha ⊢; rw [← ha]; exact (hπ' a).symm)) φ)
  let q : 𝟙_ (Over (Sp R)) ⟶ G := Over.homMk (U := 𝟙_ (Over (Sp R))) (x ≫ (torsion.ι G N).left) (by
    rw [Category.assoc, Over.w]; exact hx₂)
  refine ⟨q, ?_, ?_⟩
  · refine Over.OverMorphism.ext ?_
    rw [← GrpTangent.comp_mulN, Over.comp_left, e]
    change (x ≫ (torsion.ι G N).left) ≫ _ = _
    rw [Category.assoc, hP.w, ← Category.assoc, hx₂]
    rfl
  · change _ = _ ≫ x ≫ (torsion.ι G N).left
    rw [← Category.assoc, hx₁, hx₀₂]

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_torsion_point_nilpotent : ∀ {R : Type} [CommRing R] [Algebra ℂ R] (π : R →ₐ[ℂ] ℂ), (∀ x ∈ RingHom.ker π, IsNilpotent x) →
    ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (G₀ : Over (Sp ℂ)) [GrpObj G₀] (i : G₀.left ⟶ G.left), IsGrpPullback G₀ G (spMap (π : R →+* ℂ)) i →
    ∀ (N : ℕ), 1 ≤ N → ∀ (p : 𝟙_ (Over (Sp ℂ)) ⟶ G₀), p ^ N = 1 →
    ∃ q : 𝟙_ (Over (Sp R)) ⟶ G, q ^ N = 1 ∧ p.left ≫ i = spMap (π : R →+* ℂ) ≫ q.left := by
  atlas_forward_decl GlobalTheory.TorsionLift.exists_torsion_lift
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.LevelDescend

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S₀ : Scheme.{0}}
    {X : Obj F 𝔠 S} {X₀ : Obj F 𝔠 S₀} {b : S₀ ⟶ S} {i : X₀.A.left ⟶ X.A.left}

theorem push_injective (h : X₀.IsPullBy X b i) {T : Over S₀} {z z' : T ⟶ X₀.A}
    (e : pushPt h.grp.1.w z = pushPt h.grp.1.w z') : z = z' := by
  have e' : z.left ≫ i = z'.left ≫ i := congrArg (fun f => CommaMorphism.left f) e
  apply Over.OverMorphism.ext
  exact h.grp.1.hom_ext e' (by rw [Over.w z, Over.w z'])

theorem push_surjective (h : X₀.IsPullBy X b i) {T : Over S₀} (y : Over.mk (T.hom ≫ b) ⟶ X.A) :
    ∃ z : T ⟶ X₀.A, pushPt h.grp.1.w z = y := by
  have hy : y.left ≫ X.A.hom = T.hom ≫ b := by simpa using Over.w y
  refine ⟨Over.homMk (h.grp.1.lift y.left T.hom hy) (h.grp.1.lift_snd _ _ _), ?_⟩
  apply Over.OverMorphism.ext
  exact h.grp.1.lift_fst _ _ _

theorem push_mul (h : X₀.IsPullBy X b i) {T : Over S₀} (z z' : T ⟶ X₀.A) :
    pushPt h.grp.1.w (z * z') = pushPt h.grp.1.w z * pushPt h.grp.1.w z' := by
  apply Over.OverMorphism.ext
  exact (h.grp.2 T z z' _ _ rfl rfl).symm

theorem push_one (h : X₀.IsPullBy X b i) (T : Over S₀) :
    pushPt h.grp.1.w (1 : T ⟶ X₀.A) = 1 := by
  have e := push_mul h (1 : T ⟶ X₀.A) 1
  rw [_root_.mul_one] at e
  exact mul_left_cancel (e.symm.trans (_root_.mul_one _).symm)

theorem push_pow (h : X₀.IsPullBy X b i) {T : Over S₀} (z : T ⟶ X₀.A) (n : ℕ) :
    pushPt h.grp.1.w (z ^ n) = pushPt h.grp.1.w z ^ n := by
  induction n with
  | zero => rw [_root_.pow_zero, _root_.pow_zero, push_one h]
  | succ n ih => rw [_root_.pow_succ, _root_.pow_succ, push_mul h, ih]

theorem push_pt_act (h : X₀.IsPullBy X b i) {N : ℕ} (α₀ : X₀.Level N) (q : Fin 2 → (𝟙_ (Over S) ⟶ X.A))
    (hpq : ∀ k, (α₀.pt k).left ≫ i = b ≫ (q k).left) {W : Scheme.{0}} (t₀ : W ⟶ S₀) (k : Fin 2) (a : 𝓞 F) :
    pushPt h.grp.1.w (toUnit (Over.mk t₀) ≫ α₀.pt k ≫ X₀.rm.act a) =
      toUnit (Over.mk (t₀ ≫ b)) ≫ q k ≫ X.rm.act a := by
  apply Over.OverMorphism.ext
  simp only [pushPt, Over.homMk_left, Over.comp_left, Over.toUnit_left, Over.mk_hom, Category.assoc,
    h.act a]
  rw [reassoc_of% (hpq k)]

end GlobalTheory.RealMult.LevelDescend

namespace GlobalTheory.RealMult

open LevelDescend in

theorem level_descend : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S₀ : Scheme.{0}}
    {X : Obj F 𝔠 S} {X₀ : Obj F 𝔠 S₀} {b : S₀ ⟶ S} {i : X₀.A.left ⟶ X.A.left}, X₀.IsPullBy X b i →
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), ∃ t₀ : Sp Ω ⟶ S₀, t₀ ≫ b = t) →
    ∀ {N : ℕ} (α₀ : X₀.Level N) (q : Fin 2 → (𝟙_ (Over S) ⟶ X.A)), (∀ k, q k ^ N = 1) →
    (∀ k, (α₀.pt k).left ≫ i = b ≫ (q k).left) → Nonempty (X.Level N) := by
  intro F _ _ 𝔠 S S₀ X X₀ b i h hfac N α₀ q hq hpq
  refine ⟨{ pt := q, tors := hq, inj := ?_, surj := ?_ }⟩
  · intro Ω _ _ t a c e
    obtain ⟨t₀, rfl⟩ := hfac Ω t
    apply α₀.inj Ω t₀ a c
    apply push_injective h
    rw [push_mul h, push_one h, push_pt_act h α₀ q hpq, push_pt_act h α₀ q hpq]
    exact e
  · intro Ω _ _ t y hy
    obtain ⟨t₀, rfl⟩ := hfac Ω t
    obtain ⟨z, rfl⟩ := push_surjective h (T := Over.mk t₀) y
    have hz : z ^ N = 1 := by
      apply push_injective h
      rw [push_pow h, push_one h]
      exact hy
    obtain ⟨a, c, hac⟩ := α₀.surj Ω t₀ z hz
    refine ⟨a, c, ?_⟩
    rw [hac, push_mul h, push_pt_act h α₀ q hpq, push_pt_act h α₀ q hpq]

end GlobalTheory.RealMult
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_structure_descends : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S₀ : Scheme.{0}}
    {X : Obj F 𝔠 S} {X₀ : Obj F 𝔠 S₀} {b : S₀ ⟶ S} {i : X₀.A.left ⟶ X.A.left}, X₀.IsPullBy X b i →
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), ∃ t₀ : Sp Ω ⟶ S₀, t₀ ≫ b = t) →
    ∀ {N : ℕ} (α₀ : X₀.Level N) (q : Fin 2 → (𝟙_ (Over S) ⟶ X.A)), (∀ k, q k ^ N = 1) →
    (∀ k, (α₀.pt k).left ≫ i = b ≫ (q k).left) → Nonempty (X.Level N) := by
  atlas_forward_decl GlobalTheory.RealMult.level_descend
end

section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.LevelLift

theorem exists_factor_of_nil {R : Type} [CommRing R] [Algebra ℂ R] (π : R →ₐ[ℂ] ℂ)
    (hπ : ∀ x ∈ RingHom.ker π, IsNilpotent x) (Ω : Type) [Field Ω] (t : Sp Ω ⟶ Sp R) :
    ∃ t₀ : Sp Ω ⟶ Sp ℂ, t₀ ≫ spMap (π : R →+* ℂ) = t := by
  obtain ⟨φ, rfl⟩ : ∃ φ : R →+* Ω, spMap φ = t := ⟨(Spec.preimage t).hom, Spec.map_preimage t⟩
  refine ⟨spMap (φ.comp (algebraMap ℂ R)), ?_⟩
  have e : φ = (φ.comp (algebraMap ℂ R)).comp (π : R →+* ℂ) := by
    ext r
    have hk : r - algebraMap ℂ R (π r) ∈ RingHom.ker π := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes]; simp
    obtain ⟨n, hn⟩ := hπ _ hk
    have h0 : φ (r - algebraMap ℂ R (π r)) = 0 := by
      have : φ (r - algebraMap ℂ R (π r)) ^ n = 0 := by rw [← map_pow, hn, map_zero]
      exact pow_eq_zero_iff'.mp this |>.1
    rw [map_sub, sub_eq_zero] at h0
    simpa using h0
  conv_rhs => rw [e]
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem level_lift : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 1 ≤ N →
    ∀ (R : Type) [CommRing R] [Algebra ℂ R] (π : R →ₐ[ℂ] ℂ), (∀ x ∈ RingHom.ker π, IsNilpotent x) →
    ∀ (X' : Obj F 𝔠 (Sp R)) (X₀ : Obj F 𝔠 (Sp ℂ)) (i : X₀.A.left ⟶ X'.A.left),
      X₀.IsPullBy X' (spMap (π : R →+* ℂ)) i → X₀.Level N → Nonempty (X'.Level N) := by
  intro F _ _ _ 𝔠 N hN R _ _ π hπ X' X₀ i h α₀
  have := X'.ab.smooth
  have hy : ∀ k, ∃ q : 𝟙_ (Over (Sp R)) ⟶ X'.A, q ^ N = 1 ∧ (α₀.pt k).left ≫ i = spMap (π : R →+* ℂ) ≫ q.left :=
    fun k => GlobalTheory.T.lift_torsion_point_nilpotent π hπ X'.A X₀.A i h.grp N hN (α₀.pt k) (α₀.tors k)
  choose q hq1 hq2 using hy
  exact GlobalTheory.T.level_structure_descends h (fun Ω _ _ t => exists_factor_of_nil π hπ Ω t) α₀ q hq1 hq2

end GlobalTheory.RealMult.LevelLift
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_structure_lift_nilpotent : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 1 ≤ N →
    ∀ (R : Type) [CommRing R] [Algebra ℂ R] (π : R →ₐ[ℂ] ℂ), (∀ x ∈ RingHom.ker π, IsNilpotent x) →
    ∀ (X' : Obj F 𝔠 (Sp R)) (X₀ : Obj F 𝔠 (Sp ℂ)) (i : X₀.A.left ⟶ X'.A.left),
      X₀.IsPullBy X' (spMap (π : R →+* ℂ)) i → X₀.Level N → Nonempty (X'.Level N) := by
  atlas_forward_decl GlobalTheory.RealMult.LevelLift.level_lift
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

open scoped TensorProduct

namespace GlobalTheory.AffChartSmooth

theorem mem_of_closedPoint_mem {R : Type} [CommRing R] [IsLocalRing R] {U : Set (Sp R)}
    (hU : IsOpen U) (h : IsLocalRing.closedPoint R ∈ U) (x : Sp R) : x ∈ U := by
  have hx : (x : PrimeSpectrum R) ⤳ IsLocalRing.closedPoint R :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal x.2.ne_top)
  exact hx.mem_open hU h

theorem exists_smooth_chart : ∀ (Λ : Type) [CommRing Λ] (ι₀ : Λ →+* ℂ) (M : Scheme.{0}) (s : M ⟶ Sp Λ) (V : M.Opens) (d : ℕ),
    SmoothOfRelativeDimension d (V.ι ≫ s) → ∀ (R : Type) [CommRing R] [Algebra ℂ R] [IsLocalRing R] (b : Sp R ⟶ M),
    (∀ x, b.base x ∈ V) → b ≫ s = spMap ((algebraMap ℂ R).comp ι₀) →
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra ℂ B) (_ : Algebra.Smooth ℂ B) (g : Sp B ⟶ M) (j : B →ₐ[ℂ] R),
      spMap (j : B →+* R) ≫ g = b := by
  intro Λ _ ι₀ M s V d hd R _ _ _ b hbV hbs
  haveI : Smooth (V.ι ≫ s) := SmoothOfRelativeDimension.smooth d _
  obtain ⟨W, hW, hxW, hWV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp M.isBasis_affineOpens)
    (hbV (IsLocalRing.closedPoint R))
  have hbW : ∀ x, b.base x ∈ W := fun x =>
    mem_of_closedPoint_mem (U := b.base ⁻¹' (W : Set M)) (W.2.preimage b.base.hom.continuous) hxW x
  haveI : Smooth ((Scheme.Opens.ι (X := M) W) ≫ s) := by
    rw [← Scheme.homOfLE_ι M hWV, Category.assoc]; infer_instance
  have hWa : IsAffineOpen W := hW
  let e := hWa.isoSpec
  let f : Spec Γ(M, W) ⟶ Sp Λ := e.inv ≫ (Scheme.Opens.ι (X := M) W) ≫ s
  have hf : Smooth f := inferInstance
  let φ := Spec.preimage f
  have hφ : φ.hom.Smooth := (HasRingHomProperty.Spec_iff (P := @Smooth)).1 (by rw [Spec.map_preimage]; exact hf)

  letI : Algebra Λ Γ(M, W) := φ.hom.toAlgebra
  haveI : Algebra.Smooth Λ Γ(M, W) := RingHom.smooth_algebraMap.1 hφ
  letI : Algebra Λ ℂ := ι₀.toAlgebra
  have hrange : Set.range b.base ⊆ Set.range (Scheme.Opens.ι (X := M) W).base := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hbW x
  let b' : Sp R ⟶ W := IsOpenImmersion.lift (Scheme.Opens.ι (X := M) W) b hrange
  have hb' : b' ≫ (Scheme.Opens.ι (X := M) W) = b := IsOpenImmersion.lift_fac _ _ _
  let ψ := Spec.preimage (b' ≫ e.hom)
  have hψ : Spec.map ψ = b' ≫ e.hom := Spec.map_preimage _
  have hcomp : φ ≫ ψ = CommRingCat.ofHom ((algebraMap ℂ R).comp ι₀) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, Spec.map_preimage]
    simp only [f, Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% hb', hbs]
  letI : Algebra Λ R := ((algebraMap ℂ R).comp ι₀).toAlgebra
  haveI : IsScalarTower Λ ℂ R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let g' : Γ(M, W) →ₐ[Λ] R :=
    { ψ.hom with
      commutes' := fun r => by
        have := congrArg (fun h => h.hom r) hcomp
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
        exact this }
  let j : ℂ ⊗[Λ] Γ(M, W) →ₐ[ℂ] R :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ R) g' (fun _ _ => Commute.all _ _)
  refine ⟨ℂ ⊗[Λ] Γ(M, W), inferInstance, inferInstance, inferInstance,
    spMap (Algebra.TensorProduct.includeRight (R := Λ) (A := ℂ) (B := Γ(M, W))).toRingHom ≫ e.inv ≫ (Scheme.Opens.ι (X := M) W), j, ?_⟩
  have hj : (j : ℂ ⊗[Λ] Γ(M, W) →+* R).comp (Algebra.TensorProduct.includeRight (R := Λ) (A := ℂ) (B := Γ(M, W))).toRingHom = ψ.hom := by
    ext a
    simp [j, g']
  rw [← Category.assoc, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hj]
  change Spec.map ψ ≫ _ = _
  rw [hψ, Category.assoc, Iso.hom_inv_id_assoc, hb']

end GlobalTheory.AffChartSmooth
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_local_factorization : ∀ (Λ : Type) [CommRing Λ] (ι₀ : Λ →+* ℂ) (M : Scheme.{0}) (s : M ⟶ Sp Λ) (V : M.Opens) (d : ℕ),
    SmoothOfRelativeDimension d (V.ι ≫ s) → ∀ (R : Type) [CommRing R] [Algebra ℂ R] [IsLocalRing R] (b : Sp R ⟶ M),
    (∀ x, b.base x ∈ V) → b ≫ s = spMap ((algebraMap ℂ R).comp ι₀) →
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra ℂ B) (_ : Algebra.Smooth ℂ B) (g : Sp B ⟶ M) (j : B →ₐ[ℂ] R),
      spMap (j : B →+* R) ≫ g = b := by
  atlas_forward_decl GlobalTheory.AffChartSmooth.exists_smooth_chart
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.Obj

theorem exists_detGen_away : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (B : Type) [CommRing B] [Algebra ℂ B]
    [Algebra.Smooth ℂ B] (R : Type) [CommRing R] [Algebra ℂ R] [IsLocalRing R] (j : B →ₐ[ℂ] R) (X : Obj F 𝔠 (Sp B)),
    ∃ (B' : Type) (_ : CommRing B') (_ : Algebra ℂ B') (_ : Algebra.Smooth ℂ B') (X₁ : Obj F 𝔠 (Sp B'))
      (_ : X₁.DetGen) (k : B →ₐ[ℂ] B') (j' : B' →ₐ[ℂ] R) (q : X₁.A.left ⟶ X.A.left),
      X₁.IsPullBy X (spMap (k : B →+* B')) q ∧ j'.comp k = j := by
  intro F _ _ 𝔠 B _ _ _ R _ _ _ j X
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.lie_algebra_finite_projective_rank X
  let p : Ideal B := (IsLocalRing.maximalIdeal R).comap j
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  haveI : Module.FinitePresentation B X.Lie := Module.finitePresentation_of_projective B X.Lie
  haveI : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl X.Lie) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨f, hf, hfree, hfr⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl X.Lie) (Localization.AtPrime p)
  have hju : IsUnit (j f) := by
    by_contra h
    exact hf ((IsLocalRing.mem_maximalIdeal _).2 h)
  let B' := Localization.Away f
  let k : B →ₐ[ℂ] B' := IsScalarTower.toAlgHom ℂ B B'
  let j' : B' →ₐ[ℂ] R := IsLocalization.liftAlgHom (M := Submonoid.powers f) (f := j) (by
    rintro ⟨_, n, rfl⟩
    simpa using hju.pow n)
  have hjk : j'.comp k = j := AlgHom.ext fun x ↦ by
    simp [j', k, IsLocalization.liftAlgHom, IsLocalization.lift_eq]
  haveI : Nontrivial B' := (j' : B' →+* R).domain_nontrivial
  haveI : Algebra.Smooth B B' := Algebra.Smooth.of_isLocalization_Away f
  haveI : Algebra.Smooth ℂ B' := Algebra.Smooth.comp ℂ B B'
  obtain ⟨X₁, q, hq⟩ := exists_isPullBy X (spMap (algebraMap B B'))
  obtain ⟨e, -, -⟩ := exists_lieEquiv (R' := B') hq
  haveI : Module.Finite B' (LocalizedModule.Away f X.Lie) :=
    Module.Finite.of_isLocalizedModule (Submonoid.powers f) (LocalizedModule.mkLinearMap (Submonoid.powers f) X.Lie)
  have hd : Module.finrank B' (LocalizedModule.Away f X.Lie) = Module.finrank ℚ F := by
    rw [hfr]
    exact hrk ⟨p, inferInstance⟩
  let b₀ := Module.finBasisOfFinrankEq B' (LocalizedModule.Away f X.Lie) hd
  let hbc := IsLocalizedModule.isBaseChange (Submonoid.powers f) B'
    (LocalizedModule.mkLinearMap (Submonoid.powers f) X.Lie)
  let b₁ : Module.Basis (Fin (Module.finrank ℚ F)) B' X₁.Lie := b₀.map (hbc.equiv.symm ≪≫ₗ e)
  exact ⟨B', inferInstance, inferInstance, inferInstance, X₁, DetGen.ofBasis X₁ b₁, k, j', q, hq, hjk⟩

end GlobalTheory.RealMult.Obj
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_det_generated_cover : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (B : Type) [CommRing B] [Algebra ℂ B]
    [Algebra.Smooth ℂ B] (R : Type) [CommRing R] [Algebra ℂ R] [IsLocalRing R] (j : B →ₐ[ℂ] R) (X : Obj F 𝔠 (Sp B)),
    ∃ (B' : Type) (_ : CommRing B') (_ : Algebra ℂ B') (_ : Algebra.Smooth ℂ B') (X₁ : Obj F 𝔠 (Sp B'))
      (_ : X₁.DetGen) (k : B →ₐ[ℂ] B') (j' : B' →ₐ[ℂ] R) (q : X₁.A.left ⟶ X.A.left),
      X₁.IsPullBy X (spMap (k : B →+* B')) q ∧ j'.comp k = j := by
  atlas_forward_decl GlobalTheory.RealMult.Obj.exists_detGen_away
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet.An

theorem jetRing_local_nil : ∀ (I : Type) [Fintype I] (n : ℕ) (J : JetRing ℂ I n),
    IsLocalRing J.B ∧ (∀ a : ℂ, J.π (algebraMap ℂ J.B a) = a) ∧ ∀ x ∈ RingHom.ker J.π, IsNilpotent x := by
  intro I _ n J
  have hπ : ∀ a : ℂ, J.π (algebraMap ℂ J.B a) = a := by
    intro a
    rw [J.π_eq, Algebra.algebraMap_eq_smul_one, ← J.one, map_smul]
    simp
  have hnil : ∀ x ∈ RingHom.ker J.π, IsNilpotent x := by
    intro x hx
    obtain ⟨N, hN⟩ := J.nil
    refine ⟨N, ?_⟩
    have := hN (List.replicate N (1, x)) (by
      intro p hp; rw [List.eq_of_mem_replicate hp]; exact hx) (by simp)
    simpa [J.κ.dpow_one hx] using this
  refine ⟨?_, hπ, hnil⟩
  haveI : Nontrivial J.B := RingHom.domain_nontrivial J.π
  have key : ∀ a : J.B, a ∈ nonunits J.B → J.π a = 0 := by
    intro a ha
    by_contra h0
    apply ha
    have hu : IsUnit (algebraMap ℂ J.B (J.π a)) := (IsUnit.mk0 _ h0).map _
    have hn : IsNilpotent (a - algebraMap ℂ J.B (J.π a)) :=
      hnil _ (by simp [RingHom.mem_ker, hπ])
    have := hn.isUnit_add_left_of_commute hu (Commute.all _ _)
    simpa using this
  refine IsLocalRing.of_nonunits_add fun a b ha hb ↦ ?_
  intro hab
  have h1 := hab.map J.π
  rw [map_add, key a ha, key b hb, add_zero] at h1
  exact not_isUnit_zero h1

theorem exists_smooth_modulus_point : GlobalTheory.Published.DelignePappasModel → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
    (R : Type) [CommRing R] [Algebra ℂ R] (X' : Obj F 𝔠 (Sp R)), X'.Level 3 →
    ∃ (M : Scheme.{0}) (s : M ⟶ Sp (Localization.Away (3 : ℤ))) (U : Obj F 𝔠 M) (V : M.Opens) (b : Sp R ⟶ M)
      (φ : X'.A.left ⟶ U.A.left) (ι₀ : Localization.Away (3 : ℤ) →+* ℂ),
      X'.IsPullBy U b φ ∧ SmoothOfRelativeDimension (Module.finrank ℚ F) (V.ι ≫ s) ∧ (∀ x, b.base x ∈ V) ∧
      b ≫ s = spMap ((algebraMap ℂ R).comp ι₀) := by
  intro H F _ _ _ 𝔠 R _ _ X' β
  obtain ⟨M, s, U, α, hfine, -, -, -, -, -, ⟨V, -, hV, hdisc, -⟩, -⟩ := H F 𝔠 3 le_rfl
  have h3 : IsUnit ((Int.castRingHom ℂ) 3) := by
    rw [isUnit_iff_ne_zero]; norm_num
  let ι₀ : Localization.Away (3 : ℤ) →+* ℂ := IsLocalization.Away.lift (3 : ℤ) h3
  obtain ⟨b, ⟨hbs, φ, hφ, -⟩, -⟩ := hfine (Sp R) (spMap ((algebraMap ℂ R).comp ι₀)) X' β
  refine ⟨M, s, U, V, b, φ, ι₀, hφ, hV, ?_, hbs⟩
  intro x
  apply hdisc
  have hd : IsUnit ((NumberField.discr F : ℤ) : R) := by
    rw [← map_intCast (algebraMap ℂ R)]
    exact (IsUnit.mk0 _ (by exact_mod_cast NumberField.discr_ne_zero F)).map _
  let e := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  have hu : IsUnit ((NumberField.discr F : ℤ) : Γ(Sp R, ⊤)) := by
    have := hd.map e.symm.toRingHom
    simpa [map_intCast] using this
  have hx : x ∈ b ⁻¹ᵁ M.basicOpen ((NumberField.discr F : ℤ) : Γ(M, ⊤)) := by
    rw [Scheme.preimage_basicOpen, map_intCast]
    have hu' : IsUnit ((NumberField.discr F : ℤ) : Γ(Sp R, b ⁻¹ᵁ ⊤)) := by
      have := hu.map ((Sp R).presheaf.map (homOfLE (le_top : b ⁻¹ᵁ ⊤ ≤ ⊤)).op).hom
      rwa [map_intCast] at this
    rw [Scheme.basicOpen_of_isUnit _ hu']
    trivial
  exact hx

theorem chart_of_hilbertBlumenthal : GlobalTheory.Published.HilbertBlumenthal → Chart := by
  intro H F _ _ _ 𝔠 I _ n J X'
  obtain ⟨hloc, hπ, hnil⟩ := jetRing_local_nil I n J
  let π : J.B →ₐ[ℂ] ℂ := { J.π with commutes' := hπ }
  obtain ⟨X₀, i₀, h₀⟩ := Obj.exists_isPullBy X' (spMap (π : J.B →+* ℂ))
  obtain ⟨α₀⟩ := GlobalTheory.T.nonempty_level_structure_complex F 𝔠 3 (by norm_num) X₀
  obtain ⟨β⟩ := GlobalTheory.T.level_structure_lift_nilpotent F 𝔠 3 (by norm_num) J.B π hnil X' X₀ i₀ h₀ α₀
  obtain ⟨M, s, U, V, b, φ, ι₀, hφ, hV, hb, hbs⟩ := exists_smooth_modulus_point H.1 F 𝔠 J.B X' β
  obtain ⟨B, _, _, _, g, j, hg⟩ := GlobalTheory.T.exists_smooth_local_factorization _ ι₀ M s V _ hV J.B b hb hbs
  obtain ⟨X₁, φ₁, h₁⟩ := Obj.exists_isPullBy U g
  rw [← hg] at hφ
  obtain ⟨ψ, hψ, -⟩ := hφ.cancel h₁
  obtain ⟨B', _, _, _, X₂, δ, k, j', q, hq, hk⟩ := GlobalTheory.T.exists_smooth_det_generated_cover F 𝔠 B J.B j X₁
  have e : spMap (j : B →+* J.B) = spMap (j' : B' →+* J.B) ≫ spMap (k : B →+* B') := by
    rw [← hk]
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]; rfl
  rw [e] at hψ
  obtain ⟨ψ', hψ', -⟩ := hψ.cancel hq
  exact ⟨B', _, _, inferInstance, X₂, δ, j', ψ', hψ'⟩

end GlobalTheory.LatJet.An
end
end

open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_of_hilbert_blumenthal : GlobalTheory.Published.HilbertBlumenthal → Chart := by
  atlas_forward_decl GlobalTheory.LatJet.An.chart_of_hilbertBlumenthal
end
