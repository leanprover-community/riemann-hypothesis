import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralUnitIndicatorEventuallyOneClassStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralElementCharPolyNonsplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryConjOfSameEllipticCharpolyInert

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT

theorem ev_int_exsplit {E : Type} [Field E] [NumberField E] (x : E) :
    ∀ᶠ w : Pl E in cofinite, algebraMap E (w.adicCompletion E) x ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) x).eventually

theorem coeff_zero_ne_zero_of_mem_ell {E : Type} [Field E] [NumberField E] {n : ℕ} {P : E[X]} (hP : P ∈ Ell E n) :
    P.coeff 0 ≠ 0 := by
  intro h0
  obtain ⟨hmon, -, -, hroots⟩ := hP
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
  have hne : P.map τ ≠ 0 := (hmon.map τ).ne_zero
  have hr : (0 : ℂ) ∈ (P.map τ).roots := by
    rw [mem_roots hne, IsRoot.def, eval_map, eval₂_at_zero, h0, map_zero]
  have := hroots τ 0 hr
  simp at this

theorem exists_mat_charpoly {E : Type} [Field E] {n : ℕ} {P : E[X]} (hmon : P.Monic) (hdeg : P.natDegree = n) :
    ∃ M : Matrix (Fin n) (Fin n) E, M.charpoly = P := by
  let pb := AdjoinRoot.powerBasis hmon.ne_zero
  have hdim : pb.dim = n := by rw [AdjoinRoot.powerBasis_dim, hdeg]
  refine ⟨Matrix.reindex (finCongr hdim) (finCongr hdim) (Algebra.leftMulMatrix pb.basis pb.gen), ?_⟩
  rw [Matrix.charpoly_reindex, charpoly_leftMulMatrix, AdjoinRoot.minpoly_powerBasis_gen_of_monic hmon]

theorem exists_int_charpoly_atPl_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, IsSplitAt w → ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = atPl w P := by
  intro E _ _ _ _ n _ P hP
  obtain ⟨M, hM⟩ := exists_mat_charpoly hP.1 hP.2.1
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hM]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (coeff_zero_ne_zero_of_mem_ell hP)
  have hev1 : ∀ᶠ w : Pl E in cofinite, ∀ ij : Fin n × Fin n,
      algebraMap E (w.adicCompletion E) (M ij.1 ij.2) ∈ w.adicCompletionIntegers E :=
    Filter.eventually_all.2 fun ij => ev_int_exsplit (M ij.1 ij.2)
  have hev2 := ev_int_exsplit (E := E) M.det⁻¹
  filter_upwards [hev1, hev2] with w hent hinv hs
  let N : Matrix (Fin n) (Fin n) (Ov E w) := fun i j => ⟨_, hent (i, j)⟩
  have hN : (Ov E w).subtype.mapMatrix N = M.map (algebraMap E (w.adicCompletion E)) := by
    ext i j; rfl
  have hdetN : ((N.det : Ov E w) : w.adicCompletion E) = algebraMap E (w.adicCompletion E) M.det := by
    have := RingHom.map_det (Ov E w).subtype N
    rw [hN] at this
    exact this.trans (RingHom.map_det _ M).symm
  have hu : IsUnit N.det := by
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
    change ((N.det : Ov E w) : w.adicCompletion E) * algebraMap E (w.adicCompletion E) M.det⁻¹ = 1
    rw [hdetN, ← map_mul, mul_inv_cancel₀ hdet, map_one]
  let g : GL (Fin n) (Ov E w) := ((Matrix.isUnit_iff_isUnit_det N).2 hu).unit
  have hmemU : bc (Ov E w).subtype g ∈ UL n w := by
    simp only [UL, if_pos hs]; exact Subgroup.mem_top _
  refine ⟨⟨_, hmemU⟩, ?_, ?_⟩
  · rw [KL, Subgroup.mem_subgroupOf]
    exact ⟨g, rfl⟩
  · change ((Ov E w).subtype.mapMatrix (g : Matrix (Fin n) (Fin n) (Ov E w))).charpoly = atPl w P
    rw [IsUnit.unit_spec, hN, Matrix.charpoly_map, hM]

end GlobalTheory.BCT
end
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_exists_integral_charpoly_split_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, IsSplitAt w → ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = atPl w P := by
  first | exact @GlobalTheory.BCT.exists_int_charpoly_atPl_split | exact GlobalTheory.BCT.exists_int_charpoly_atPl_split | (intros; apply GlobalTheory.BCT.exists_int_charpoly_atPl_split <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_element_char_poly_nonsplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = atPl w P := by
  first | exact @GlobalTheory.ExInertUnit.exists_integral_unitary_charpoly | exact GlobalTheory.ExInertUnit.exists_integral_unitary_charpoly | (intros; apply GlobalTheory.ExInertUnit.exists_integral_unitary_charpoly <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.SplitConj

theorem exists_conj_of_isSplitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∀ P ∈ Ell E n,
    ∀ w : Pl E, IsSplitAt w → ∀ γ γ' : UL n w, γ.1.val.charpoly = atPl w P → γ'.1.val.charpoly = atPl w P →
      ∃ g : UL n w, γ' = g⁻¹ * γ * g := by
  intro E _ _ _ n P hP w hw γ γ' h h'
  have hs : (atPl w P).Separable := hP.2.2.1.map
  obtain ⟨g, hg⟩ := GlobalTheory.BCT.ClsFin.conj_of_charpoly γ.1 γ'.1 (by rw [h]; exact hs) (h.trans h'.symm)
  have hmem : g ∈ UL n w := by
    rw [UL, if_pos hw]
    exact Subgroup.mem_top g
  exact ⟨⟨g, hmem⟩, Subtype.ext hg⟩

end GlobalTheory.BCT.SplitConj
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_same_separable_charpoly_split_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∀ P ∈ Ell E n, ∀ w : Pl E, IsSplitAt w → ∀ γ γ' : UL n w, γ.1.val.charpoly = atPl w P → γ'.1.val.charpoly = atPl w P → ∃ g : UL n w, γ' = g⁻¹ * γ * g := by
  first | exact @GlobalTheory.BCT.SplitConj.exists_conj_of_isSplitAt | exact GlobalTheory.BCT.SplitConj.exists_conj_of_isSplitAt | (intros; apply GlobalTheory.BCT.SplitConj.exists_conj_of_isSplitAt <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_unitary_conj_of_same_elliptic_charpoly_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, ¬ IsSplitAt w → ∀ γ γ' : UL n w, γ ∈ KL n w → γ' ∈ KL n w → γ.1.val.charpoly = atPl w P → γ'.1.val.charpoly = atPl w P → ∃ g : UL n w, γ' = g⁻¹ * γ * g := by
  first | exact @GlobalTheory.BCT.UnitInert.conj_of_charpoly_inert | exact GlobalTheory.BCT.UnitInert.conj_of_charpoly_inert | (intros; apply GlobalTheory.BCT.UnitInert.conj_of_charpoly_inert <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitOrbCount

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cp_conj {n : ℕ} {w : Pl E} (g γ : UL n w) :
    (g⁻¹ * γ * g).1.val.charpoly = γ.1.val.charpoly := by
  have h : ((g⁻¹ * γ * g : UL n w) : GLw n w) = (g : GLw n w)⁻¹ * (γ : GLw n w) * (g : GLw n w) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  have h2 : (g⁻¹ * γ * g).1.val = ((g : GLw n w)⁻¹ : GLw n w).val * γ.1.val * (g : GLw n w).val := by
    rw [← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val h
  rw [h2, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' (g : GLw n w) γ.1.val

theorem mk_eq_iff {G : Type} [Group G] (x y : G) :
    (Quot.mk _ x : TwCl (MonoidHom.id G)) = Quot.mk _ y ↔ ∃ g : G, y = g⁻¹ * x * g := by
  constructor
  · intro h
    have h' := Quot.eqvGen_exact h
    clear h
    induction h' with
    | rel a b hab => obtain ⟨g, hg⟩ := hab; exact ⟨g, by simpa using hg⟩
    | refl a => exact ⟨1, by simp⟩
    | symm a b _ ih => obtain ⟨g, hg⟩ := ih; exact ⟨g⁻¹, by rw [hg]; group⟩
    | trans a b c _ _ ih1 ih2 =>
      obtain ⟨g, hg⟩ := ih1; obtain ⟨k, hk⟩ := ih2; exact ⟨g * k, by rw [hk, hg]; group⟩
  · rintro ⟨g, hg⟩
    exact Quot.sound ⟨g, by simpa using hg⟩

theorem exists_section : ∃ S : Set (Pl E), IsSection S := by
  refine ⟨{u | u = @Classical.epsilon _ ⟨u⟩ fun u' : Pl E => u'.under (𝓞 (maximalRealSubfield E)) =
      u.under (𝓞 (maximalRealSubfield E))}, fun w => ?_⟩
  haveI : Nonempty (Pl E) := ⟨w⟩
  have hspec := Classical.epsilon_spec (p := fun u' : Pl E => u'.under (𝓞 (maximalRealSubfield E)) =
      w.under (𝓞 (maximalRealSubfield E))) ⟨w, rfl⟩
  refine ⟨_, ⟨?_, hspec⟩, ?_⟩
  · show _ = _
    simp only [hspec]
  · rintro u ⟨hu, hu'⟩
    rw [Set.mem_setOf_eq] at hu
    rw [hu]
    simp only [hu']

theorem ell_mul {n : ℕ} (p₁ p₂ : E[X]) (h1 : p₁ ∈ Ell E p₁.natDegree) (h2 : p₂ ∈ Ell E p₂.natDegree)
    (hc : IsCoprime p₁ p₂) (hn : p₁.natDegree + p₂.natDegree = n) : p₁ * p₂ ∈ Ell E n := by
  obtain ⟨m1, -, s1, r1⟩ := h1
  obtain ⟨m2, -, s2, r2⟩ := h2
  refine ⟨m1.mul m2, by rw [m1.natDegree_mul m2, hn], s1.mul s2 hc, fun τ z hz => ?_⟩
  rw [Polynomial.map_mul, Polynomial.roots_mul] at hz
  · rcases Multiset.mem_add.1 hz with h | h
    · exact r1 τ z h
    · exact r2 τ z h
  · rw [← Polynomial.map_mul]
    exact ((m1.mul m2).map τ).ne_zero

end GlobalTheory.UnitOrbCount

namespace GlobalTheory.UnitOrbCount


end GlobalTheory.UnitOrbCount
end
