import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AutFormDefiniteUnitaryEqSumPolynomialMulAutForm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsConjPolynomialDefiniteUnitaryRational
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DefiniteUnitaryRealApproxAndFiniteInfiniteSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryCoordinateAlgebraDenseStatement

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.autFormDefiniteUnitary_eq_sum_polynomial_mul_autForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : UA E n → ℂ), IsAutFormU φ → ∃ (m : ℕ) (p : Fin m → infU E n → ℂ) (e : Fin m → UA E n → ℂ), (∀ i, p i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j} ∧ IsAutFormU (e i)) ∧ ∀ (k : infU E n) (g : UA E n), φ (g * k) = ∑ i, p i k * e i g := by
  first | exact @GlobalTheory.UnitaryDecomp.exists_poly_mul_autForm | exact GlobalTheory.UnitaryDecomp.exists_poly_mul_autForm | (intros; apply GlobalTheory.UnitaryDecomp.exists_poly_mul_autForm <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_polynomial_definiteUnitary_rational : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ), ∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∃ p' ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∀ γ ∈ ratU E n, ∀ k : infU E n, cInf k.1 = cInf γ → p' k = σ (p k) := by
  first | exact @GlobalTheory.UnitaryBC.exists_conj_polyFun | exact GlobalTheory.UnitaryBC.exists_conj_polyFun | (intros; apply GlobalTheory.UnitaryBC.exists_conj_polyFun <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitary_realApprox_and_finite_infinite_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), Dense ((ratU E n : Set (UA E n)) * (finU E n : Set (UA E n))) ∧ Dense {k : infU E n | ∃ γ ∈ ratU E n, cInf k.1 = cInf γ} ∧ (∀ k : infU E n, ∀ g ∈ finU E n, k.1 * g = g * k.1) ∧ ∃ (a : UA E n →* finU E n) (b : UA E n →* infU E n), Continuous a ∧ Continuous b ∧ (∀ x, x = (a x).1 * (b x).1) ∧ ∀ (g : finU E n) (k : infU E n), a (g.1 * k.1) = g ∧ b (g.1 * k.1) = k := by
  first | exact @GlobalTheory.UnitarySplit.dense_and_split | exact GlobalTheory.UnitarySplit.dense_and_split | (intros; apply GlobalTheory.UnitarySplit.dense_and_split <;> assumption)
end

section
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

theorem continuous_of_right_invariant_open {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (e : G → ℂ) (V : Subgroup G) (hV : IsOpen (V : Set G)) (h : ∀ u ∈ V, ∀ g, e (g * u) = e g) :
    Continuous e := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open e).2 fun x => ?_)
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (V : Set G), hV.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  rw [← h _ hy x, mul_inv_cancel_left]

theorem exists_fun_of_poly_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (m : ℕ) (p : Fin m → infU E n → ℂ) (e : Fin m → finU E n → ℂ), (∀ i, p i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) → (∀ i, ∃ V : Subgroup (finU E n), IsOpen (V : Set (finU E n)) ∧ ∀ u ∈ V, ∀ g, e i (g * u) = e i g) → ∃ φ : UA E n → ℂ, Continuous φ ∧ IsOpen {k : finU E n | RU E n k φ = φ} ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)) ∧ ∀ (g : finU E n) (k : infU E n), φ (g.1 * k.1) = ∑ i, p i k * e i g := by
  intro E _ _ _ n m p e hp he
  obtain ⟨-, -, -, a, b, ha, hb, -, hab⟩ := GlobalTheory.T.definiteUnitary_realApprox_and_finite_infinite_split E n
  obtain ⟨hcont, -, -, -, hco⟩ := GlobalTheory.T.unitary_coordinate_algebra_dense E n
  choose V hVo hV using he
  have haf : ∀ g : finU E n, a g.1 = g := fun g => by simpa using (hab g 1).1
  have hbf : ∀ g : finU E n, b g.1 = 1 := fun g => by simpa using (hab g 1).2
  have hai : ∀ k : infU E n, a k.1 = 1 := fun k => by simpa using (hab 1 k).1
  have hbi : ∀ k : infU E n, b k.1 = k := fun k => by simpa using (hab 1 k).2
  have hR : ∀ (x : UA E n) (φ : UA E n → ℂ) (g : UA E n), RU E n x φ g = φ (g * x) := fun _ _ _ => rfl
  refine ⟨fun x => ∑ i, p i (b x) * e i (a x), ?_, ?_, ?_, fun g k => ?_⟩
  · exact continuous_finsetSum _ fun i _ => ((hcont _ (hp i)).comp hb).mul
      ((continuous_of_right_invariant_open _ _ (hVo i) (hV i)).comp ha)
  · set φ : UA E n → ℂ := fun x => ∑ i, p i (b x) * e i (a x) with hφ
    let S : Subgroup (finU E n) :=
      { carrier := {k : finU E n | RU E n k φ = φ}
        one_mem' := by
          change RU E n ((1 : finU E n) : UA E n) φ = φ
          funext g
          rw [hR]
          simp
        mul_mem' := fun {x y} hx hy => by
          change RU E n ((x * y : finU E n) : UA E n) φ = φ
          funext g
          have h1 := congrFun (show RU E n x φ = φ from hx) g
          have h2 := congrFun (show RU E n y φ = φ from hy) (g * x)
          rw [hR] at h1 h2 ⊢
          rw [Subgroup.coe_mul, ← mul_assoc, h2, h1]
        inv_mem' := fun {x} hx => by
          change RU E n ((x⁻¹ : finU E n) : UA E n) φ = φ
          funext g
          have h1 := congrFun (show RU E n x φ = φ from hx) (g * (x : UA E n)⁻¹)
          rw [hR] at h1 ⊢
          rw [Subgroup.coe_inv, ← h1, inv_mul_cancel_right] }
    have hle : (⨅ i, V i) ≤ S := fun u hu => by
      change RU E n (u : UA E n) φ = φ
      funext g
      rw [hR]
      simp only [hφ, map_mul, haf, hbf, mul_one]
      exact Finset.sum_congr rfl fun i _ => by rw [hV i u (Subgroup.mem_iInf.1 hu i)]
    refine Subgroup.isOpen_mono hle ?_
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite hVo
  · choose N c d _ hcd using fun i => hco _ (hp i)
    let f : (Σ i, Fin (N i)) → UA E n → ℂ := fun s x => c s.1 s.2 (b x) * e s.1 (a x)
    haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range f)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    have : RU E n k (fun x => ∑ i, p i (b x) * e i (a x)) = ∑ s : Σ i, Fin (N i), d s.1 s.2 k • f s := by
      funext g
      rw [hR]
      simp only [map_mul, hai, hbi, mul_one, hcd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, f,
        Fintype.sum_sigma, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    change RU E n k _ ∈ _
    rw [this]
    exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  · simp only [(hab g k).1, (hab g k).2]

end GlobalTheory.UnitaryBC
end

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_definiteUnitary_function_polynomial_mul_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (m : ℕ) (p : Fin m → infU E n → ℂ) (e : Fin m → finU E n → ℂ), (∀ i, p i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) → (∀ i, ∃ V : Subgroup (finU E n), IsOpen (V : Set (finU E n)) ∧ ∀ u ∈ V, ∀ g, e i (g * u) = e i g) → ∃ φ : UA E n → ℂ, Continuous φ ∧ IsOpen {k : finU E n | RU E n k φ = φ} ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)) ∧ ∀ (g : finU E n) (k : infU E n), φ (g.1 * k.1) = ∑ i, p i k * e i g := by
  atlas_forward_decl GlobalTheory.UnitaryBC.exists_fun_of_poly_smooth
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

theorem exists_conj_isAutFormU (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ)
    (φ : UA E n → ℂ) (hφ : IsAutFormU φ) :
    ∃ φ' : UA E n → ℂ, IsAutFormU φ' ∧ ∀ g ∈ finU E n, φ' g = σ (φ g) := by
  obtain ⟨m, p, e, hpe, hdec⟩ := GlobalTheory.T.autFormDefiniteUnitary_eq_sum_polynomial_mul_autForm E n φ hφ
  choose p' hp' hpp using fun i => GlobalTheory.T.exists_conj_polynomial_definiteUnitary_rational E n σ (p i) (hpe i).1
  obtain ⟨hD, -, -, a, b, -, -, hab, -⟩ := GlobalTheory.T.definiteUnitary_realApprox_and_finite_infinite_split E n
  obtain ⟨φ', hc, hl, hk, hv⟩ := GlobalTheory.T.exists_definiteUnitary_function_polynomial_mul_smooth E n m p' (fun i g => σ (e i g.1)) hp' (fun i => by
    refine ⟨
      { carrier := {k : finU E n | RU E n k (e i) = e i}
        one_mem' := by simp
        mul_mem' := fun {x y} hx hy => by
          simp only [Set.mem_setOf_eq] at hx hy ⊢
          rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hy, hx]
        inv_mem' := fun {x} hx => by
          simp only [Set.mem_setOf_eq] at hx ⊢
          conv_lhs => rw [← hx]
          rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply] }, ?_, ?_⟩
    · exact (hpe i).2.level
    · intro u hu g
      exact congrArg σ (congrFun (show RU E n u (e i) = e i from hu) g.1))
  have key : ∀ γ ∈ ratU E n, ∀ x : UA E n, cInf x = cInf γ → φ' x = σ (φ x) := by
    intro γ hγ x hx
    have h1 : cInf (b x).1 = cInf γ := by
      rw [← hx]
      conv_rhs => rw [hab x, map_mul, show cInf (a x).1 = 1 from (a x).2, one_mul]
    conv_lhs => rw [hab x, hv]
    conv_rhs => rw [hab x, hdec, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hpp i γ hγ _ h1]
  refine ⟨φ', ⟨hc, fun γ hγ g => ?_, hl, hk⟩, fun g hg => key 1 (one_mem _) g (by rw [map_one]; exact hg)⟩
  have hc2 : Continuous fun x => φ' (γ * x) := hc.comp (continuous_const.mul continuous_id)
  refine congrFun (Continuous.ext_on hD hc2 hc ?_) g
  rintro _ ⟨δ, hδ, u, hu, rfl⟩
  have hu' : cInf u = 1 := hu
  change φ' (γ * (δ * u)) = φ' (δ * u)
  rw [key (γ * δ) (mul_mem hγ hδ) _ (by simp only [map_mul, hu', mul_one]),
    key δ hδ _ (by simp only [map_mul, hu', mul_one]), hφ.left γ hγ]

end GlobalTheory.UnitaryBC
end
