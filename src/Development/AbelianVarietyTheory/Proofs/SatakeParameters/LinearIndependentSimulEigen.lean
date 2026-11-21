import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DefiniteUnitaryRealApproxAndFiniteInfiniteSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryCoordinateAlgebraDense
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AutFormDefiniteUnitaryEqSumPolynomialMulAutForm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsConjPolynomialDefiniteUnitaryRational
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsConjIsAutFormU

section
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
open scoped Pointwise

noncomputable section

namespace GlobalTheory.EigenConj

theorem opOf_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ) (t : UA E n →₀ ℂ), (∀ g ∈ t.support, g ∈ finU E n ∧ ∃ q : ℚ, t g = q) → ∀ (φ φ' : UA E n → ℂ) (z : ℂ), IsAutFormU φ → IsAutFormU φ' → (∀ g ∈ finU E n, φ' g = σ (φ g)) → opOf (RU E n) t φ = z • φ → opOf (RU E n) t φ' = σ z • φ' := by
  intro E _ _ _ n σ t ht φ φ' z hφ hφ' hfin heig
  have key : ∀ (f : UA E n → ℂ) (x : UA E n),
      opOf (RU E n) t f x = ∑ g ∈ t.support, t g * f (x * g) := by
    intro f x
    simp only [opOf, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  have hc1 : Continuous (opOf (RU E n) t φ') := by
    have e : opOf (RU E n) t φ' = fun x => ∑ g ∈ t.support, t g * φ' (x * g) := funext (key φ')
    rw [e]
    exact continuous_finset_sum _ fun g _ =>
      continuous_const.mul (hφ'.cont.comp (continuous_id.mul continuous_const))
  have hc2 : Continuous (σ z • φ') := hφ'.cont.const_smul _
  have hl1 : ∀ γ ∈ ratU E n, ∀ x, opOf (RU E n) t φ' (γ * x) = opOf (RU E n) t φ' x := by
    intro γ hγ x
    rw [key, key]
    simp_rw [mul_assoc, hφ'.left γ hγ]
  have hl2 : ∀ γ ∈ ratU E n, ∀ x, (σ z • φ') (γ * x) = (σ z • φ') x := by
    intro γ hγ x
    simp only [Pi.smul_apply, hφ'.left γ hγ]
  have hfinEq : ∀ h ∈ finU E n, opOf (RU E n) t φ' h = (σ z • φ') h := by
    intro h hh
    have e := congrFun heig h
    rw [key, Pi.smul_apply, smul_eq_mul] at e
    rw [key, Pi.smul_apply, smul_eq_mul]
    calc ∑ g ∈ t.support, t g * φ' (h * g) = ∑ g ∈ t.support, σ (t g * φ (h * g)) :=
          Finset.sum_congr rfl fun g hg => by
            obtain ⟨hgU, q, hq⟩ := ht g hg
            rw [map_mul, hfin _ ((finU E n).mul_mem hh hgU), hq, map_ratCast]
      _ = σ (∑ g ∈ t.support, t g * φ (h * g)) := (map_sum σ _ _).symm
      _ = σ (z * φ h) := by rw [e]
      _ = σ z * φ' h := by rw [map_mul, hfin h hh]
  have hon : Set.EqOn (opOf (RU E n) t φ') (σ z • φ') ((ratU E n : Set (UA E n)) * (finU E n : Set (UA E n))) := by
    rintro _ ⟨γ, hγ, g, hg, rfl⟩
    rw [hl1 γ hγ, hl2 γ hγ]
    exact hfinEq g hg
  exact Continuous.ext_on (GlobalTheory.UnitarySplit.dense_and_split E n).1 hc1 hc2 hon

end GlobalTheory.EigenConj
end
end

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryRationalHecke_commute_complexAutomorphism : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ) (t : UA E n →₀ ℂ), (∀ g ∈ t.support, g ∈ finU E n ∧ ∃ q : ℚ, t g = q) → ∀ (φ φ' : UA E n → ℂ) (z : ℂ), IsAutFormU φ → IsAutFormU φ' → (∀ g ∈ finU E n, φ' g = σ (φ g)) → opOf (RU E n) t φ = z • φ → opOf (RU E n) t φ' = σ z • φ' := by
  atlas_forward_decl GlobalTheory.EigenConj.opOf_conj
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
open scoped Pointwise

noncomputable section

namespace GlobalTheory.ConjSpan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def gen (t : (E →+* ℂ) × Fin n × Fin n) : infU E n → ℂ := fun x => (cEmb t.1 x.1).val t.2.1 t.2.2

def mono (l : List ((E →+* ℂ) × Fin n × Fin n)) : infU E n → ℂ := (l.map gen).prod

variable (E n) in

def polys (N : ℕ) : Submodule ℂ (infU E n → ℂ) :=
  Submodule.span ℂ (mono '' {l | l.length ≤ N})

theorem polys_fd (N : ℕ) : FiniteDimensional ℂ (polys E n N) :=
  FiniteDimensional.span_of_finite ℂ ((List.finite_length_le _ N).image _)

theorem polys_mono {N N' : ℕ} (h : N ≤ N') : polys E n N ≤ polys E n N' :=
  Submodule.span_mono (Set.image_mono fun _ hl => le_trans hl h)

variable (E n) in

abbrev gens : Set (infU E n → ℂ) := {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}

theorem exists_mono_of_mem_closure {f : infU E n → ℂ} (hf : f ∈ Submonoid.closure (gens E n)) :
    ∃ l, f = mono l := by
  induction hf using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨τ, i, j, rfl⟩ := hf
    exact ⟨[(τ, i, j)], by funext x; simp [mono, gen]⟩
  | one => exact ⟨[], by simp [mono]⟩
  | mul f g _ _ hf hg =>
    obtain ⟨l, rfl⟩ := hf
    obtain ⟨l', rfl⟩ := hg
    exact ⟨l ++ l', by simp [mono]⟩

theorem exists_polys_of_mem_adjoin {p : infU E n → ℂ} (hp : p ∈ Algebra.adjoin ℂ (gens E n)) :
    ∃ N, p ∈ polys E n N := by
  have h : p ∈ Subalgebra.toSubmodule (Algebra.adjoin ℂ (gens E n)) := hp
  rw [Algebra.adjoin_eq_span] at h
  clear hp
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l, rfl⟩ := exists_mono_of_mem_closure hf
    exact ⟨l.length, Submodule.subset_span ⟨l, (le_refl l.length : l.length ≤ l.length), rfl⟩⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add f g _ _ hf hg =>
    obtain ⟨N, hN⟩ := hf
    obtain ⟨N', hN'⟩ := hg
    exact ⟨max N N', add_mem (polys_mono (le_max_left _ _) hN) (polys_mono (le_max_right _ _) hN')⟩
  | smul c f _ hf =>
    obtain ⟨N, hN⟩ := hf
    exact ⟨N, Submodule.smul_mem _ c hN⟩

theorem mono_mem_adjoin (l : List ((E →+* ℂ) × Fin n × Fin n)) : mono l ∈ Algebra.adjoin ℂ (gens E n) := by
  unfold mono
  induction l with
  | nil => simpa using one_mem (Algebra.adjoin ℂ (gens E n))
  | cons t l ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_mem (Algebra.subset_adjoin ⟨t.1, t.2.1, t.2.2, rfl⟩) ih

theorem polys_le_adjoin (N : ℕ) : polys E n N ≤ Subalgebra.toSubmodule (Algebra.adjoin ℂ (gens E n)) :=
  Submodule.span_le.2 (by rintro _ ⟨l, -, rfl⟩; exact mono_mem_adjoin l)

def conjIdx (σ : ℂ ≃+* ℂ) (t : (E →+* ℂ) × Fin n × Fin n) : (E →+* ℂ) × Fin n × Fin n :=
  (σ.toRingHom.comp t.1, t.2)

theorem mono_conj (σ : ℂ ≃+* ℂ) (l : List ((E →+* ℂ) × Fin n × Fin n)) {γ : UA E n} (hγ : γ ∈ ratU E n)
    (k : infU E n) (hk : cInf k.1 = cInf γ) : mono (l.map (conjIdx σ)) k = σ (mono l k) := by
  induction l with
  | nil => simp [mono]
  | cons t l ih =>
    simp only [mono, List.map_cons, List.prod_cons, Pi.mul_apply] at ih ⊢
    rw [ih, map_mul]
    congr 1
    obtain ⟨x, hx⟩ := exists_cEmb_entry_eq hγ hk t.2.1 t.2.2
    simp only [gen, conjIdx, hx]
    rfl

theorem exists_conj_polys (σ : ℂ ≃+* ℂ) {N : ℕ} {p : infU E n → ℂ} (hp : p ∈ polys E n N) :
    ∃ p' ∈ polys E n N, ∀ γ ∈ ratU E n, ∀ k : infU E n, cInf k.1 = cInf γ → p' k = σ (p k) := by
  induction hp using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l, hl, rfl⟩ := hf
    exact ⟨mono (l.map (conjIdx σ)), Submodule.subset_span ⟨_, by simpa using hl, rfl⟩,
      fun γ hγ k hk => mono_conj σ l hγ k hk⟩
  | zero => exact ⟨0, zero_mem _, fun _ _ _ _ => by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨f', hf', hf⟩ := hf
    obtain ⟨g', hg', hg⟩ := hg
    exact ⟨f' + g', add_mem hf' hg', fun γ hγ k hk => by
      rw [Pi.add_apply, Pi.add_apply, map_add, hf γ hγ k hk, hg γ hγ k hk]⟩
  | smul c f _ hf =>
    obtain ⟨f', hf', hf⟩ := hf
    exact ⟨σ c • f', Submodule.smul_mem _ _ hf', fun γ hγ k hk => by
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, hf γ hγ k hk]⟩

theorem conj_span_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : UA E n → ℂ),
    IsAutFormU φ → ∃ M : Submodule ℂ (UA E n → ℂ), FiniteDimensional ℂ M ∧ ∀ (σ : ℂ ≃+* ℂ) (φ' : UA E n → ℂ),
      IsAutFormU φ' → (∀ g ∈ finU E n, φ' g = σ (φ g)) → φ' ∈ M := by
  intro E _ _ _ n φ hφ
  classical
  obtain ⟨hdense, hdk, -, a, b, -, -, hab, -⟩ := GlobalTheory.UnitarySplit.dense_and_split E n
  obtain ⟨m, p, e, hpe, hdec⟩ := GlobalTheory.UnitaryDecomp.exists_poly_mul_autForm E n φ hφ
  have hcont := (GlobalTheory.PolyRealU.poly_infU E n).1
  choose D hD using fun i => exists_polys_of_mem_adjoin (hpe i).1
  set N := Finset.univ.sup D with hN
  have hpN : ∀ i, p i ∈ polys E n N := fun i => polys_mono (Finset.le_sup (Finset.mem_univ i)) (hD i)
  set K := GlobalTheory.UnitaryDecomp.finStab φ with hK
  obtain ⟨S, hS⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E n K hφ.level
  set S' : Finset (UA E n) := S.image fun s => ((a s : finU E n) : UA E n) with hS'
  let M : Submodule ℂ (UA E n → ℂ) :=
    { carrier := {ψ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧ (∀ k ∈ K, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧
        ∀ s ∈ S', (fun x : infU E n => ψ (s * x)) ∈ polys E n N}
      add_mem' := fun {ψ χ} hψ hχ =>
        ⟨fun γ hγ g => by simp only [Pi.add_apply, hψ.1 γ hγ g, hχ.1 γ hγ g],
          fun k hk g => by simp only [Pi.add_apply, hψ.2.1 k hk g, hχ.2.1 k hk g],
          fun s hs => add_mem (hψ.2.2 s hs) (hχ.2.2 s hs)⟩
      zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => zero_mem _⟩
      smul_mem' := fun c ψ hψ =>
        ⟨fun γ hγ g => by simp only [Pi.smul_apply, hψ.1 γ hγ g],
          fun k hk g => by simp only [Pi.smul_apply, hψ.2.1 k hk g],
          fun s hs => Submodule.smul_mem _ c (hψ.2.2 s hs)⟩ }

  have hred : ∀ g : UA E n, ∃ s ∈ S', ∃ y : infU E n, ∀ ψ ∈ M, ψ g = ψ (s * y) := by
    intro g
    obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hS g
    refine ⟨((a s : finU E n) : UA E n), by rw [hS']; exact Finset.mem_image_of_mem _ hs, ⟨(b s).1 * x, mul_mem (b s).2 hx⟩, fun ψ hψ => ?_⟩
    rw [hψ.2.1 k hk, mul_assoc, hψ.1 γ hγ]
    conv_lhs => rw [hab s]
    simp only [mul_assoc]
  haveI := polys_fd (E := E) (n := n) N
  let f : M →ₗ[ℂ] ((s : S') → polys E n N) :=
    { toFun := fun ψ s => ⟨fun x => ψ.1 (s.1 * x), ψ.2.2.2 s.1 s.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective f := by
    intro ψ χ h
    refine Subtype.ext (funext fun g => ?_)
    obtain ⟨s, hs, y, hy⟩ := hred g
    rw [hy ψ.1 ψ.2, hy χ.1 χ.2]
    exact congrFun (congrArg Subtype.val (congrFun h ⟨s, hs⟩)) y
  refine ⟨M, Module.Finite.of_injective f hinj, fun σ φ' hφ' hagree => ?_⟩

  have hrat : ∀ s ∈ finU E n, ∀ k : infU E n, ∀ γ ∈ ratU E n, cInf k.1 = cInf γ →
      φ' (s * (k : UA E n)) = σ (φ (s * (k : UA E n))) := by
    intro s hs k γ hγ hk
    have hy : γ⁻¹ * (s * (k : UA E n)) ∈ finU E n := by
      have hs1 : cInf s = 1 := hs
      show cInf (γ⁻¹ * (s * (k : UA E n))) = 1
      rw [map_mul, map_mul, map_inv, hs1, hk, one_mul, inv_mul_cancel]
    have e1 : s * (k : UA E n) = γ * (γ⁻¹ * (s * (k : UA E n))) := by group
    rw [e1, hφ'.left γ hγ, hφ.left γ hγ, hagree _ hy]
  refine ⟨hφ'.left, fun k hk => ?_, fun s hs => ?_⟩
  ·
    have hkφ : ∀ x, φ (x * (k : UA E n)) = φ x := fun x => congrFun hk x
    refine congrFun (Continuous.ext_on hdense (hφ'.cont.comp (continuous_mul_const _)) hφ'.cont ?_)
    rintro _ ⟨γ, hγ, x, hx, rfl⟩
    have hxk : x * (k : UA E n) ∈ finU E n := mul_mem hx k.2
    simp only [Function.comp_apply]
    rw [mul_assoc, hφ'.left γ hγ, hφ'.left γ hγ, hagree _ hxk, hagree _ hx, hkφ]
  · obtain ⟨s₀, hs₀, rfl⟩ := Finset.mem_image.1 hs
    have hsf : ((a s₀ : finU E n) : UA E n) ∈ finU E n := (a s₀).2
    choose p' hp'm hp' using fun i => exists_conj_polys σ (hpN i)
    have hq : (∑ i, σ (e i (a s₀)) • p' i) ∈ polys E n N :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hp'm i)
    convert hq using 1
    refine Continuous.ext_on hdk (hφ'.cont.comp (continuous_const.mul continuous_subtype_val))
      (hcont _ (polys_le_adjoin N hq)) ?_
    rintro k ⟨γ, hγ, hk⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hrat _ hsf k γ hγ hk, hdec k, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hp' i γ hγ k hk, mul_comm]

end GlobalTheory.ConjSpan

end
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugates_automorphicForm_span_finiteDimensional : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : UA E n → ℂ), IsAutFormU φ → ∃ M : Submodule ℂ (UA E n → ℂ), FiniteDimensional ℂ M ∧ ∀ (σ : ℂ ≃+* ℂ) (φ' : UA E n → ℂ), IsAutFormU φ' → (∀ g ∈ finU E n, φ' g = σ (φ g)) → φ' ∈ M := by
  first | exact @GlobalTheory.ConjSpan.conj_span_finite | exact GlobalTheory.ConjSpan.conj_span_finite | (intros; apply GlobalTheory.ConjSpan.conj_span_finite; all_goals assumption)
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong

namespace GlobalTheory

theorem orbit_finite_mem_finite_ext : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (J : Type) (z : J → ℂ),
    (Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (z j)).Finite →
      ∃ L : IntermediateField ℚ_[l] (Qbar l), FiniteDimensional ℚ_[l] L ∧ ∀ j, ι.symm (z j) ∈ L := by
  intro l _ ι J z hfin
  classical
  set O := Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (z j) with hO
  haveI : Finite O := hfin.to_subtype
  set w : J → Qbar l := fun j => ι.symm (z j) with hw
  let K : Finset J → IntermediateField ℚ_[l] (Qbar l) := fun s =>
    IntermediateField.adjoin ℚ_[l] (w '' (s : Set J))
  have hKfin : ∀ s, FiniteDimensional ℚ_[l] (K s) := fun s => by
    haveI : Finite (w '' (s : Set J)) := (s.finite_toSet.image w).to_subtype
    exact IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hbound : ∀ s, Module.finrank ℚ_[l] (K s) ≤ Nat.card O := by
    intro s
    haveI := hKfin s
    rw [← AlgHom.card ℚ_[l] (K s) (Qbar l), ← Nat.card_eq_fintype_card]
    let g : (K s →ₐ[ℚ_[l]] Qbar l) → O := fun φ =>
      ⟨fun j => ι (φ.liftNormal (Qbar l) (w j)),
        ι.symm.trans ((AlgEquiv.ofBijective (φ.liftNormal (Qbar l))
          (Algebra.IsAlgebraic.algHom_bijective _)).toRingEquiv.trans ι), rfl⟩
    apply Nat.card_le_card_of_injective g
    intro φ ψ h
    apply IntermediateField.adjoin_algHom_ext
    rintro x ⟨j, hj, rfl⟩
    have h1 := ι.injective (congrFun (congrArg Subtype.val h) j)
    have e1 := AlgHom.liftNormal_commutes φ (Qbar l) ⟨w j, IntermediateField.subset_adjoin _ _ ⟨j, hj, rfl⟩⟩
    have e2 := AlgHom.liftNormal_commutes ψ (Qbar l) ⟨w j, IntermediateField.subset_adjoin _ _ ⟨j, hj, rfl⟩⟩
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at e1 e2
    exact e1.symm.trans (h1.trans e2)
  set R := Set.range fun s : Finset J => Module.finrank ℚ_[l] (K s) with hR
  have hne : R.Nonempty := ⟨_, ∅, rfl⟩
  have hbdd : BddAbove R := ⟨Nat.card O, by rintro _ ⟨s, rfl⟩; exact hbound s⟩
  obtain ⟨s0, hs0⟩ := Nat.sSup_mem hne hbdd
  haveI := hKfin s0
  refine ⟨K s0, inferInstance, fun j => ?_⟩
  have hle : K s0 ≤ K (insert j s0) :=
    IntermediateField.adjoin.mono _ _ _ (Set.image_mono (by simp))
  haveI := hKfin (insert j s0)
  have heq : K s0 = K (insert j s0) := by
    apply IntermediateField.eq_of_le_of_finrank_le hle
    rw [show Module.finrank ℚ_[l] (K s0) = sSup R from hs0]
    exact le_csSup hbdd ⟨insert j s0, rfl⟩
  rw [heq]
  exact IntermediateField.subset_adjoin _ _ ⟨j, by simp, rfl⟩

end GlobalTheory
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_automorphism_orbit_mem_finite_extension_padic : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (J : Type) (z : J → ℂ), (Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (z j)).Finite → ∃ L : IntermediateField ℚ_[l] (Qbar l), FiniteDimensional ℚ_[l] L ∧ ∀ j, ι.symm (z j) ∈ L := by
  first | exact @GlobalTheory.orbit_finite_mem_finite_ext | exact GlobalTheory.orbit_finite_mem_finite_ext | (intros; apply GlobalTheory.orbit_finite_mem_finite_ext; all_goals assumption)
end

section
namespace GlobalTheory.JointEigenvectorsIndependentSatakeParameters

theorem linearIndependent_jointEigenvectors {J V : Type} [AddCommGroup V] [Module ℂ V]
    (T : J → V →ₗ[ℂ] V) (S : Set (J → ℂ)) (v : S → V)
    (hv : ∀ χ : S, v χ ≠ 0)
    (hT : ∀ (χ : S) (j : J), T j (v χ) = (χ : J → ℂ) j • v χ) :
    LinearIndependent ℂ v := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro g _ i hi
    simp at hi
  | insert a s ha ih =>
    intro g hg
    rw [Finset.sum_insert ha] at hg
    have e1 : ∑ i ∈ s, g i • v i = -(g a • v a) := eq_neg_of_add_eq_zero_right hg
    have hs : ∀ i ∈ s, g i = 0 := by
      intro i hi
      have hne : (i : J → ℂ) ≠ a := fun h => ha (Subtype.ext h ▸ hi)
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
      have e2 : ∑ i ∈ s, (g i * (i : J → ℂ) j) • v i = -((g a * (a : J → ℂ) j) • v a) := by
        have := congrArg (T j) e1
        simpa [map_sum, map_smul, hT, smul_smul] using this
      have e3 : ∑ i ∈ s, ((a : J → ℂ) j * g i) • v i = -(((a : J → ℂ) j * g a) • v a) := by
        have := congrArg (fun x => (a : J → ℂ) j • x) e1
        simpa [Finset.smul_sum, smul_smul] using this
      have h2 : ∑ i ∈ s, (g i * ((i : J → ℂ) j - (a : J → ℂ) j)) • v i = 0 := by
        calc ∑ i ∈ s, (g i * ((i : J → ℂ) j - (a : J → ℂ) j)) • v i
            = ∑ i ∈ s, (g i * (i : J → ℂ) j) • v i - ∑ i ∈ s, ((a : J → ℂ) j * g i) • v i := by
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [← sub_smul]
              congr 1
              ring
          _ = 0 := by rw [e2, e3, mul_comm ((a : J → ℂ) j) (g a)]; exact sub_self _
      have := ih (fun i => g i * ((i : J → ℂ) j - (a : J → ℂ) j)) h2 i hi
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hj)
    have hsum : ∑ i ∈ s, g i • v i = 0 := Finset.sum_eq_zero fun i hi => by rw [hs i hi, zero_smul]
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [hsum, add_zero] at hg
      exact (smul_eq_zero.mp hg).resolve_right (hv _)
    · exact hs i hi

end GlobalTheory.JointEigenvectorsIndependentSatakeParameters
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong
open scoped Pointwise

noncomputable section

namespace GlobalTheory.Cong

theorem linearIndependent_simulEigen {J V : Type} [AddCommGroup V] [Module ℂ V] (T : J → V →ₗ[ℂ] V)
    (S : Set (J → ℂ)) (v : S → V) (hv : ∀ χ, v χ ≠ 0)
    (hT : ∀ (χ : S) j, T j (v χ) = (χ : J → ℂ) j • v χ) : LinearIndependent ℂ v := by
  first
  | exact @_root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors
  | exact _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors
  | (apply _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors <;> assumption)
  | (intros; apply _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors <;> assumption)
  | (intros; apply @_root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors ..)

def opLin {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) (f : Γ →₀ ℂ) :
    V →ₗ[ℂ] V :=
  f.sum fun g c => c • ρ g

theorem opLin_apply {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) (f : Γ →₀ ℂ)
    (v : V) : opLin ρ f v = opOf ρ f v := by
  simp [opLin, opOf, Finsupp.sum, LinearMap.sum_apply]

theorem eq_zero_of_finU {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {φ : UA E n → ℂ}
    (hφ : IsAutFormU φ) (h0 : ∀ g ∈ finU E n, φ g = 0) : φ = 0 := by
  refine Continuous.ext_on (GlobalTheory.UnitarySplit.dense_and_split E n).1 hφ.cont continuous_const ?_
  rintro x ⟨γ, hγ, g, hg, rfl⟩
  simp only [Pi.zero_apply]
  rw [hφ.left γ hγ g]
  exact h0 g hg

theorem finU_holds : FinU := by
  intro E _ _ _ l _ ι a _ w₀ K _ lam J t η ht hact U hU
  obtain ⟨φ, hφU, hφ0, hφK⟩ := hU.fix
  have hφ : IsAutFormU φ := hU.aut.aut φ hφU
  have heig : ∀ j, opOf (RU E a) (t j) φ = η U j • φ := fun j => hact U hU.aut φ hφU hφK j
  obtain ⟨g₀, hg₀, hφg₀⟩ : ∃ g ∈ finU E a, φ g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ0 (eq_zero_of_finU hφ h)
  choose φ' hφ' hφ'eq using fun σ : ℂ ≃+* ℂ => exists_conj_isAutFormU E a σ φ hφ
  obtain ⟨M, hMfin, hM⟩ := GlobalTheory.T.conjugates_automorphicForm_span_finiteDimensional E a φ hφ
  have heig' : ∀ σ j, opOf (RU E a) (t j) (φ' σ) = σ (η U j) • φ' σ := fun σ j =>
    GlobalTheory.T.definiteUnitaryRationalHecke_commute_complexAutomorphism E a σ (t j) (ht j) φ (φ' σ) (η U j) hφ (hφ' σ) (hφ'eq σ) (heig j)
  have hne : ∀ σ, φ' σ ≠ 0 := by
    intro σ h
    have e := hφ'eq σ g₀ hg₀
    rw [h, Pi.zero_apply, eq_comm, map_eq_zero_iff σ σ.injective] at e
    exact hφg₀ e
  have hfin : (Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (η U j)).Finite := by
    set S := Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (η U j) with hS
    have hch : ∀ χ : S, ∃ σ : ℂ ≃+* ℂ, (fun j => σ (η U j)) = (χ : J → ℂ) := fun χ => χ.2
    choose sel hsel using hch
    let v : S → (UA E a → ℂ) := fun χ => φ' (sel χ)
    have hli : LinearIndependent ℂ v := by
      refine linearIndependent_simulEigen (fun j => opLin (RU E a) (t j)) S v (fun χ => hne _) ?_
      intro χ j
      rw [opLin_apply, heig', ← hsel χ]
    let v' : S → M := fun χ => ⟨v χ, hM (sel χ) (φ' (sel χ)) (hφ' _) (hφ'eq _)⟩
    have hli' : LinearIndependent ℂ v' := LinearIndependent.of_comp M.subtype hli
    have : Finite S := hli'.finite
    exact Set.toFinite S
  obtain ⟨L, hL, hLmem⟩ := GlobalTheory.T.finite_automorphism_orbit_mem_finite_extension_padic l ι J (η U) hfin
  exact ⟨⟨L, hL⟩, hLmem⟩

end GlobalTheory.Cong
end
end
