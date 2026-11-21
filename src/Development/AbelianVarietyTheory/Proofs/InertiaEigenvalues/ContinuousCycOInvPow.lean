import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.ReindexedFiltrationComparison
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete

noncomputable section

namespace GlobalTheory.AdmLoc.CycWitness

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct

section Line

variable {G Qp LL R : Type} [Group G] [Field Qp] [Field LL] [Algebra Qp LL] [CommRing R] [Algebra Qp R]

theorem mem_of_tmul_mem (S : Submodule Qp R) {v : LL} (hv : v ≠ 0) {r : R}
    (h : v ⊗ₜ[Qp] r ∈ LinearMap.range
      (AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL) S.subtype)) : r ∈ S := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one Qp hv
  let m : LL ⊗[Qp] R →ₗ[Qp] R := (TensorProduct.lid Qp R).toLinearMap ∘ₗ φ.rTensor R
  have hm : ∀ y, m (AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL) S.subtype y) ∈ S := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v c => simpa [m] using S.smul_mem (φ v) c.2
    | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  have := hm y
  rw [hy] at this
  simpa [m, hφ] using this


theorem fixed_iff (act : G → R →ₗ[Qp] R) (hmul : ∀ g x y, act g (x * y) = act g x * act g y)
    (hinv : ∀ b, (∀ g, act g b = b) → ∃ q : Qp, algebraMap Qp R q = b) {u : R} (hu : IsUnit u)
    (c : G → Qp) (hc : ∀ g, c g • act g u = u) (θ : G →* LLˣ)
    (hθ : ∀ g, (θ g : LL) = algebraMap Qp LL (c g)) (x : LL ⊗[Qp] R) :
    (∀ g, AlgebraTensorModule.map (charRep θ g) (act g) x = x) ↔
      x ∈ Submodule.span LL {(1 : LL) ⊗ₜ[Qp] u} := by
  classical
  have ht : ∀ g (v : LL) (r : R), AlgebraTensorModule.map (charRep θ g) (act g) (v ⊗ₜ[Qp] r) =
      v ⊗ₜ[Qp] (c g • act g r) := by
    intro g v r
    rw [AlgebraTensorModule.map_tmul, ← smul_tmul]
    congr 1
    change (θ g : LL) • v = _
    rw [hθ, algebraMap_smul]
  constructor
  · intro hx
    let b := Module.Basis.ofVectorSpace Qp LL
    let e := TensorProduct.equivFinsuppOfBasisLeft (N := R) b
    have he : ∀ g y i, e (AlgebraTensorModule.map (charRep θ g) (act g) y) i = c g • act g (e y i) := by
      intro g y i
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v r =>
        rw [ht]
        simp only [e, equivFinsuppOfBasisLeft_apply_tmul_apply, map_smul]
        rw [smul_comm]
      | add a b ha hb => simp only [map_add, Finsupp.add_apply, ha, hb, smul_add]
    have hx' : x = (e x).sum fun i c => b i ⊗ₜ[Qp] c := by
      rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
      exact (e.symm_apply_apply x).symm
    rw [hx']
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨z, hz⟩ : ∃ z, e x i = z * u := ⟨e x i * ↑hu.unit⁻¹, by simp [mul_assoc]⟩
    obtain ⟨q, rfl⟩ := hinv z fun g => hu.mul_right_cancel (by
      have h := he g x i
      rw [hx, hz, hmul, ← mul_smul_comm, hc] at h
      exact h.symm)
    refine Submodule.mem_span_singleton.2 ⟨q • b i, ?_⟩
    rw [hz, ← Algebra.smul_def, smul_tmul', smul_eq_mul, mul_one, smul_tmul]
  · intro hx g
    obtain ⟨v, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [map_smul, ht, hc]

end Line

section Per

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]



variable (hK : Function.Surjective (algebraMap Qp K)) (a : ℕ) (θ : G →* LLˣ)
  (hθ : ∀ g, (θ g : LL) = algebraMap Qp LL (((PD.χ g)⁻¹ ^ a : Qpˣ) : Qp))

include hK in
theorem surj_K₀ : Function.Surjective (algebraMap Qp K₀) := fun x => by
  obtain ⟨q, hq⟩ := hK (algebraMap K₀ K x)
  exact ⟨q, (algebraMap K₀ K).injective (by rw [← hq, ← IsScalarTower.algebraMap_apply])⟩

include hK hθ




end Per

def lowData (t : ℕ) (h1 : 1 ≤ t) (h4 : t ≤ 4) : TopData 1 1 where
  h := fun _ => 12
  η := fun _ => 10
  ty := fun _ => LType.G
  w := fun _ => 1
  t := t
  lows := fun _ => {7}
  cloud := fun _ => 0
  two_le_h := fun _ => by norm_num
  one_le_η := fun _ => by norm_num
  one_le_letterBlockLength := h1
  card_eq := fun _ => by simp
  range := fun _ u hu => by simp [mem_block] at hu; push_cast; omega
  lowG := fun _ _ u hu => by simp [mem_block] at hu; push_cast; omega
  cloudG := fun _ _ u hu => by simp at hu
  lowBd := fun _ h => by cases h
  cloudBd := fun _ h => by cases h



variable {l : ℕ} [Fact l.Prime]

def cycO (P : LocPrime l) (K LL : FinExt l) : ↥(GK K) →* (↥(OL LL))ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => ⟨_, GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.cyc_mem P K LL g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp) }

theorem cycO_val (P : LocPrime l) (K LL : FinExt l) (g : ↥(GK K)) :
    algebraMap ↥(OL LL) ↥LL.1 (cycO P K LL g) = algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ g) := rfl







end GlobalTheory.AdmLoc.CycWitness
