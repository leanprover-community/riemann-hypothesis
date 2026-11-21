import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.FilZeroEqRangeCDAndCDInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSumTmul

section
open TensorProduct

theorem _root_.UpperTheory.KN.coeff_eq_zero_of_sum_tmul_linearIndependent_eq_zero :
    ∀ (K V C ι : Type) [Field K] [AddCommGroup V] [Module K V] [AddCommGroup C] [Module K C] [Fintype ι] (v : ι → V), LinearIndependent K v → ∀ c : ι → C, ∑ i, v i ⊗ₜ[K] c i = 0 → ∀ i, c i = 0 := by
  intro K V C ι _ _ _ _ _ _ v hv c hsum i
  classical
  obtain ⟨f, hf⟩ := LinearMap.exists_extend ((Module.Basis.span hv).coord i)
  have hfv : ∀ j, f (v j) = if j = i then 1 else 0 := by
    intro j
    have h1 : f (v j) = (Module.Basis.span hv).coord i ⟨v j, Submodule.subset_span ⟨j, rfl⟩⟩ := by
      rw [← hf]
      rfl
    rw [h1, ← Module.Basis.span_apply hv j, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
  have h2 := congrArg (⇑((TensorProduct.lid K C).toLinearMap ∘ₗ TensorProduct.map f LinearMap.id)) hsum
  simp only [map_sum, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_coe, TensorProduct.lid_tmul, hfv, map_zero] at h2
  simpa using h2
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem linearIndependent_smul_basis_pairs {Z Q O L V κ σ : Type*} [CommRing Z] [Field Q] [Algebra Z Q] [IsFractionRing Z Q]
    [CommRing O] [Field L] [Algebra O L] [Algebra Z O] [Algebra Q L] [Algebra Z L]
    [IsScalarTower Z O L] [IsScalarTower Z Q L] [AddCommGroup V] [Module L V] [Module O V] [Module Q V]
    [IsScalarTower O L V] [IsScalarTower Q L V] (M : Submodule O V) (b : Module.Basis κ O M)
    (ω : Module.Basis σ Z O) :
    LinearIndependent Q (fun p : σ × κ => (algebraMap O L (ω p.1)) • ((b p.2 : M) : V)) := by
  letI : Module Z V := Module.compHom V (algebraMap Z L)
  haveI : IsScalarTower Z Q V := ⟨fun z q v => by
    show (z • q) • v = algebraMap Z L z • (q • v)
    rw [← algebraMap_smul L (z • q) v, ← algebraMap_smul L q v, smul_smul, Algebra.smul_def z q,
      map_mul, ← IsScalarTower.algebraMap_apply Z Q L]⟩
  haveI : IsScalarTower Z O V := ⟨fun z o v => by
    show (z • o) • v = algebraMap Z L z • (o • v)
    rw [Algebra.smul_def z o, mul_smul, ← algebraMap_smul L (algebraMap Z O z) (o • v),
      ← IsScalarTower.algebraMap_apply Z O L]⟩
  have hc : LinearIndependent O (fun k => ((b k : M) : V)) :=
    b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hZ : LinearIndependent Z (fun p : σ × κ => ω p.1 • ((b p.2 : M) : V)) :=
    linearIndependent_smul ω.linearIndependent hc
  have hQ := (LinearIndependent.iff_fractionRing Z Q).mp hZ
  have hf : (fun p : σ × κ => (algebraMap O L (ω p.1)) • ((b p.2 : M) : V)) =
      fun p => ω p.1 • ((b p.2 : M) : V) := funext fun p => algebraMap_smul L (ω p.1) _
  rw [hf]
  exact hQ


theorem _root_.UpperTheory.KN.linearIndependent_Ql_integerBasis_smul_latticeBasis :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (κ σ : Type) [Fintype κ] [Fintype σ] (b : Module.Basis κ ↥(OL LL) ↥T.L.T) (ω : Module.Basis σ ℤ_[l] ↥(OL LL)), LinearIndependent ℚ_[l] (fun p : σ × κ => ((ω p.1 : ↥(OL LL)) : ↥LL.1) • ((b p.2 : ↥T.L.T) : T.V)) := by
  intro l _ LL T κ σ _ _ b ω
  exact linearIndependent_smul_basis_pairs (Z := ℤ_[l]) (Q := ℚ_[l]) (L := ↥LL.1) T.L.T b ω
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem exists_sum_tmul {R O B σ : Type} [CommRing R] [AddCommGroup O] [Module R O]
    [AddCommGroup B] [Module R B] [Fintype σ] (ω : Module.Basis σ R O) (x : O ⊗[R] B) :
    ∃ y : σ → B, x = ∑ s, ω s ⊗ₜ[R] y s :=
  _root_.UpperTheory.Reformulated.B.Qj2.exists_sum_tmul ω x

private theorem abstract_indep {R K O B V C σ κ : Type} [CommRing R] [Field K] [AddCommGroup O]
    [Module R O] [AddCommGroup B] [Module R B] [AddCommGroup V] [Module K V] [AddCommGroup C]
    [Module K C] [Fintype σ] [Fintype κ] (ω : Module.Basis σ R O)
    (act : O ⊗[R] B →+ (V ⊗[K] C →+ V ⊗[K] C)) (e : κ → V ⊗[K] C) (w : σ × κ → V) (f : B → C)
    (hf : ∀ y, f y = 0 → y = 0) (hw : LinearIndependent K w)
    (hact : ∀ s k y, act (ω s ⊗ₜ[R] y) (e k) = w (s, k) ⊗ₜ[K] f y)
    (d : κ → O ⊗[R] B) (hd : ∑ k, act (d k) (e k) = 0) (k : κ) : d k = 0 := by
  choose y hy using fun k => exists_sum_tmul ω (d k)
  have h : ∑ p : σ × κ, w p ⊗ₜ[K] f (y p.2 p.1) = 0 := by
    rw [← hd, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hy k, map_sum, AddMonoidHom.finset_sum_apply]
    exact Finset.sum_congr rfl fun s _ => (hact s k _).symm
  have h0 := UpperTheory.KN.coeff_eq_zero_of_sum_tmul_linearIndependent_eq_zero K V C (σ × κ) w hw _ h
  rw [hy k]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [hf _ (h0 (s, k)), TensorProduct.tmul_zero]

theorem _root_.UpperTheory.KN.linearIndependent_Ql_productBasis_of_Zl_lattice :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (κ : Type) [Fintype κ] (b : Module.Basis κ ↥(OL LL) ↥T.L.T), ∀ d : κ → OD l ↥(OL LL), ∑ k, act (d k) (((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) = 0 → ∀ k, d k = 0 := by
  intro l _ LL T Pl AI Td act hact κ _ b d hd k
  haveI : Module.Free ℤ_[l] ↥(OL LL) := inferInstance
  haveI : Module.Finite ℤ_[l] ↥(OL LL) := inferInstance
  have hinj := (UpperTheory.KN.fil_zero_eq_range_cD_and_cD_injective l Pl AI Td LL).2
  refine abstract_indep (Module.Free.chooseBasis ℤ_[l] ↥(OL LL)) act
    (fun k => ((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) _
    (fun y => GlobalTheory.BKGal.JumpDR.cD Td y) (fun y hy => hinj (hy.trans (map_zero _).symm))
    (UpperTheory.KN.linearIndependent_Ql_integerBasis_smul_latticeBasis l LL T κ _ b (Module.Free.chooseBasis ℤ_[l] ↥(OL LL))) ?_ d hd k
  intro s k y
  refine (hact _ _ _ _).trans ?_
  rw [mul_one]
end
