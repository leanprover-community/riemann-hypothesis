import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnitDualParts
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GammaStableInverse
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.WachLettersFree
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisDD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfFrobeniusEquationCyclotomicFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineQuotientTensorDual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitForOfTie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumPart

section
noncomputable section

namespace GlobalTheory.WachTensor

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts GlobalTheory.EtaleExact
open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation (QuotCrys TensorCrys DualCrys)
open GlobalTheory.IndefiniteRowSideFullHecke.GammaStableInverse GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

theorem bil_expand {R M M' M'' : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] [AddCommGroup M''] [Module R M''] (b : M →ₗ[R] M' →ₗ[R] M'') {ι κ : Type}
    [Fintype ι] [Fintype κ] (u : ι → R) (x : ι → M) (u' : κ → R) (y : κ → M') :
    b (∑ i, u i • x i) (∑ k, u' k • y k) = ∑ q : ι × κ, (u q.1 * u' q.2) • b (x q.1) (y q.2) := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Fintype.sum_prod_type, mul_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => smul_comm _ _ _

theorem exists_frob_mat (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤)
    (hφ : Function.Surjective φR) (T : LocLat G Qp LL O) {ι : Type} [Fintype ι]
    (e : Module.Basis ι W.EE (W.DD T)) : ∃ U : ι → ι → W.EE, ∀ a,
      E.jD T (e a) = ∑ b, E.ioE (U a b) • TWmap φR T (E.jD T (e b)) := by
  choose U hU using fun a => (Submodule.mem_span_range_iff_exists_fun W.EE).1
    ((exists_frob_inv E hm hφ T e).ge (Submodule.mem_top (x := e a)))
  refine ⟨U, fun a => ?_⟩
  conv_lhs => rw [← hU a, map_sum]
  exact Finset.sum_congr rfl fun b _ => by rw [E.jD_smul, E.jD_φ]

theorem exists_bases {T : LocLat G Qp LL O} {r : ℕ} {b : Fin r → W.DD T} (hb : IsWachBasis W T b) :
    ∃ (e : Module.Basis (Fin r) W.EE (W.DD T)) (c : Module.Basis (Fin r) (LetA O n) ↥(W.N T)),
      ∀ i, e i = (c i : W.DD T) := by
  obtain ⟨h1, h2, h3, h4⟩ := hb
  refine ⟨Module.Basis.mk h3 h4.ge, (Module.Basis.span h1).map (LinearEquiv.ofEq _ _ h2), fun i => ?_⟩
  simp [Module.Basis.span_apply]


theorem exists_mul (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤)
    (hφ : Function.Surjective φR) (hd : Descends E) {T T' T'' : LocLat G Qp LL O}
    (m : ↥T.L.T ⊗[O] ↥T'.L.T ≃ₗ[O] ↥T''.L.T) (hmt : IsTensorLat m) :
    ∃ μ : W.DD T →ₗ[W.EE] W.DD T' →ₗ[W.EE] W.DD T'',
      ∀ x y, E.jD T'' (μ x y) = mulL RW m.toLinearMap (E.jD T x) (E.jD T' y) := by
  obtain ⟨e⟩ := exists_basis_DD E T
  obtain ⟨e'⟩ := exists_basis_DD E T'
  obtain ⟨U, hU⟩ := exists_frob_mat E hm hφ T e
  obtain ⟨U', hU'⟩ := exists_frob_mat E hm hφ T' e'
  have hact : ∀ (g : G) (x : TW RW T) (y : TW RW T'),
      TWact (gR g) T'' g (mulL RW m.toLinearMap x y) =
        mulL RW m.toLinearMap (TWact (gR g) T g x) (TWact (gR g) T' g y) := fun g x y =>
    map_mulL RW m.toLinearMap (gR g) (T.actT g) (T'.actT g) (T''.actT g) (hmt g) x y
  have hfr : ∀ (x : TW RW T) (y : TW RW T'), TWmap φR T'' (mulL RW m.toLinearMap x y) =
      mulL RW m.toLinearMap (TWmap φR T x) (TWmap φR T' y) := fun x y =>
    map_mulL RW m.toLinearMap φR LinearMap.id LinearMap.id LinearMap.id (fun _ _ => rfl) x y
  generalize mulL RW m.toLinearMap = b at hact hfr ⊢
  have key := mem_range_jD E hd T''
    (ι := Fin (Module.finrank O ↥T.L.T) × Fin (Module.finrank O ↥T'.L.T))
    (fun p q => U p.1 q.1 * U' p.2 q.2) (fun p => b (E.jD T (e p.1)) (E.jD T' (e' p.2)))
    (fun g hg p => by simp only [hact, jD_fixed E T g hg, jD_fixed E T' g hg])
    (fun p => by
      simp only [hfr, map_mul]
      rw [← bil_expand b (fun b => E.ioE (U p.1 b))
        (fun b => TWmap φR T (E.jD T (e b))) (fun b => E.ioE (U' p.2 b))
        (fun b => TWmap φR T' (E.jD T' (e' b))), ← hU, ← hU'])
  exact exists_descend E.ioE (E.jD T).toAddMonoidHom (E.jD T').toAddMonoidHom
    (E.jD T'').toAddMonoidHom (E.jD_smul T) (E.jD_smul T') (E.jD_smul T'') (E.jD_inj T'')
    b e e' fun a c => key (a, c)



end GlobalTheory.WachTensor
end
end

section
noncomputable section

namespace GlobalTheory.WachTensor

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts GlobalTheory.EtaleExact
open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation (QuotCrys TensorCrys DualCrys)
open GlobalTheory.IndefiniteRowSideFullHecke.GammaStableInverse GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness


variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

theorem flip_bijective {T T' : LocLat G Qp LL O} {Pr : T.V →ₗ[LL] T'.V →ₗ[LL] LL}
    (h : IsDualLat T.L T'.L Pr) : Function.Bijective Pr.flip := by
  have h1 : Function.Injective Pr.flip :=
    (injective_iff_map_eq_zero _).2 fun y hy => h.2.2.1 y fun x => LinearMap.congr_fun hy x
  refine ⟨h1, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 h1⟩
  rw [← h.2.2.2.1]
  exact (Subspace.dual_finrank_eq (K := LL) (V := T.V)).symm

theorem isCrys_dual (hq : QuotCrys PD LL) (hdu : DualCrys PD LL) {T T' : LocLat G Qp LL O}
    (hT : IsCrys PD T.ρ) {Pr : T.V →ₗ[LL] T'.V →ₗ[LL] LL} (h : IsDualLat T.L T'.L Pr) :
    IsCrys PD T'.ρ := by
  let ε := LinearEquiv.ofBijective Pr.flip (flip_bijective h)
  refine hq _ T.ρ.dual _ T'.ρ ε.symm.toLinearMap ?_ ε.symm.surjective (hdu _ _ hT)
  intro g f
  obtain ⟨y, rfl⟩ := ε.surjective f
  rw [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_eq]
  ext x
  change Pr (T.ρ g⁻¹ x) y = Pr x (T'.ρ g y)
  rw [← h.1 g, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]


theorem exists_pair (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤)
    (hφ : Function.Surjective φR) (hd : Descends E) {T T' : LocLat G Qp LL O}
    (β : ↥T.L.T →ₗ[O] ↥T'.L.T →ₗ[O] O) (hβ : ∀ g x y, β (T.actT g x) (T'.actT g y) = β x y) :
    ∃ b : W.DD T →ₗ[W.EE] W.DD T' →ₗ[W.EE] W.EE,
      ∀ x y, E.ioE (b x y) = pairL RW β (E.jD T x) (E.jD T' y) := by
  obtain ⟨e⟩ := exists_basis_DD E T
  obtain ⟨e'⟩ := exists_basis_DD E T'
  obtain ⟨U, hU⟩ := exists_frob_mat E hm hφ T e
  obtain ⟨U', hU'⟩ := exists_frob_mat E hm hφ T' e'
  have hact : ∀ (g : G) (x : TW RW T) (y : TW RW T'), gR g (pairL RW β x y) =
      pairL RW β (TWact (gR g) T g x) (TWact (gR g) T' g y) := fun g x y =>
    map_pairL RW β (gR g) (T.actT g) (T'.actT g) (hβ g) x y
  have hfr : ∀ (x : TW RW T) (y : TW RW T'), φR (pairL RW β x y) =
      pairL RW β (TWmap φR T x) (TWmap φR T' y) := fun x y =>
    map_pairL RW β φR LinearMap.id LinearMap.id (fun _ _ => rfl) x y
  generalize pairL RW β = b at hact hfr ⊢
  have key := hd (Fin (Module.finrank O ↥T.L.T) × Fin (Module.finrank O ↥T'.L.T))
    (fun p q => U p.1 q.1 * U' p.2 q.2) (fun p => b (E.jD T (e p.1)) (E.jD T' (e' p.2)))
    (fun g hg p => by simp only [hact, jD_fixed E T g hg, jD_fixed E T' g hg])
    (fun p => by
      simp only [hfr, map_mul, ← smul_eq_mul (α := RW) (_ * _)]
      rw [← bil_expand b (fun b => E.ioE (U p.1 b))
        (fun b => TWmap φR T (E.jD T (e b))) (fun b => E.ioE (U' p.2 b))
        (fun b => TWmap φR T' (E.jD T' (e' b))), ← hU, ← hU'])
  exact exists_descend E.ioE (E.jD T).toAddMonoidHom (E.jD T').toAddMonoidHom
    E.ioE.toRingHom.toAddMonoidHom (E.jD_smul T) (E.jD_smul T') (fun a x => map_mul E.ioE a x)
    (ioE_injective E) b e e' fun a c => key (a, c)




end GlobalTheory.WachTensor
end
end

section
set_option synthInstance.maxHeartbeats 400000
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_range_of_frobeniusEquation_cyclotomicFixed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) (E : EtSit P AI K s LL h W) (ι : Type) [Fintype ι] (M : ι → ι → W.EE) (c : ι → W.EE) (w : ι → RW LL), (∀ g : ↥(GK K), W.resΓ g = 1 → ∀ i, AI.gRW LL (g : GQ l) (w i) = w i) → (∀ i, w i = ∑ j, E.tie.ioE (M i j) * φRW LL (w j) + E.tie.ioE (c i)) → ∀ i, ∃ e : W.EE, E.tie.ioE e = w i := by
  first | exact @GlobalTheory.FrobDescent.mem_range_of_fixed | exact GlobalTheory.FrobDescent.mem_range_of_fixed | (intros; apply GlobalTheory.FrobDescent.mem_range_of_fixed <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_quotient_tensor_dual : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), GlobalTheory.Per.IsStd P AI → GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.LocQuotCrys l P ∧ GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.LocTensorCrys l P ∧ GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.LocDualCrys l P := by
  first | exact @GlobalTheory.RegularRing.quot_tensor_dual_crys | exact GlobalTheory.RegularRing.quot_tensor_dual_crys | (intros; apply GlobalTheory.RegularRing.quot_tensor_dual_crys <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.WachTensor

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts GlobalTheory.EtaleExact
open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation (LocQuotCrys LocTensorCrys LocDualCrys)

set_option synthInstance.maxHeartbeats 400000

variable {l : ℕ} [Fact l.Prime]

private theorem frobW_surjective_lemma : Function.Surjective (frobW l) := by
  have hC : IsAlgClosed (Cb l) := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1
  have hf : Function.Surjective (frobenius (Cb l) l) := by
    first
      | exact surjective_frobenius (Cb l) l
      | exact (bijective_frobenius (Cb l) l).2
      | exact fun y => ⟨(frobeniusEquiv (Cb l) l).symm y, by simp⟩
  intro y
  obtain ⟨x, hx⟩ := WittVector.map_surjective (p := l) _ hf y
  unfold frobW
  exact ⟨x, hx⟩

theorem φRW_surjective (LL : FinExt l) : Function.Surjective (φRW LL) := by
  have hg : Function.Surjective (frobW l).toLinearMap := frobW_surjective_lemma
  intro y
  obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective (↥(OL LL)) hg y
  refine ⟨x, ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [φRW]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem isFractionRing_OL (LL : FinExt l) : IsFractionRing ↥(OL LL) ↥LL.1 := by
  have : FiniteDimensional ℚ_[l] LL.1 := LL.2
  unfold OL
  exact integralClosure.isFractionRing_of_finite_extension ℚ_[l] _

theorem map_ne_top {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l}
    {h : Good K s LL}
    {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
    (E : EtSit P AI K s LL h W) (m : Ideal W.EE) (hm : m.IsMaximal) :
    m.map E.tie.ioE.toRingHom ≠ ⊤ := by
  have : Module.Finite ℤ_[l] ↥(OL LL) := GlobalTheory.EtaleExact.finite_OL LL
  have : IsNoetherianRing ↥(OL LL) := by
    first
      | infer_instance
      | exact isNoetherian_of_tower ℤ_[l] inferInstance
  refine GlobalTheory.EtaleExact.map_ne_top_of_tie E.tie (fun c => ?_) (fun x hx => ?_) m hm
  · rw [P.PD_p K]
    exact GlobalTheory.EtaleExact.isUnit_or_dvd_pow P LL c
  · exact GlobalTheory.EtaleExact.sep_RW LL x (by simpa [P.PD_p K] using hx)

theorem descends {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l}
    {h : Good K s LL}
    {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
    (E : EtSit P AI K s LL h W) : Descends E.tie := by
  intro ι _ M w hg hw i
  exact GlobalTheory.T.mem_range_of_frobeniusEquation_cyclotomicFixed l P AI K s LL h W E ι M 0 w hg (fun i => by simpa using hw i) i



end GlobalTheory.WachTensor
end
end
