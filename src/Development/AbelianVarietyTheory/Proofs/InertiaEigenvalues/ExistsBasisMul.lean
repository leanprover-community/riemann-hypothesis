import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnitDualParts
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GammaStableInverse
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.WachLettersFree
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisDD

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
