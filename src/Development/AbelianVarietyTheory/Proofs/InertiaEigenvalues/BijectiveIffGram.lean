import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnitDualParts
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GammaStableInverse
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.WachLettersFree
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisMul

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
