import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFinitenessStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaOfFiltrationStatement
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GeometricSplitting.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSupportRealisedByProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankProductLeOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankExtensionBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSwapProductGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerHeredity.Replay
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.WhitCuspOfSegCuspGeneric
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.CuspidalGenericity.Bridge
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.UnlinkedIrreducibility.LUnlinkedIrrOfHeredity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedLayersHold
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSegmentRepresentationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentGenericOfJacquetNuPair
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredityGenericProductStatement
import GroundTheory.PAdicHodge.AInfGalois
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.NuPairInjectivity.NuPair
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAll

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.RgGu

theorem suppExists (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    SuppExists k := by
  intro N V _ _ π hs hi
  have hG : GlobalTheory.Published.GeometricLemma := GlobalTheory.T.geometricLemma_of_bzFiniteness_of_filtration GlobalTheory.T.bernstein_zelevinsky_finiteness PositivityTheory.Geo.geometricLemmaFiltration
  obtain ⟨s, h⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport GlobalTheory.T.bernstein_zelevinsky_finiteness hG (IrrGL.of π hs hi)
  exact ⟨s, h.of_equiv (IrrGL.equivOf π hs hi).symm⟩

theorem genericUnlinkedGL_of
    (hS : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
      SuppExists k)
    (hU : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
      GenericUnique k)
    (hR : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
      UnlinkedRealize k) :
    GlobalTheory.Published.GenericUnlinkedGL := by
  intro k _ _ _ _ _ N V _ _ π hs hi hg
  obtain ⟨s, hsupp⟩ := hS k N V π hs hi
  have hsum : (s.map Sigma.fst).sum = N := by simpa using hsupp.sum_fst
  obtain ⟨h, Δ, x, hd, hΔ, hL, hx, hxg⟩ := hR k N s (fun y hy => hsupp.isCusp hy) hsum
  exact ⟨h, Δ, x, hd, hΔ, hL, hU k N s V _ π (prodIrr x hd) hsupp hx hg hxg⟩

end GlobalTheory.RgGu

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.RgGu

theorem exists_equiv_of_map_univ_eq {α : Type*} {h h' : ℕ} (x : Fin h → α) (y : Fin h' → α)
    (H : Finset.univ.val.map x = Finset.univ.val.map y) : ∃ e : Fin h ≃ Fin h', ∀ a, y (e a) = x a := by
  classical
  have hc : ∀ v, Fintype.card {a // x a = v} = Fintype.card {b // y b = v} := fun v => by
    have := congrArg (Multiset.count v) H
    simp only [Multiset.count_map] at this
    simp only [Fintype.card_subtype, Finset.card_def, Finset.filter_val, eq_comm (b := v)]
    exact this
  exact ⟨Equiv.ofFiberEquiv fun v => Fintype.equivOfCardEq (hc v), fun a => Equiv.ofFiberEquiv_map _ a⟩

theorem genericUnique_of_perm {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hH : GlobalTheory.BZMir.Leib.WhitHeredity k) (hW : GlobalTheory.BZSeg.WhitRankIrr k)
    (hC : GlobalTheory.BZSeg.CuspGeneric k)
    (hP : GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k → GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → GlobalTheory.BZSeg.CuspGeneric k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ {h N : ℕ} (x : Fin h → IrrGL k), (∀ a, (x a).IsCusp) → ∀ (hd : ∑ a, (x a).1 = N) (τ : Equiv.Perm (Fin h)) (hd' : ∑ a, (x (τ a)).1 = N) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible → IsGenericFor ψ σ → IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (τ a)) hd')) :
    GenericUnique k := by
  intro N s V W _ _ _ _ π σ hπ hσ gπ gσ
  obtain ⟨ψ, hψc, hψ1, gπψ⟩ := gπ
  have gσψ : IsGenericFor ψ σ := (isGeneric_iff_isGenericFor hψc hψ1 σ).1 gσ
  obtain ⟨h, x, hd, hxs, hxc, hπx⟩ := GlobalTheory.T.cuspidal_support_realised_by_product k π s hπ
  obtain ⟨h', y, hd', hys, hyc, hσy⟩ := GlobalTheory.T.cuspidal_support_realised_by_product k σ s hσ
  obtain ⟨e, he⟩ := exists_equiv_of_map_univ_eq x y (hxs.trans hys.symm)
  have hh : h = h' := by simpa using Fintype.card_congr e
  subst hh
  have hfun : (fun a => y (e a)) = x := funext he
  subst hfun
  have hσx : IsSubquotient σ (prodIrr (fun a => y (e a)) hd) :=
    hP hA (GlobalTheory.T.gelfand_kazhdan_local hA) hH hW hC ψ hψc hψ1 y hyc hd' e hd σ hσ.isSmooth hσ.isIrreducible gσψ hσy
  exact GlobalTheory.T.whittaker_rank_extension_bound k ψ hψc N (prodIrr (fun a => y (e a)) hd) π σ (isSmooth_prodIrr _ hd)
    (GlobalTheory.T.whittaker_rank_product_le_one k hH hW ψ hψc hψ1 h N _ hd) hπ.isIrreducible hσ.isIrreducible hπx hσx gπψ gσψ

theorem perm_abs {α : Type 1} {h : ℕ} (P : (Fin h → α) → Prop)
    (hP : ∀ (y : Fin h → α) (j : ℕ) (hj : j + 1 < h), P y → P fun a => y (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a))
    (x : Fin h → α) (hx : P x) (τ : Equiv.Perm (Fin h)) : P fun a => x (τ a) := by
  rcases h with _ | n
  · obtain rfl : τ = 1 := Subsingleton.elim _ _
    exact hx
  have hτ : τ ∈ Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
  induction hτ using Submonoid.closure_induction_right with
  | one => exact hx
  | mul_right t ht s hs' ih =>
    obtain ⟨i, rfl⟩ := hs'
    exact hP (fun a => x (t a)) i.1 (by omega) ih

theorem perm_of_swap : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k → GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → GlobalTheory.BZSeg.CuspGeneric k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ {h N : ℕ} (x : Fin h → IrrGL k), (∀ a, (x a).IsCusp) → ∀ (hd : ∑ a, (x a).1 = N) (τ : Equiv.Perm (Fin h)) (hd' : ∑ a, (x (τ a)).1 = N) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible → IsGenericFor ψ σ → IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (τ a)) hd') := by
  intro k _ _ _ _ hA hG hH hW hC ψ hc h1 h N x hx hd τ hd' W _ _ σ hs hi hg hσ
  let P : (Fin h → IrrGL k) → Prop := fun y =>
    (∀ a, (y a).IsCusp) ∧ ∃ e : ∑ a, (y a).1 = N, IsSubquotient σ (prodIrr y e)
  have step : ∀ (y : Fin h → IrrGL k) (j : ℕ) (hj : j + 1 < h), P y →
      P fun a => y (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a) := by
    rintro y j hj ⟨c, e, H⟩
    have e' : ∑ a, (y (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)).1 = N :=
      (Equiv.sum_comp (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩) fun a => (y a).1).trans e
    exact ⟨fun a => c _, e', @GlobalTheory.T.cuspidal_swap_product_generic k _ _ _ _ hA hG hH hW hC ψ hc h1 h N y c e j hj e' W _ _ σ hs hi hg H⟩
  obtain ⟨-, e, H⟩ := perm_abs P step x ⟨hx, hd, hσ⟩ τ
  exact H

theorem genericUnique_of {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hH : GlobalTheory.BZMir.Leib.WhitHeredity k) (hW : GlobalTheory.BZSeg.WhitRankIrr k)
    (hC : GlobalTheory.BZSeg.CuspGeneric k) : GenericUnique k :=
  genericUnique_of_perm hA hH hW hC (@perm_of_swap k _ _ _ _)

end GlobalTheory.RgGu

end
end

section
namespace GlobalTheory.RgGu

theorem genericUnique (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GenericUnique k :=
  genericUnique_of PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top (PositivityTheory.rg.gu.hered2.whitHeredity_all k)
    (PositivityTheory.rg.gu.whit.whitRankIrr k) (GlobalTheory.BZSeg.Cusp.cuspGeneric k)

end GlobalTheory.RgGu
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.RgGu

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sum_map_fst_ms (Δ : Segment k) : (Δ.ms.map Sigma.fst).sum = Δ.deg := by
  rw [Segment.ms, Multiset.map_map, ← Δ.sum_term_fst]
  rfl

theorem unlinkedRealize_of (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hL : GlobalTheory.BZSeg.LUnlinkedIrr k)
    (hG : GlobalTheory.BZSeg.LSegGeneric k) (hP : GlobalTheory.BZMir.Leib.GenericProdIff k) : UnlinkedRealize k := by
  intro N s hs hN
  obtain ⟨h, Δ, hun, hbind⟩ := GlobalTheory.T.unlinked_layers_hold k s hs
  choose π hπ using fun i => GlobalTheory.T.exists_segment_representation hA (Δ i)
  let x : Fin h → IrrGL k := fun i => IrrGL.of (π i).ρ (π i).smooth (π i).irr
  have hx : ∀ i, IsLSeg (Δ i) (x i).rep := fun i => (hπ i).of_equiv (IrrGL.equivOf _ _ _)
  have hd : ∑ a, (x a).1 = N := by
    rw [← hN, ← hbind, Multiset.map_bind, Multiset.sum_bind]
    change ∑ a, (Δ a).deg = _
    rw [Finset.sum_eq_multiset_sum]
    congr 1
    exact Multiset.map_congr rfl fun i _ => (sum_map_fst_ms (Δ i)).symm
  have hirr : (prodIrr x hd).IsIrreducible :=
    hL h N Δ x hd (fun i j => if e : i = j then e ▸ Segment.not_linked_self _ else hun i j e) hx
  refine ⟨h, Δ, x, hd, hun, hx, ?_, ?_⟩
  · have := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (t := fun i => (Δ i).ms)
      (fun i => (hx i).hasSupport) hirr (IsSubquotient.refl _)
    rwa [show (∑ i, (Δ i).ms) = s from hbind] at this
  · exact (hP h N (fun a => (x a).1) hd (fun a => (x a).2.rep.V) (fun a => (x a).rep)
      (fun a => (x a).2.rep.smooth)).2 fun i => hG (Δ i) _ _ _ (hx i)

theorem unlinkedRealize (hJ : Zc.LSegJacquet k) (hN : GlobalTheory.BZSeg.NuPair k) : UnlinkedRealize k :=
  unlinkedRealize_of PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
    (GlobalTheory.RgGu.Unl.lUnlinkedIrr_nu k hJ PositivityTheory.Geo.geometricLemmaFiltration hN)
    (GlobalTheory.T.segment_generic_of_jacquet_nu_pair k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top hJ hN)
    (GlobalTheory.T.whittaker_heredity_generic_product k (PositivityTheory.rg.gu.hered2.whitHeredity_all k))

end GlobalTheory.RgGu

end
end

section
namespace GlobalTheory.RgGu

theorem genericUnlinkedGL_of_segRep2 (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.GenericUnlinkedGL :=
  genericUnlinkedGL_of (fun k _ _ _ _ _ => suppExists k) (fun k _ _ _ _ _ => genericUnique k)
    (fun k _ _ _ _ _ => unlinkedRealize (k := k)
      (GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top hZ) (GlobalTheory.RgGu.Nup2.nuPair k))

end GlobalTheory.RgGu
end
