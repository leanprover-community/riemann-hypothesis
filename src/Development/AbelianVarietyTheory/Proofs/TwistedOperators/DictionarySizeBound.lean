import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOMemLatOOfHat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacter
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSeriesSchwartzBruhatContinuousSchrodinger
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepsLatticeQuotientConjugateHalfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticesDifferentiableOperatorStatement

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.StdHalfLat

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem locPl_over {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) (t : T) :
    ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ∈ G.pl.S0 ∨ ∃ w' ∈ L.Q t, w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) := by
  classical
  intro w hw
  rcases Finset.mem_union.1 hw with hw0 | hwQ
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw0
    exact Or.inl ((G.pl.under_w hv).symm ▸ hv)
  · exact Or.inr ⟨w, hwQ, rfl⟩

private theorem kill_lemma' {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc}
    (N : Std G Set.univ) {t : T} {e : AE D} (he : IsIdemSum e (locPl G t)) (p : Pair T) {X : Node}
    (hX : DefNode D.R.m X) : ∃ a : AE D, e * (a + cA D a) = 0 ∧ SuppAt a (G.V X) (N.u X).1 :=
  exists_kill N (Set.mem_univ t) (FinDatum.ind G t p (locPl G t) (locPl_over G t) e he) hX

theorem mem_pairLat_iff_std : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ) (t : T) (p : Pair T), DefPair D.R.m p → ∀ (e : AE D), IsIdemSum e (locPl G t) → ∀ x : WO (G.pS p) (G.pT p), IsHalf e x → (x ∈ pairLat G p ↔ x ∈ latO (G.pS p) (G.pT p) (S.N.latS p : Set (Fin (G.pS p).rank → D.host.E)) (S.N.latT p : Set (Fin (G.pT p).rank → D.host.E)) fun _ => True) := by
  intro D T L sc G W S t p hp e he x hx
  cases p with
  | chi i j =>
    obtain ⟨hi, rfl⟩ := hp
    have hXS : DefNode D.R.m (.grid (i + 1) D.R.m) := ⟨hi, rfl⟩
    have hXT : DefNode D.R.m (.grid i D.R.m) := ⟨by omega, rfl⟩
    obtain ⟨hS1, hS2⟩ := hat_moves S.N hXS
    obtain ⟨hT1, hT2⟩ := hat_moves S.N hXT
    obtain ⟨a, ha, hga⟩ := kill_lemma' S.N he (.chi i D.R.m) hXS
    obtain ⟨b, hb, hhb⟩ := kill_lemma' S.N he (.chi i D.R.m) hXT
    refine (mem_latO_iff_of_half (negGA _ (S.N.u (.grid (i + 1) D.R.m)).1) (S.N.u (.grid i D.R.m)).1
      ?_ ?_ hT1 hT2 ha hb ?_ hhb hx).symm
    · intro v hv
      have h := hS1 v hv
      rw [← mt_negGA] at h
      exact h
    · intro v hv
      have h := hS2 v hv
      rw [← mt_negGA, map_inv] at h
      exact h
    · unfold SuppAt at hga ⊢
      rw [← mt_negGA] at hga
      exact hga
  | top t' j =>
    have hXS : DefNode D.R.m (.top j) := by simp only [DefPair] at hp; show j ≤ D.R.m; omega
    have hXT : DefNode D.R.m (.top (j + 1)) := hp
    obtain ⟨hS1, hS2⟩ := hat_moves S.N hXS
    obtain ⟨hT1, hT2⟩ := hat_moves S.N hXT
    obtain ⟨a, ha, hga⟩ := kill_lemma' S.N he (.top t' j) hXS
    obtain ⟨b, hb, hhb⟩ := kill_lemma' S.N he (.top t' j) hXT
    exact (mem_latO_iff_of_half _ _ hS1 hS2 hT1 hT2 ha hb hga hhb hx).symm
  | mu _ _ _ => exact hp.elim
  | core _ => exact hp.elim

end GlobalTheory.StdHalfLat
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_gridPairWeilLattice_iff_standard_of_half : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ) (t : T) (p : Pair T), DefPair D.R.m p → ∀ (e : AE D), IsIdemSum e (locPl G t) → ∀ x : WO (G.pS p) (G.pT p), IsHalf e x → (x ∈ pairLat G p ↔ x ∈ latO (G.pS p) (G.pT p) (S.N.latS p : Set (Fin (G.pS p).rank → D.host.E)) (S.N.latT p : Set (Fin (G.pT p).rank → D.host.E)) fun _ => True) := by
  atlas_forward_decl GlobalTheory.StdHalfLat.mem_pairLat_iff_std
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.HalfIndex

theorem relIndex_nsmul_half : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → ∀ (c : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D c → GlobalTheory.SplitHecke.Chart c v π → ∀ k : ℕ, 0 < k → (AddSubgroup.map (nsmulAddMonoidHom k) ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T c)).relIndex ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T c) = Nat.card (v.adicCompletionIntegers D.host.F ⧸ Ideal.span {(k : v.adicCompletionIntegers D.host.F)}) ^ (S.rank * T.rank) := by
  intro D S T ΛS ΛT hS hT c v π hc hπ k hk
  haveI : CharZero (Fv D.host.F v) := algebraRat.charZero _
  obtain ⟨σ, q1, q2⟩ := GlobalTheory.SplitLinear.exists_section (S := S) (T := T) hc.1 hπ
  have inj : Function.Injective σ := fun w w' h => by rw [← q1 w, h, q1]
  have hinf : infPart D c = 0 := GlobalTheory.PlaceModelSum.infPart_split hc
  set L0 := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hL0
  set L := L0.comap σ with hL
  have hM : L0 ⊓ GlobalTheory.PlaceModel.half S T c = L.map σ := by
    rw [hL, AddSubgroup.map_comap_eq, ← GlobalTheory.SplitLinear.section_range hπ q1 q2, inf_comm]
  let nk : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) →+ Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) :=
    nsmulAddMonoidHom k
  have hcomm : (L.map σ).map (nsmulAddMonoidHom k) = (L.map nk).map σ := by
    rw [AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    exact AddMonoidHom.ext fun w => (map_nsmul σ k w).symm
  have e1 : ((L0 ⊓ GlobalTheory.PlaceModel.half S T c).map (nsmulAddMonoidHom k)).relIndex (L0 ⊓ GlobalTheory.PlaceModel.half S T c) =
      (L.map nk).relIndex L := by
    rw [hM, hcomm, AddSubgroup.relIndex_map_map_of_injective _ _ inj]
  have hk0 : (k : Fv D.host.F v) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hnk : ∀ w, nk w = (k : Fv D.host.F v) • w := fun w => (Nat.cast_smul_eq_nsmul (Fv D.host.F v) k w).symm
  have nkinj : Function.Injective nk := fun w w' h => by
    rw [hnk, hnk] at h
    exact smul_right_injective _ hk0 h
  have nksurj : Function.Surjective nk := fun w => ⟨(k : Fv D.host.F v)⁻¹ • w, by rw [hnk, smul_inv_smul₀ hk0]⟩
  have e2 : (L.map nk).relIndex L = L.relIndex (L.comap nk) := by
    rw [← AddSubgroup.relIndex_map_map_of_injective L (L.comap nk) nkinj,
      AddSubgroup.map_comap_eq_self_of_surjective nksurj]
  let u : (Fv D.host.F v)ˣ := Units.mk0 _ hk0
  have hH : ∀ w : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v),
      ((k : Fv D.host.F v) • (1 : Matrix (Fin T.rank) (Fin T.rank) (Fv D.host.F v))) * w * (1 : Matrix (Fin S.rank) (Fin S.rank) (Fv D.host.F v)) = nk w := fun w => by
    rw [hnk, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
  have hA := GlobalTheory.SplitLinear.relIndex_matrix_lattice D.host.F v S.rank T.rank L (L.comap nk)
    (fun o ho m hm => GlobalTheory.SplitLinear.section_smul hc.1 hπ q1 q2 o ho m hm)
    (GlobalTheory.SplitLinear.section_den hS hT hπ q1 q2) (fun w => ?_)
    ((k : Fv D.host.F v) • 1) 1 1 (u ^ T.rank) (by simp) (by simp [u, Matrix.det_smul]) (fun m hm => ?_) (fun w => ?_)
  rotate_left
  · obtain ⟨N, hN, h1⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' hS hT (σ w)
      (GlobalTheory.PlaceDatum.infPart_of_half hinf (q2 w))
    exact ⟨N, hN, by rwa [AddSubgroup.mem_comap, map_nsmul]⟩
  · rw [hH]
    exact nsmul_mem hm k
  · rw [hH]
    rfl
  have hkc : (((k : v.adicCompletionIntegers D.host.F)) : Fv D.host.F v) = (k : Fv D.host.F v) := by simp
  have hv : Valued.v (k : Fv D.host.F v) ≠ 0 := by simpa using hk0
  have h1 : Valued.v (k : Fv D.host.F v) ≤ 1 := hkc ▸ (k : v.adicCompletionIntegers D.host.F).2
  have hl : WithZero.log (Valued.v (k : Fv D.host.F v)) ≤ 0 := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log hv, WithZero.exp_zero]; exact h1
  obtain ⟨e, he⟩ : ∃ e : ℕ, WithZero.log (Valued.v (k : Fv D.host.F v)) = -(e : ℤ) :=
    ⟨(-WithZero.log (Valued.v (k : Fv D.host.F v))).toNat, by omega⟩
  have he' : Valued.v (k : Fv D.host.F v) = WithZero.exp (-(e : ℤ)) := by
    rw [← he, WithZero.exp_log hv]
  have hcard := (GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers D.host.F v).2
    (k : v.adicCompletionIntegers D.host.F) e (by rw [hkc]; exact he')
  have hu : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV D.host.F v u = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ e)⁻¹ := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV, Units.val_mk0, he, zpow_neg, zpow_natCast]
  have h1' : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV D.host.F v 1 = 1 := by simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
  rw [e1, e2, hcard]
  apply Nat.cast_injective (R := ℝ)
  rw [hA, GlobalTheory.SplitLinear.absV_pow, hu, h1']
  push_cast
  rw [one_pow, one_mul, ← pow_mul, inv_pow, inv_inv, mul_comm T.rank S.rank]

end GlobalTheory.HalfIndex
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_nsmul_idempotentHalf_at_splitPlace : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → ∀ (c : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D c → GlobalTheory.SplitHecke.Chart c v π → ∀ k : ℕ, 0 < k → (AddSubgroup.map (nsmulAddMonoidHom k) ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T c)).relIndex ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T c) = Nat.card (v.adicCompletionIntegers D.host.F ⧸ Ideal.span {(k : v.adicCompletionIntegers D.host.F)}) ^ (S.rank * T.rank) := by
  atlas_forward_decl GlobalTheory.HalfIndex.relIndex_nsmul_half
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory

theorem prod_card_quot_natCast_dvd_pow_finrank : ∀ (F : Type) [Field F] [NumberField F] (s : Finset (HeightOneSpectrum (𝓞 F))) (k : ℕ), 0 < k → ∏ v ∈ s, Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {(k : v.adicCompletionIntegers F)}) ∣ k ^ Module.finrank ℚ F := by
  intro F _ _ s k hk
  classical
  set I : Ideal (𝓞 F) := Ideal.span {(k : 𝓞 F)} with hIdef
  have hI : I ≠ 0 := by
    rw [hIdef, Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hk.ne'
  have hmap : ∀ v : HeightOneSpectrum (𝓞 F),
      I.map (algebraMap (𝓞 F) (v.adicCompletionIntegers F)) =
        Ideal.span {(k : v.adicCompletionIntegers F)} := by
    intro v
    rw [hIdef, Ideal.map_span, Set.image_singleton, map_natCast]
  obtain ⟨hfin, hprod⟩ := GlobalTheory.LocalDifferentProduct.finprod_card_quot_map hI
  simp only [hmap] at hfin hprod
  have hnorm : Ideal.absNorm I = k ^ Module.finrank ℚ F := by
    rw [hIdef, Ideal.absNorm_span_singleton]
    have e : (k : 𝓞 F) = algebraMap ℤ (𝓞 F) (k : ℤ) := by simp
    rw [e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Int.natAbs_pow]
    simp
  rw [← hnorm, ← hprod, finprod_eq_prod_of_mulSupport_subset (s := s ∪ hfin.toFinset) _
    (by intro x hx; simp [hx])]
  exact Finset.prod_dvd_prod_of_subset _ _ _ Finset.subset_union_left

end GlobalTheory
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_card_adicCompletionIntegers_quot_dvd_pow_finrank : ∀ (F : Type) [Field F] [NumberField F] (s : Finset (HeightOneSpectrum (𝓞 F))) (k : ℕ), 0 < k → ∏ v ∈ s, Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {(k : v.adicCompletionIntegers F)}) ∣ k ^ Module.finrank ℚ F := by
  atlas_forward_decl GlobalTheory.prod_card_quot_natCast_dvd_pow_finrank
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.HalfSplit

def kIdx (k : ℕ) (A : Type) [AddCommGroup A] : ℕ := (nsmulAddMonoidHom k : A →+ A).range.index

theorem relIndex_eq_kIdx {G : Type} [AddCommGroup G] (H : AddSubgroup G) (k : ℕ) :
    (AddSubgroup.map (nsmulAddMonoidHom k) H).relIndex H = kIdx k H := by
  unfold kIdx AddSubgroup.relIndex
  congr 1
  ext x
  simp only [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using hyx)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.2, by simp⟩

theorem kIdx_congr {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (k : ℕ) :
    kIdx k A = kIdx k B := by
  unfold kIdx
  rw [← AddSubgroup.index_map_equiv _ e]
  congr 1
  ext x
  simp only [AddSubgroup.mem_map, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨e y, by simp⟩
  · rintro ⟨y, rfl⟩
    exact ⟨k • e.symm y, ⟨e.symm y, rfl⟩, by simp⟩

theorem kIdx_prod {A B : Type} [AddCommGroup A] [AddCommGroup B] (k : ℕ) :
    kIdx k (A × B) = kIdx k A * kIdx k B := by
  unfold kIdx
  rw [← AddSubgroup.index_prod]
  congr 1
  ext ⟨a, b⟩
  simp only [AddSubgroup.mem_prod, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨⟨x, y⟩, hxy⟩
    exact ⟨⟨x, congrArg Prod.fst hxy⟩, ⟨y, congrArg Prod.snd hxy⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨(x, y), Prod.ext hx hy⟩

theorem kIdx_subsingleton {A : Type} [AddCommGroup A] [Subsingleton A] (k : ℕ) : kIdx k A = 1 :=
  AddSubgroup.index_eq_one.2 (eq_top_iff.2 fun x _ => ⟨0, Subsingleton.elim _ _⟩)

variable {R M : Type} [Ring R] [AddCommGroup M] [Module R M]

section split

variable (h : R → AddSubgroup M) (hmem : ∀ e u, u ∈ h e ↔ e • u = u) (Λ : AddSubgroup M) {e f : R}

include hmem in
theorem smul_mem_inf (he : e * e = e) (hΛe : ∀ u ∈ Λ, e • u ∈ Λ) {u : M} (hu : u ∈ Λ) : e • u ∈ Λ ⊓ h e :=
  AddSubgroup.mem_inf.2 ⟨hΛe u hu, (hmem _ _).2 (by rw [smul_smul, he])⟩

def splitEquiv (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) (hfe : f * e = 0)
    (hΛe : ∀ u ∈ Λ, e • u ∈ Λ) (hΛf : ∀ u ∈ Λ, f • u ∈ Λ) :
    ↥(Λ ⊓ h (e + f)) ≃+ ↥(Λ ⊓ h e) × ↥(Λ ⊓ h f) where
  toFun u := (⟨e • u.1, smul_mem_inf h hmem Λ he hΛe (AddSubgroup.mem_inf.1 u.2).1⟩,
    ⟨f • u.1, smul_mem_inf h hmem Λ hf hΛf (AddSubgroup.mem_inf.1 u.2).1⟩)
  invFun p := ⟨p.1.1 + p.2.1, AddSubgroup.mem_inf.2 ⟨add_mem (AddSubgroup.mem_inf.1 p.1.2).1
      (AddSubgroup.mem_inf.1 p.2.2).1, (hmem _ _).2 (by
        have h1 := (hmem _ _).1 (AddSubgroup.mem_inf.1 p.1.2).2
        have h2 := (hmem _ _).1 (AddSubgroup.mem_inf.1 p.2.2).2
        have h3 : f • (p.1.1 : M) = 0 := by rw [← h1, smul_smul, hfe, zero_smul]
        have h4 : e • (p.2.1 : M) = 0 := by rw [← h2, smul_smul, hef, zero_smul]
        rw [smul_add, add_smul, add_smul, h1, h2, h3, h4, add_zero, zero_add])⟩⟩
  left_inv u := by
    apply Subtype.ext
    change e • (u : M) + f • (u : M) = u
    rw [← add_smul]
    exact (hmem _ _).1 (AddSubgroup.mem_inf.1 u.2).2
  right_inv p := by
    have h1 := (hmem _ _).1 (AddSubgroup.mem_inf.1 p.1.2).2
    have h2 := (hmem _ _).1 (AddSubgroup.mem_inf.1 p.2.2).2
    have h3 : f • (p.1.1 : M) = 0 := by rw [← h1, smul_smul, hfe, zero_smul]
    have h4 : e • (p.2.1 : M) = 0 := by rw [← h2, smul_smul, hef, zero_smul]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change e • ((p.1 : M) + p.2) = p.1
      rw [smul_add, h1, h4, add_zero]
    · change f • ((p.1 : M) + p.2) = p.2
      rw [smul_add, h2, h3, zero_add]
  map_add' u v := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change e • ((u : M) + v) = e • (u : M) + e • (v : M)
      exact smul_add _ _ _
    · change f • ((u : M) + v) = f • (u : M) + f • (v : M)
      exact smul_add _ _ _

end split

theorem sum_idem {ι : Type} (s : Finset ι) (cs : ι → R) (hid : ∀ i ∈ s, cs i * cs i = cs i)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → cs i * cs j = 0) :
    (∑ i ∈ s, cs i) * (∑ i ∈ s, cs i) = ∑ i ∈ s, cs i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j hj hji => horth i hi j hj (Ne.symm hji)) (fun h => absurd hi h), hid i hi]

theorem kIdx_half_sum (h : R → AddSubgroup M) (hmem : ∀ e u, u ∈ h e ↔ e • u = u) (Λ : AddSubgroup M)
    {ι : Type} (P : Finset ι) (cs : ι → R) (hid : ∀ i ∈ P, cs i * cs i = cs i)
    (horth : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → cs i * cs j = 0) (hΛ : ∀ i ∈ P, ∀ u ∈ Λ, cs i • u ∈ Λ) (k : ℕ) :
    kIdx k ↥(Λ ⊓ h (∑ i ∈ P, cs i)) = ∏ i ∈ P, kIdx k ↥(Λ ⊓ h (cs i)) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    haveI : Subsingleton ↥(Λ ⊓ h 0) := ⟨fun a b => by
      have ha := (hmem _ _).1 (AddSubgroup.mem_inf.1 a.2).2
      have hb := (hmem _ _).1 (AddSubgroup.mem_inf.1 b.2).2
      rw [zero_smul] at ha hb
      exact Subtype.ext (ha.symm.trans hb)⟩
    exact kIdx_subsingleton k
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
    have ha' : a ∈ insert a s := Finset.mem_insert_self a s
    have hne : ∀ j ∈ s, a ≠ j := fun j hj haj => ha (haj ▸ hj)
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      ← ih (fun i hi => hid i (hs i hi)) (fun i hi j hj => horth i (hs i hi) j (hs j hj))
        (fun i hi => hΛ i (hs i hi)),
      kIdx_congr (splitEquiv h hmem Λ (hid a ha')
        (sum_idem s cs (fun i hi => hid i (hs i hi)) (fun i hi j hj => horth i (hs i hi) j (hs j hj)))
        (by rw [Finset.mul_sum]; exact Finset.sum_eq_zero fun j hj => horth a ha' j (hs j hj) (hne j hj))
        (by rw [Finset.sum_mul]; exact Finset.sum_eq_zero fun j hj => horth j (hs j hj) a ha' (hne j hj).symm)
        (hΛ a ha')
        (fun u hu => by rw [Finset.sum_smul]; exact AddSubgroup.sum_mem _ fun i hi => hΛ i (hs i hi) u hu)),
      kIdx_prod]

theorem relIndex_nsmul_half_sum : ∀ {D : D7} (S T : HSp D) (Λ : AddSubgroup (WO S T)) {ι : Type} (P : Finset ι) (cs : ι → AE D), (∀ i ∈ P, cs i * cs i = cs i) → (∀ i ∈ P, ∀ j ∈ P, i ≠ j → cs i * cs j = 0) → (∀ i ∈ P, ∀ u ∈ Λ, cs i • u ∈ Λ) → ∀ k : ℕ, (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T (∑ i ∈ P, cs i))).relIndex (Λ ⊓ GlobalTheory.PlaceModel.half S T (∑ i ∈ P, cs i)) = ∏ i ∈ P, (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T (cs i))).relIndex (Λ ⊓ GlobalTheory.PlaceModel.half S T (cs i)) := by
  intro D S T Λ ι P cs hid horth hΛ k
  rw [relIndex_eq_kIdx]
  simp only [relIndex_eq_kIdx]
  exact kIdx_half_sum (GlobalTheory.PlaceModel.half S T) (fun e u => GlobalTheory.PlaceModel.mem_half S T) Λ P cs hid horth hΛ k

end GlobalTheory.HalfSplit
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_nsmul_half_orthogonal_idempotent_sum : ∀ {D : D7} (S T : HSp D) (Λ : AddSubgroup (WO S T)) {ι : Type} (P : Finset ι) (cs : ι → AE D), (∀ i ∈ P, cs i * cs i = cs i) → (∀ i ∈ P, ∀ j ∈ P, i ≠ j → cs i * cs j = 0) → (∀ i ∈ P, ∀ u ∈ Λ, cs i • u ∈ Λ) → ∀ k : ℕ, (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T (∑ i ∈ P, cs i))).relIndex (Λ ⊓ GlobalTheory.PlaceModel.half S T (∑ i ∈ P, cs i)) = ∏ i ∈ P, (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T (cs i))).relIndex (Λ ⊓ GlobalTheory.PlaceModel.half S T (cs i)) := by
  atlas_forward_decl GlobalTheory.HalfSplit.relIndex_nsmul_half_sum
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.ChartPlaces

variable {D : D7}

theorem mul_eq_zero_of_ne {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {es : Formalism.L2.DIV.Pl D.host.E → AE D}
    (hes : ∀ Q ∈ P, Formalism.L2.NTheta.IsIdemAt (es Q) Q) {Q Q' : Formalism.L2.DIV.Pl D.host.E} (hQ : Q ∈ P) (hQ' : Q' ∈ P)
    (hne : Q ≠ Q') : es Q * es Q' = 0 := by
  refine (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (hes Q hQ).1 (hes Q' hQ').1).resolve_left fun h => hne ?_
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
  · rw [(hes Q hQ).2 x hx, (hes Q' hQ').2 x hx, h]

theorem chart_places_injective : ∀ {D : D7} (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (es : Formalism.L2.DIV.Pl D.host.E → AE D), (∀ Q ∈ P, Formalism.L2.NTheta.IsIdemAt (es Q) Q) → e = ∑ Q ∈ P, es Q → e * cA D e = 0 → ∀ v : ↥P → HeightOneSpectrum (𝓞 D.host.F), (∀ Q : ↥P, ∃ π : AE D →+* Fv D.host.F (v Q), GlobalTheory.SplitHecke.Chart (cA D (es Q)) (v Q) π) → Function.Injective v := by
  intro D e P es hes hsum hec v hπ
  have hsplit : ∀ Q ∈ P, Formalism.L2.Theta.IsSplitIdem D (es Q) := fun Q hQ => (hes Q hQ).1
  have horth : ∀ Q ∈ P, ∀ Q' ∈ P, Q' ≠ Q → es Q * es Q' = 0 :=
    fun Q hQ Q' hQ' hne => mul_eq_zero_of_ne hes hQ hQ' (Ne.symm hne)

  have habs : ∀ Q ∈ P, es Q * e = es Q := fun Q hQ => by
    rw [hsum]; exact GlobalTheory.PlaceModelSum.mul_sum_orth hsplit horth hQ

  have hcross : ∀ Q ∈ P, ∀ Q' ∈ P, es Q' * cA D (es Q) = 0 := fun Q hQ Q' hQ' => by
    have h1 : cA D (es Q) * cA D e = cA D (es Q) := by rw [← map_mul, habs Q hQ]
    calc es Q' * cA D (es Q) = (es Q' * e) * (cA D e * cA D (es Q)) := by
          rw [habs Q' hQ', mul_comm (cA D e), h1]
      _ = es Q' * (e * cA D e) * cA D (es Q) := by ring
      _ = 0 := by rw [hec, mul_zero, zero_mul]
  intro Q Q' hvv
  by_contra hne
  have hne' : (Q : Formalism.L2.DIV.Pl D.host.E) ≠ Q' := fun h => hne (Subtype.ext h)
  obtain ⟨π, hπc⟩ := hπ Q
  obtain ⟨π', hπc'⟩ := hπ Q'
  have hs' : Formalism.L2.Theta.IsSplitIdem D (cA D (es Q')) := GlobalTheory.PlaceModelSum.isSplitIdem_cA (hsplit Q' Q'.2)
  obtain ⟨hid', hort', v', ε', ⟨α', rfl, hα1, hα0⟩, hsum'⟩ := hs'

  have hπ'1 : π' (cA D (es Q')) = 1 := by
    have := (hπc'.2.1 (1 - cA D (es Q'))).2 (by rw [mul_sub, mul_one, hid', sub_self])
    rwa [map_sub, map_one, sub_eq_zero, eq_comm] at this
  have hπ'0 : π' (cA D (cA D (es Q'))) = 0 := (hπc'.2.1 _).2 hort'
  have hw1 : evalV D.host.F (v Q') α' = 1 := by
    have := hπc'.2.2.1 (pairA D.host.F 0 α')
    rw [← hsum', map_add, hπ'1, hπ'0, add_zero] at this
    exact this.symm
  have hwv : v Q' = v' := by
    by_contra h
    rw [hα0 _ h] at hw1
    exact zero_ne_one hw1

  have hA : π (cA D (es Q')) = 0 := (hπc.2.1 _).2 (by
    rw [← map_mul, mul_eq_zero_of_ne hes Q.2 Q'.2 hne', map_zero])
  have hB : π (cA D (cA D (es Q'))) = 0 := (hπc.2.1 _).2 (by
    rw [cA_cA, mul_comm]; exact hcross Q Q.2 Q' Q'.2)
  have hC := hπc.2.2.1 (pairA D.host.F 0 α')
  rw [← hsum', map_add, hA, hB, add_zero] at hC
  have h0 : evalV D.host.F (v Q) α' = 0 := hC.symm
  rw [hvv.trans hwv, hα1] at h0
  exact one_ne_zero h0

end GlobalTheory.ChartPlaces
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_idempotent_chart_places_injective : ∀ {D : D7} (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (es : Formalism.L2.DIV.Pl D.host.E → AE D), (∀ Q ∈ P, Formalism.L2.NTheta.IsIdemAt (es Q) Q) → e = ∑ Q ∈ P, es Q → e * cA D e = 0 → ∀ v : ↥P → HeightOneSpectrum (𝓞 D.host.F), (∀ Q : ↥P, ∃ π : AE D →+* Fv D.host.F (v Q), GlobalTheory.SplitHecke.Chart (cA D (es Q)) (v Q) π) → Function.Injective v := by
  atlas_forward_decl GlobalTheory.ChartPlaces.chart_places_injective
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.HalfCosetCount

set_option maxHeartbeats 2000000 in

theorem halfCoset_reps_card : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), (∀ y ∈ R, IsHalf (cA D e) y ∧ k • y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ (∀ y : WO S T, IsHalf (cA D e) y → k • y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∃! r, r ∈ R ∧ y - r ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ R.card ∣ k ^ (D.R.f * S.rank * T.rank) := by
  intro D S T ΛS ΛT hS hT e P he k hk
  classical
  obtain ⟨⟨es, hes, rfl⟩, hec⟩ := he
  set Λ := (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) with hΛ
  set c := cA D (∑ Q ∈ P, es Q) with hcdef
  have hc : c = ∑ Q ∈ P, cA D (es Q) := map_sum _ _ _
  have hes_orth : ∀ Q ∈ P, ∀ Q' ∈ P, Q ≠ Q' → es Q * es Q' = 0 := fun Q hQ Q' hQ' hne =>
    (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (hes Q hQ).1 (hes Q' hQ').1).resolve_left fun h => hne
      (HeightOneSpectrum.ext (Ideal.ext fun x => by
        by_cases hx : x = 0
        · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
        · rw [(hes Q hQ).2 x hx, (hes Q' hQ').2 x hx, h]))
  have hidem : ∀ Q ∈ P, cA D (es Q) * cA D (es Q) = cA D (es Q) := fun Q hQ => by
    rw [← map_mul, (hes Q hQ).1.1]
  have horth : ∀ Q ∈ P, ∀ Q' ∈ P, Q ≠ Q' → cA D (es Q) * cA D (es Q') = 0 := fun Q hQ Q' hQ' hne => by
    rw [← map_mul, hes_orth Q hQ Q' hQ' hne, map_zero]
  have hstab : ∀ Q ∈ P, ∀ u ∈ Λ, cA D (es Q) • u ∈ Λ := fun Q hQ u hu =>
    GlobalTheory.PlaceModelSum.idem_smul_latO (hidem Q hQ) hu
  have hch : ∀ Q : ↥P, ∃ w : HeightOneSpectrum (𝓞 D.host.F), ∃ π : AE D →+* Fv D.host.F w,
      GlobalTheory.SplitHecke.Chart (cA D (es Q)) w π := fun Q =>
    GlobalTheory.SplitChart.exists_chart _ (GlobalTheory.PlaceModelSum.isSplitIdem_cA (hes Q Q.2).1)
  choose v π hπ using hch
  have hvinj : Function.Injective v :=
    GlobalTheory.T.conjugate_idempotent_chart_places_injective _ P es (fun Q hQ => hes Q hQ) rfl hec v fun Q => ⟨π Q, hπ Q⟩

  have hcount : (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T c)).relIndex
      (Λ ⊓ GlobalTheory.PlaceModel.half S T c) =
      (∏ Q : ↥P, Nat.card ((v Q).adicCompletionIntegers D.host.F ⧸
        Ideal.span {(k : (v Q).adicCompletionIntegers D.host.F)})) ^ (S.rank * T.rank) := by
    rw [hc, GlobalTheory.T.relIndex_nsmul_half_orthogonal_idempotent_sum S T Λ P (fun Q => cA D (es Q)) hidem horth hstab k, ← Finset.prod_pow,
      ← Finset.prod_attach P]
    refine Finset.prod_congr rfl fun Q _ => ?_
    exact GlobalTheory.T.relIndex_nsmul_idempotentHalf_at_splitPlace S T ΛS ΛT hS.1 hT.1 _ (v Q) (π Q) (GlobalTheory.PlaceModelSum.isSplitIdem_cA (hes Q Q.2).1) (hπ Q) k hk
  have hdvd : (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T c)).relIndex
      (Λ ⊓ GlobalTheory.PlaceModel.half S T c) ∣ k ^ (D.R.f * S.rank * T.rank) := by
    have h1 := GlobalTheory.T.prod_card_adicCompletionIntegers_quot_dvd_pow_finrank D.host.F (Finset.univ.image v) k hk
    rw [Finset.prod_image fun x _ y _ h => hvinj h, Formalism.MainNotions.J.finrank_F_eq] at h1
    rw [hcount, mul_assoc, pow_mul k D.R.f]
    exact pow_dvd_pow_of_dvd h1 _

  set M := Λ ⊓ GlobalTheory.PlaceModel.half S T c with hM
  set Y := Λ.comap (nsmulAddMonoidHom k) ⊓ GlobalTheory.PlaceModel.half S T c with hY
  have hinj : Function.Injective (nsmulAddMonoidHom k : WO S T →+ WO S T) := fun x y h => nsmul_cancel_mx hk h
  have hu : IsUnit (k : AE D) := by
    rw [← map_natCast (algebraMap D.host.F (AE D))]
    exact (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hk.ne')).map _
  have hYM : Y.map (nsmulAddMonoidHom k) = M := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hy1, hy2⟩ := AddSubgroup.mem_inf.1 hy
      exact AddSubgroup.mem_inf.2 ⟨hy1, (GlobalTheory.PlaceModel.half S T c).nsmul_mem hy2 k⟩
    · intro hx
      obtain ⟨hx1, hx2⟩ := AddSubgroup.mem_inf.1 hx
      have key : k • ((↑hu.unit⁻¹ : AE D) • x) = x := by
        rw [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, IsUnit.mul_val_inv, one_smul]
      refine ⟨(↑hu.unit⁻¹ : AE D) • x, AddSubgroup.mem_inf.2 ⟨?_, ?_⟩, key⟩
      · rw [AddSubgroup.mem_comap]
        change k • _ ∈ Λ
        rw [key]; exact hx1
      · refine (GlobalTheory.PlaceModel.mem_half S T).2 ?_
        have hx3 : c • x = x := (GlobalTheory.PlaceModel.mem_half S T).1 hx2
        rw [smul_comm c (↑hu.unit⁻¹ : AE D) x, hx3]
  have hMY : M.relIndex Y = (M.map (nsmulAddMonoidHom k)).relIndex M := by
    rw [← AddSubgroup.relIndex_map_map_of_injective (f := (nsmulAddMonoidHom k : WO S T →+ WO S T)) M Y hinj, hYM]
  have hne : (M.addSubgroupOf Y).index ≠ 0 := by
    change M.relIndex Y ≠ 0
    rw [hMY]
    exact fun h => (pow_pos hk _).ne' (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  haveI : Finite (↥Y ⧸ M.addSubgroupOf Y) := AddSubgroup.index_ne_zero_iff_finite.1 hne
  obtain ⟨R, hRc, hRY, hRu⟩ := GlobalTheory.SplitLinear.exists_reps M Y
  refine ⟨R, fun y hy => ?_, fun y hy1 hy2 => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 (hRY y hy)
    exact ⟨(GlobalTheory.PlaceModel.isHalf_iff S T).2 h2, h1⟩
  · have hyY : y ∈ Y := AddSubgroup.mem_inf.2 ⟨hy2, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hy1⟩
    obtain ⟨r, ⟨hr, hyr⟩, huniq⟩ := hRu y hyY
    refine ⟨r, ⟨hr, (AddSubgroup.mem_inf.1 hyr).1⟩, fun r' hr' => huniq r' ⟨hr'.1, AddSubgroup.mem_inf.2 ⟨hr'.2, ?_⟩⟩⟩
    exact sub_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hy1) (AddSubgroup.mem_inf.1 (hRY r' hr'.1)).2
  · rw [hRc, hMY]
    exact hdvd

end GlobalTheory.HalfCosetCount
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_halfCosetRepresentatives_card_dvd : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), (∀ y ∈ R, IsHalf (cA D e) y ∧ k • y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ (∀ y : WO S T, IsHalf (cA D e) y → k • y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∃! r, r ∈ R ∧ y - r ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ R.card ∣ k ^ (D.R.f * S.rank * T.rank) := by
  atlas_forward_decl GlobalTheory.HalfCosetCount.halfCoset_reps_card
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.CharSumHalf

open GlobalTheory.Core.Rk.ThetaOf GlobalTheory.DownLift.GenQuot

set_option synthInstance.maxHeartbeats 100000 in

theorem charSum_detects_multiple : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (e : AE D) (k : ℕ) (R : Finset (WO S T)), 0 < k → (∀ u ∈ Λ, IsHalf e u → ∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T u y) = 1) → (∀ x : WO S T, IsHalf e x → (∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) → x ∈ Λ) → (∀ y ∈ R, IsHalf (cA D e) y ∧ k • y ∈ Λ) → (∀ y : WO S T, IsHalf (cA D e) y → k • y ∈ Λ → ∃! r, r ∈ R ∧ y - r ∈ Λ) → ∀ t ∈ Λ, IsHalf e t → ((∃ u ∈ Λ, IsHalf e u ∧ t = k • u) → ∑ r ∈ R, ψ (symplO S T t r) = R.card) ∧ ((¬ ∃ u ∈ Λ, IsHalf e u ∧ t = k • u) → ∑ r ∈ R, ψ (symplO S T t r) = 0) := by
  intro D ψ S T Λ e k R hk hpair hann hR hU t htΛ hte
  classical
  have half_sub : ∀ {c : AE D} {x y : WO S T}, IsHalf c x → IsHalf c y → IsHalf c (x - y) :=
    fun hx hy i j => by simp only [Matrix.sub_apply, mul_sub, hx i j, hy i j]
  have half_add : ∀ {c : AE D} {x y : WO S T}, IsHalf c x → IsHalf c y → IsHalf c (x + y) :=
    fun hx hy i j => by simp only [Matrix.add_apply, mul_add, hx i j, hy i j]
  have half_nsmul : ∀ {c : AE D} {x : WO S T} (n : ℕ), IsHalf c x → IsHalf c (n • x) :=
    fun n hx i j => by rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hx i j]
  have half_smul : ∀ {c : AE D} {x : WO S T} (a : AE D), IsHalf c x → IsHalf c (a • x) :=
    fun a hx i j => by simp only [Matrix.smul_apply, smul_eq_mul]; rw [mul_left_comm, hx i j]
  have pair_add : ∀ x y y' : WO S T,
      ψ (symplO S T x (y + y')) = ψ (symplO S T x y) * ψ (symplO S T x y') := by
    intro x y y'; rw [symplO_add_right, AddChar.map_add_eq_mul]
  constructor
  · rintro ⟨u, huΛ, hue, rfl⟩
    have h1 : ∀ r ∈ R, ψ (symplO S T (k • u) r) = 1 := fun r hr => by
      rw [symplO_nsmul_swap]
      exact hpair u huΛ hue _ (hR r hr).2 (half_nsmul k (hR r hr).1)
    rw [Finset.sum_congr rfl h1]; simp
  · intro hnot
    have hex : ∃ r₀ ∈ R, ψ (symplO S T t r₀) ≠ 1 := by
      by_contra hall
      push_neg at hall
      apply hnot
      set a : AE D := algebraMap D.host.F (AE D) ((k : D.host.F)⁻¹) with ha
      have hka : k • a = 1 := by
        rw [ha, ← map_nsmul, nsmul_eq_mul, mul_inv_cancel₀ (by exact_mod_cast hk.ne'), map_one]
      have hkx : ∀ x : WO S T, k • (a • x) = x := fun x => by
        rw [← smul_assoc, hka, one_smul]
      refine ⟨a • t, ?_, half_smul a hte, (hkx t).symm⟩
      apply hann _ (half_smul a hte)
      intro y hyΛ hyc
      obtain ⟨r, ⟨hrR, hdiff⟩, -⟩ := hU (a • y) (half_smul a hyc) (by rw [hkx]; exact hyΛ)
      have hsw : symplO S T (a • t) y = symplO S T t (a • y) := by
        conv_lhs => rw [← hkx y]
        rw [← symplO_nsmul_swap, hkx]
      rw [hsw, show a • y = (a • y - r) + r by abel, pair_add, hall r hrR, mul_one]
      exact hpair t htΛ hte _ hdiff (half_sub (half_smul a hyc) (hR r hrR).1)
    obtain ⟨r₀, hr₀R, hr₀⟩ := hex
    obtain ⟨rep, rep_spec⟩ : ∃ rep : WO S T → WO S T,
        ∀ y, IsHalf (cA D e) y → k • y ∈ Λ → rep y ∈ R ∧ y - rep y ∈ Λ := by
      refine ⟨fun y => if h : IsHalf (cA D e) y ∧ k • y ∈ Λ then (hU y h.1 h.2).exists.choose else 0, ?_⟩
      intro y h1 h2
      dsimp only
      rw [dif_pos (And.intro h1 h2)]
      exact (hU y h1 h2).exists.choose_spec
    have rep_eq : ∀ y r, IsHalf (cA D e) y → k • y ∈ Λ → r ∈ R → y - r ∈ Λ → rep y = r :=
      fun y r h1 h2 hr hd => (hU y h1 h2).unique (rep_spec y h1 h2) ⟨hr, hd⟩
    have hadd : ∀ r ∈ R, ∀ s ∈ R, IsHalf (cA D e) (r + s) ∧ k • (r + s) ∈ Λ := fun r hr s hs =>
      ⟨half_add (hR r hr).1 (hR s hs).1, by rw [nsmul_add]; exact Λ.add_mem (hR r hr).2 (hR s hs).2⟩
    have hsub : ∀ r ∈ R, ∀ s ∈ R, IsHalf (cA D e) (r - s) ∧ k • (r - s) ∈ Λ := fun r hr s hs =>
      ⟨half_sub (hR r hr).1 (hR s hs).1, by rw [nsmul_sub]; exact Λ.sub_mem (hR r hr).2 (hR s hs).2⟩
    have key : ∑ r ∈ R, ψ (symplO S T t r₀) * ψ (symplO S T t r) = ∑ r ∈ R, ψ (symplO S T t r) := by
      apply Finset.sum_nbij' (fun r => rep (r + r₀)) (fun r => rep (r - r₀))
      · intro r hr; exact (rep_spec _ (hadd r hr r₀ hr₀R).1 (hadd r hr r₀ hr₀R).2).1
      · intro r hr; exact (rep_spec _ (hsub r hr r₀ hr₀R).1 (hsub r hr r₀ hr₀R).2).1
      · intro r hr
        obtain ⟨h1, h2⟩ := rep_spec _ (hadd r hr r₀ hr₀R).1 (hadd r hr r₀ hr₀R).2
        have hs := hsub _ h1 r₀ hr₀R
        refine rep_eq _ r hs.1 hs.2 hr ?_
        have : rep (r + r₀) - r₀ - r = -((r + r₀) - rep (r + r₀)) := by abel
        rw [this]; exact Λ.neg_mem h2
      · intro r hr
        obtain ⟨h1, h2⟩ := rep_spec _ (hsub r hr r₀ hr₀R).1 (hsub r hr r₀ hr₀R).2
        have hs := hadd _ h1 r₀ hr₀R
        refine rep_eq _ r hs.1 hs.2 hr ?_
        have : rep (r - r₀) + r₀ - r = -((r - r₀) - rep (r - r₀)) := by abel
        rw [this]; exact Λ.neg_mem h2
      · intro r hr
        obtain ⟨h1, h2⟩ := rep_spec _ (hadd r hr r₀ hr₀R).1 (hadd r hr r₀ hr₀R).2
        have hrep : rep (r + r₀) = (r + r₀) + -((r + r₀) - rep (r + r₀)) := by abel
        have hhalf : IsHalf (cA D e) (-((r + r₀) - rep (r + r₀))) := by
          have := half_sub (hadd r hr r₀ hr₀R).1 (hR _ h1).1
          intro i j; simp only [Matrix.neg_apply, mul_neg, this i j]
        show _ = ψ (symplO S T t (rep (r + r₀)))
        rw [hrep, pair_add, pair_add, hpair t htΛ hte _ (Λ.neg_mem h2) hhalf, mul_one, mul_comm]
    rw [← Finset.mul_sum] at key
    have h0 : (ψ (symplO S T t r₀) - 1) * ∑ r ∈ R, ψ (symplO S T t r) = 0 := by
      rw [sub_mul, key, one_mul, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hr₀)

end GlobalTheory.CharSumHalf
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfLattice_charSum_detects_nsmul_multiple : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (e : AE D) (k : ℕ) (R : Finset (WO S T)), 0 < k → (∀ u ∈ Λ, IsHalf e u → ∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T u y) = 1) → (∀ x : WO S T, IsHalf e x → (∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) → x ∈ Λ) → (∀ y ∈ R, IsHalf (cA D e) y ∧ k • y ∈ Λ) → (∀ y : WO S T, IsHalf (cA D e) y → k • y ∈ Λ → ∃! r, r ∈ R ∧ y - r ∈ Λ) → ∀ t ∈ Λ, IsHalf e t → ((∃ u ∈ Λ, IsHalf e u ∧ t = k • u) → ∑ r ∈ R, ψ (symplO S T t r) = R.card) ∧ ((¬ ∃ u ∈ Λ, IsHalf e u ∧ t = k • u) → ∑ r ∈ R, ψ (symplO S T t r) = 0) := by
  atlas_forward_decl GlobalTheory.CharSumHalf.charSum_detects_multiple
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.RowEx.FourierSelfDualModel

open GlobalTheory.RowTest GlobalTheory.FunObj Formalism.IndefR.Datum

theorem stdSelfDual {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {U : Set T}
    (N : Std G U) {p : Pair T} (hp : DefPair D.R.m p) :
    IsSelfDualC (G.pS p) (N.latS p) ∧ IsSelfDualC (G.pT p) (N.latT p) := by
  obtain ⟨h1, h2⟩ := hp.nodes
  rcases p with ⟨i, j⟩ | ⟨t', i, j⟩ | i | ⟨t', j⟩
  · exact ⟨isSelfDualC_neg (N.selfDual h2), N.selfDual h1⟩
  · exact hp.elim
  · exact hp.elim
  · exact ⟨N.selfDual h1, N.selfDual h2⟩

theorem pow_psi_eq_one {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (e : AE D) (k : ℕ)
    (hLL : ∀ u ∈ Λ, IsHalf e u → ∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T u y) = 1)
    {x y : WO S T} (hx : IsHalf e x) (hkx : k • x ∈ Λ) (hy : IsHalf (cA D e) y) (hky : k • y ∈ Λ) :
    ψ (symplOH S T x y) ^ (2 * k * k) = 1 := by
  have hl : ∀ (m : ℕ) (a b : WO S T), symplOH S T (m • a) b = m • symplOH S T a b := fun m a b => by
    induction m with
    | zero => simp [GlobalTheory.FinTranslate.symplOH_zero_left]
    | succ m ih => rw [succ_nsmul, GlobalTheory.FinTranslate.symplOH_add_left, ih, succ_nsmul]
  have hr : ∀ (m : ℕ) (a b : WO S T), symplOH S T a (m • b) = m • symplOH S T a b := fun m a b => by
    induction m with
    | zero => simp [GlobalTheory.FinTranslate.symplOH_zero_right]
    | succ m ih => rw [succ_nsmul, GlobalTheory.FinTranslate.symplOH_add_right, ih, succ_nsmul]
  have h2 : ∀ a b : WO S T, symplOH S T a b + symplOH S T a b = symplO S T a b := fun a b => by
    unfold symplOH
    rw [← add_mul, ← map_add]
    norm_num
  have e1 : (2 * k * k) • symplOH S T x y = symplO S T (k • x) (k • y) := by
    rw [← h2, hl, hr, ← two_nsmul, ← mul_nsmul, ← mul_nsmul]
    ring_nf
  rw [← AddChar.map_nsmul_eq_pow, e1]
  exact hLL _ hkx (isHalf_nsmul_of k hx) _ hky (isHalf_nsmul_of k hy)

theorem mem_qbar_of_pow {z : ℂ} {N : ℕ} (hN : 0 < N) (h : z ^ N = 1) : z ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  have hi : IsIntegral ℚ z := IsIntegral.of_pow hN (by rw [h]; exact isIntegral_one)
  exact mem_algebraicClosure_iff.2 hi.isAlgebraic

set_option maxHeartbeats 1600000 in
open Classical in

theorem model_coset {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (e : AE D) (P : Finset (Pl D.host.E))
    (he : IsIdemSum e P) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ))
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm)
    (k : ℕ) (hk : 0 < k) (x₀ : WO S T) (hx₀ : IsHalf e x₀)
    (hkx : k • x₀ ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    ∃ (n : ℕ) (c : Fin n → Formalism.MainNotions.TaylorLogMetric.Qbar) (w : Fin n → WO S T),
      (∀ i, k • w i ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧
      (∀ i, (w i).map (infPart D) = 0) ∧
      (∀ i, IsIntegral ℤ ((k : Formalism.MainNotions.TaylorLogMetric.Qbar) ^ (D.R.f * S.rank * T.rank) * c i)) ∧
      (∀ ρ : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ, ∑ i, ‖ρ (c i)‖ ≤ 1) ∧
      Tm ((halfCoset e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
        k x₀).indicator 1) = ∑ i, (c i : ℂ) • heisO ψ S T (w i) f₀ := by
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛ
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hinfc := GlobalTheory.PlaceDatum.infPart_cA hinf
  have hLL : ∀ u ∈ Λ, IsHalf e u → ∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T u y) = 1 :=
    fun u hu hu' y hy _ => ((GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1 u (GlobalTheory.PlaceDatum.infPart_of_half hinf hu')).1 hu y hy
  have hdual : ∀ x : WO S T, IsHalf e x → (∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) → x ∈ Λ := by
    intro x hx h
    refine ((GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1 x
      (GlobalTheory.PlaceDatum.infPart_of_half hinf hx)).2 fun u hu => ?_
    have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
    have hec : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
    have hcu : IsHalf (cA D e) (cA D e • u) := fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hec]
    have := h _ (GlobalTheory.SplitScalar.idem_smul_mem hec u hu) hcu
    rwa [← GlobalTheory.PlaceModel.symplO_smul, show e • x = x from Matrix.ext fun i j => hx i j] at this
  obtain ⟨R, hR1, hR2, hRd⟩ := GlobalTheory.T.exists_halfCosetRepresentatives_card_dvd S T ΛS ΛT hS hT e P he k hk
  have hsum := GlobalTheory.T.halfLattice_charSum_detects_nsmul_multiple ψ S T Λ e k R hk hLL hdual hR1 hR2
  have hcard : R.card ≠ 0 := by
    intro h0
    rw [h0, zero_dvd_iff] at hRd
    exact pow_ne_zero _ hk.ne' hRd
  have hcardC : (R.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hcard
  set Ψ : WO S T → ℂ := (halfCoset e Λ k 0).indicator 1 with hΨdef
  have hmem0 : ∀ t, t ∈ halfCoset e Λ k 0 ↔ ∃ u ∈ Λ, IsHalf e u ∧ t = k • u := fun t => by
    simp only [halfCoset, Set.mem_setOf_eq, zero_add]
  have hΨ : Ψ = (R.card : ℂ)⁻¹ • ∑ r ∈ R, (fun t => ψ (symplO S T t r) * halfInd e Λ t) := by
    funext t
    rw [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    by_cases ht : t ∈ Λ ∧ IsHalf e t
    · have h1 : halfInd e Λ t = 1 := if_pos ht
      simp only [h1, mul_one]
      by_cases hm : ∃ u ∈ Λ, IsHalf e u ∧ t = k • u
      · rw [(hsum t ht.1 ht.2).1 hm, inv_mul_cancel₀ hcardC, hΨdef, Set.indicator_of_mem ((hmem0 t).2 hm)]
        rfl
      · rw [(hsum t ht.1 ht.2).2 hm, mul_zero, hΨdef, Set.indicator_of_notMem (fun h => hm ((hmem0 t).1 h))]
    · have h1 : halfInd e Λ t = 0 := if_neg ht
      simp only [h1, mul_zero, Finset.sum_const_zero]
      rw [hΨdef, Set.indicator_of_notMem]
      intro h
      obtain ⟨u, hu, hu', rfl⟩ := (hmem0 t).1 h
      exact ht ⟨nsmul_mem hu k, isHalf_nsmul_of k hu'⟩
  have hΨsb : IsSBHalf e Λ Ψ := isSBHalf_halfCoset_indicator hk (fun i j => mul_zero _) (by simp)
  have hind : (halfCoset e Λ k x₀).indicator (1 : WO S T → ℂ) = fun t => Ψ (t + -x₀) := by
    funext t
    have hiff : t ∈ halfCoset e Λ k x₀ ↔ t + -x₀ ∈ halfCoset e Λ k 0 := by
      rw [hmem0]
      simp only [halfCoset, Set.mem_setOf_eq]
      refine exists_congr fun u => and_congr_right fun _ => and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
      · rw [h]; abel
      · rw [← h]; abel
    by_cases h : t ∈ halfCoset e Λ k x₀
    · rw [Set.indicator_of_mem h, hΨdef, Set.indicator_of_mem (hiff.1 h)]
      rfl
    · rw [Set.indicator_of_notMem h, hΨdef, Set.indicator_of_notMem (fun h' => h (hiff.2 h'))]
  have hvac : Tm (halfInd e Λ) = f₀ := by
    have := hTm.vac
    rwa [one_smul] at this
  have hTΨ : Tm Ψ = (R.card : ℂ)⁻¹ • ∑ r ∈ R, heisO ψ S T r f₀ := by
    rw [hΨ, map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [hTm.modul _ (GlobalTheory.isSBHalf_halfInd e Λ) r (hR1 r hr).1, hvac]
  have hnx : IsHalf e (-x₀) := fun i j => by rw [Matrix.neg_apply, mul_neg, hx₀ i j]
  have hneg : k • -x₀ = -(k • x₀) := by
    rw [eq_neg_iff_add_eq_zero, ← nsmul_add, neg_add_cancel, nsmul_zero]
  have hmain : Tm ((halfCoset e Λ k x₀).indicator 1) =
      ∑ r ∈ R, ((R.card : ℂ)⁻¹ * ψ (symplOH S T (-x₀) r)) • heisO ψ S T (-x₀ + r) f₀ := by
    rw [hind, hTm.trans Ψ hΨsb (-x₀) hnx, hTΨ]
    have hlin : heisO ψ S T (-x₀) ((R.card : ℂ)⁻¹ • ∑ r ∈ R, heisO ψ S T r f₀) =
        (R.card : ℂ)⁻¹ • ∑ r ∈ R, heisO ψ S T (-x₀) (heisO ψ S T r f₀) := by
      funext t
      simp only [heisO, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => by ring
    rw [hlin, Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [GlobalTheory.FinTranslate.heisO_heisO, smul_smul]

  have hroot : ∀ r ∈ R, ψ (symplOH S T (-x₀) r) ^ (2 * k * k) = 1 := fun r hr =>
    pow_psi_eq_one ψ S T Λ e k hLL hnx (by rw [hneg]; exact neg_mem hkx)
      (hR1 r hr).1 (hR1 r hr).2
  have hN : 0 < 2 * k * k := by positivity
  let ζ : R → Formalism.MainNotions.TaylorLogMetric.Qbar := fun r => ⟨ψ (symplOH S T (-x₀) r.1), mem_qbar_of_pow hN (hroot r.1 r.2)⟩
  have hζ : ∀ r, ζ r ^ (2 * k * k) = 1 := fun r => Subtype.ext (by
    show (ψ (symplOH S T (-x₀) r.1)) ^ (2 * k * k) = 1
    exact hroot r.1 r.2)
  let cc : R → Formalism.MainNotions.TaylorLogMetric.Qbar := fun r => (R.card : Formalism.MainNotions.TaylorLogMetric.Qbar)⁻¹ * ζ r
  have hcc : ∀ r, (cc r : ℂ) = (R.card : ℂ)⁻¹ * ψ (symplOH S T (-x₀) r.1) := fun r => by
    simp [cc, ζ]
  obtain ⟨m, hm⟩ := hRd
  refine ⟨R.card, fun i => cc (R.equivFin.symm i), fun i => -x₀ + (R.equivFin.symm i).1, fun i => ?_, fun i => ?_,
    fun i => ?_, fun ρ => ?_, ?_⟩
  · rw [nsmul_add]
    refine add_mem ?_ (hR1 _ (R.equivFin.symm i).2).2
    rw [hneg]
    exact neg_mem hkx
  · have h1 := GlobalTheory.PlaceDatum.infPart_of_half hinf hnx
    have h2 := GlobalTheory.PlaceDatum.infPart_of_half hinfc (hR1 _ (R.equivFin.symm i).2).1
    ext a b
    have e1 : infPart D ((-x₀) a b) = 0 := by
      have := congrFun (congrFun h1 a) b
      rwa [Matrix.map_apply, Matrix.zero_apply] at this
    have e2 : infPart D ((R.equivFin.symm i).1 a b) = 0 := by
      have := congrFun (congrFun h2 a) b
      rwa [Matrix.map_apply, Matrix.zero_apply] at this
    rw [Matrix.map_apply]
    dsimp only
    rw [Matrix.add_apply, RingHom.map_add, e1, e2, add_zero, Matrix.zero_apply]
  · have hc0 : ((R.card : ℕ) : Formalism.MainNotions.TaylorLogMetric.Qbar) ≠ 0 := Nat.cast_ne_zero.2 hcard
    have e1 : (k : Formalism.MainNotions.TaylorLogMetric.Qbar) ^ (D.R.f * S.rank * T.rank) * cc (R.equivFin.symm i) =
        (m : Formalism.MainNotions.TaylorLogMetric.Qbar) * ζ (R.equivFin.symm i) := by
      simp only [cc]
      rw [← Nat.cast_pow, hm, Nat.cast_mul, ← mul_assoc, mul_comm ((R.card : ℕ) : Formalism.MainNotions.TaylorLogMetric.Qbar), mul_assoc (m : Formalism.MainNotions.TaylorLogMetric.Qbar),
        mul_inv_cancel₀ hc0, mul_one]
    rw [e1]
    have hm' : IsIntegral ℤ ((m : ℕ) : Formalism.MainNotions.TaylorLogMetric.Qbar) := by
      have := isIntegral_algebraMap (R := ℤ) (A := Formalism.MainNotions.TaylorLogMetric.Qbar) (x := (m : ℤ))
      rwa [map_natCast] at this
    exact hm'.mul (IsIntegral.of_pow hN (by rw [hζ]; exact isIntegral_one))
  · have h1 : ∀ r, ‖ρ (cc r)‖ = (R.card : ℝ)⁻¹ := fun r => by
      have hρ : ρ (ζ r) ^ (2 * k * k) = 1 := by rw [← map_pow, hζ, map_one]
      simp only [cc, map_mul, map_inv₀, map_natCast, norm_mul, norm_inv, Complex.norm_natCast,
        Complex.norm_eq_one_of_pow_eq_one hρ hN.ne', mul_one]
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_inv_cancel₀ (Nat.cast_ne_zero.2 hcard)]
  · rw [hmain, ← Finset.sum_coe_sort R, ← R.equivFin.symm.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcc]

end GlobalTheory.RowEx.FourierSelfDualModel

open GlobalTheory.RowEx.FourierSelfDualModel in

theorem GlobalTheory.RowEx.fourierVec : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ) (t : T) (p : Pair T), DefPair D.R.m p → ∀ (k : ℕ) (d : FinDatum G t p), 0 < k → IsCosetDatum k d → d.z = 1 → d.P = locPl G t → ∃ (n : ℕ) (c : Fin n → Formalism.MainNotions.TaylorLogMetric.Qbar) (w : Fin n → WO (G.pS p) (G.pT p)), (∀ i, k • w i ∈ latO (G.pS p) (G.pT p) (S.N.latS p : Set _) (S.N.latT p : Set _) fun _ => True) ∧ (∀ i, (w i).map (infPart D) = 0) ∧ (∀ i, IsIntegral ℤ ((k : Formalism.MainNotions.TaylorLogMetric.Qbar) ^ (D.R.f * (G.pS p).rank * (G.pT p).rank) * c i)) ∧ (∀ ρ : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ, ∑ i, ‖ρ (c i)‖ ≤ 1) ∧ S.Z.vec d = ∑ i, (c i : ℂ) • heisO W.ψ (G.pS p) (G.pT p) (w i) (S.Z.vac p) := by
  intro D T L sc G W S t p hp k d hk hc hz hP
  obtain ⟨x₀, hx₀, hkx, hfn⟩ := hc
  have he : IsIdemSum d.e (locPl G t) := hP ▸ d.e_is
  have hag := GlobalTheory.T.mem_gridPairWeilLattice_iff_standard_of_half S t p hp d.e he
  have hcos : halfCoset d.e (pairLat G p) k x₀ = halfCoset d.e (latO (G.pS p) (G.pT p)
      (S.N.latS p : Set (Fin (G.pS p).rank → D.host.E)) (S.N.latT p : Set (Fin (G.pT p).rank → D.host.E)) fun _ => True) k x₀ := by
    ext x
    simp only [halfCoset, Set.mem_setOf_eq]
    exact exists_congr fun u => ⟨fun ⟨h1, h2, h3⟩ => ⟨(hag u h2).1 h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨(hag u h2).2 h1, h2, h3⟩⟩
  have hkx' := (hag _ (isHalf_nsmul_of k hx₀)).1 hkx
  have hsb : IsSBHalf d.e (latO (G.pS p) (G.pT p) (S.N.latS p : Set (Fin (G.pS p).rank → D.host.E))
      (S.N.latT p : Set (Fin (G.pT p).rank → D.host.E)) fun _ => True) d.fn := by
    rw [hfn, hcos]
    exact isSBHalf_halfCoset_indicator hk hx₀ hkx'
  obtain ⟨hSd, hTd⟩ := stdSelfDual S.N hp
  have hv := S.Z.vac_is p hp
  obtain ⟨f, hf⟩ : ∃ f, d.IsTheta W (S.N.latS p) (S.N.latT p) (S.Z.vac p) f :=
    VecEx.exists_isThetaAt_of_vac hSd.1 hTd.1 hSd hTd d.e_is hv hsb
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := id hf
  have hfT : f = Tm d.fn := hall Tm hTm
  have hvec : S.Z.vec d = f := by
    rw [Normal.vec, FinDatum.vec_eq W hf, hz, Prod.mk_one_one, map_one]
    rfl
  obtain ⟨n, c, w, h1, h2, h3, h4, h5⟩ := model_coset W.ψ (G.pS p) (G.pT p) (S.N.latS p) (S.N.latT p) hv.1 hSd hTd d.e _
    d.e_is (S.Z.vac p) Tm hTm k hk x₀ hx₀ hkx'
  refine ⟨n, c, w, h1, h2, h3, h4, ?_⟩
  rw [hvec, hfT, hfn, hcos, h5]
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetDatumVector_finite_heisenbergCombination : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ) (t : T) (p : Pair T), DefPair D.R.m p → ∀ (k : ℕ) (d : FinDatum G t p), 0 < k → IsCosetDatum k d → d.z = 1 → d.P = locPl G t → ∃ (n : ℕ) (c : Fin n → Formalism.MainNotions.TaylorLogMetric.Qbar) (w : Fin n → WO (G.pS p) (G.pT p)), (∀ i, k • w i ∈ latO (G.pS p) (G.pT p) (S.N.latS p : Set _) (S.N.latT p : Set _) fun _ => True) ∧ (∀ i, (w i).map (infPart D) = 0) ∧ (∀ i, IsIntegral ℤ ((k : Formalism.MainNotions.TaylorLogMetric.Qbar) ^ (D.R.f * (G.pS p).rank * (G.pT p).rank) * c i)) ∧ (∀ ρ : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ, ∑ i, ‖ρ (c i)‖ ≤ 1) ∧ S.Z.vec d = ∑ i, (c i : ℂ) • heisO W.ψ (G.pS p) (G.pT p) (w i) (S.Z.vac p) := by
  atlas_forward_decl GlobalTheory.RowEx.fourierVec
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.DictFree

open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

noncomputable def conjQ : Qbar →+* Qbar where
  toFun x := ⟨starRingEnd ℂ x, by
    have h : IsAlgebraic ℚ (x : ℂ) := (mem_algebraicClosure_iff).1 x.2
    exact (mem_algebraicClosure_iff).2
      (h.algHom ((Complex.conjAe.restrictScalars ℚ : ℂ ≃ₐ[ℚ] ℂ) : ℂ →ₐ[ℚ] ℂ))⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

noncomputable def oppQ {T : Type} : Pair T → (Qbar →+* Qbar)
  | .chi _ _ => conjQ
  | .core _ => conjQ
  | _ => RingHom.id _

theorem oppQ_coe {T : Type} (p : Pair T) (x : Qbar) : ((oppQ p x : Qbar) : ℂ) = opp p (x : ℂ) := by
  cases p <;> rfl

theorem opp_opp {T : Type} (p : Pair T) (z : ℂ) : opp p (opp p z) = z := by
  cases p <;> simp [opp]

end GlobalTheory.DictFree

namespace GlobalTheory.DictFree
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 MvPolynomial

theorem jetTab_comb {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (W : G.Weil)
    (B : VertexFrames G) (p : Pair T) {f : WO (G.pS p) (G.pT p) → ℂ} (hf : IsThetaFunO W.ψ _ _ f) {n : ℕ}
    (a : Fin n → ℂ) (w : Fin n → WO (G.pS p) (G.pT p)) (hw : ∀ i, (w i).map (infPart D) = 0)
    (X : FinPt G p.small) (Y : FinPt G p.big) (mon : Formalism.L2.Ker.DVar D.what₂.Tau (G.V p.small).rank (G.V p.big).rank →₀ ℕ) :
    jetTab W B p (∑ i, a i • heisO W.ψ _ _ (w i) f) X Y mon = ∑ i, a i * jetTab W B p (heisO W.ψ _ _ (w i) f) X Y mon := by
  have h1 := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D W.ψ W.θ (G.pS p) (G.pT p) W.ψ_std W.θ_is
    (G.cartS W.cart p) (G.onT W.cart p) (G.onS B p) (G.onT B p) f hf n a w hw (monomial (mon.mapDomain (fvar G p)) 1)).1
  have h2 : ∀ i, heisO W.ψ _ _ (w i) (pureTensorO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (G.onS B p) (G.onT B p) f
      (monomial (mon.mapDomain (fvar G p)) 1)) = pureTensorO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (G.onS B p)
      (G.onT B p) (heisO W.ψ _ _ (w i) f) (monomial (mon.mapDomain (fvar G p)) 1) := fun i => by
    have := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D W.ψ W.θ (G.pS p) (G.pT p) W.ψ_std W.θ_is
      (G.cartS W.cart p) (G.onT W.cart p) (G.onS B p) (G.onT B p) f hf 1 (fun _ => 1) (fun _ => w i) (fun _ => hw i)
      (monomial (mon.mapDomain (fvar G p)) 1)).1
    simpa using this
  simp only [jetTab, kerFin, fockIn, GridData.Weil.ker, thetaKO]
  rw [← h1]
  simp only [← h2, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.DictFree

namespace GlobalTheory.DictFree
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 MvPolynomial

theorem differentiable_U {D : D7} (Tr : Tor D) {N N' : ℕ} (s : VC D N N') {G : VC D N N' → ℂ} (hG : Differentiable ℂ G) :
    Differentiable ℂ (Formalism.MainNotions.TaylorLogMetric.U D Tr s G) := by
  unfold Formalism.MainNotions.TaylorLogMetric.U Formalism.MainNotions.TaylorLogMetric.Hf
  fun_prop

theorem dictAt_big : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → Big fun ch => GlobalTheory.SumSize.DictAt ch := by
  intro hP hI
  obtain ⟨CF0, hCF⟩ := GlobalTheory.T.self_dual_lattices_differentiable_operator hP hI
  refine ⟨CF0, fun ε CF hCF0 => ?_⟩
  obtain ⟨x₀, hx⟩ := hCF ε CF hCF0
  refine ⟨x₀, ?_⟩
  intro D large₂ hε hx₀ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt
  have H2 := hx D large₂ hε hx₀ Γ Pl0 T A Ks R F hS ch hIs hAt
  intro t p hp k d hk hcos hz hP' x y
  obtain ⟨Ls, Lt, κ, hLs, hLt, hκ, hdiff, hq, htr⟩ := H2 p hp x y
  obtain ⟨n, c, w, hwL, hwf, hcI, hcN, hvec⟩ := GlobalTheory.T.cosetDatumVector_finite_heisenbergCombination ch.S.toGridChoice t p hp k d hk hcos hz hP'
  choose ζ s hζ hs hjet using fun i => htr k hk (w i) (hwL i)
  refine ⟨Ls, Lt, κ, n, fun i => oppQ p (c i) * ζ i, s, hLs, hLt, hκ, hs, fun i => ?_, fun ρ => ?_, hq, fun mon => ?_⟩
  · obtain ⟨m, hm, hζm⟩ := hζ i
    have hζi : IsIntegral ℤ (ζ i) := ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 hm.ne', by simp [hζm]⟩
    have e : (k : Qbar) ^ (D.R.f * (ch.G.pS p).rank * (ch.G.pT p).rank) * (oppQ p (c i) * ζ i) =
        oppQ p ((k : Qbar) ^ (D.R.f * (ch.G.pS p).rank * (ch.G.pT p).rank) * c i) * ζ i := by
      rw [map_mul, map_pow, map_natCast]; ring
    rw [e]
    exact ((hcI i).map (oppQ p).toIntAlgHom).mul hζi
  · have h1 : ∀ i, ‖ρ (ζ i)‖ = 1 := fun i => by
      obtain ⟨m, hm, hζm⟩ := hζ i
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 (by rw [← norm_pow, ← map_pow, hζm, map_one, norm_one])
    calc ∑ i, ‖ρ (oppQ p (c i) * ζ i)‖ = ∑ i, ‖(ρ.comp (oppQ p)) (c i)‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul, norm_mul, h1, mul_one]; rfl
      _ ≤ 1 := hcN _
  · have hvac : IsThetaFunO ch.W.ψ _ _ (ch.S.Z.vac p) := (ch.S.Z.vac_is p hp).2.theta
    show jetTab ch.W ch.S.N.frC p (ch.S.Z.vec d) _ _ mon = _
    rw [hvec, jetTab_comb ch.W ch.S.N.frC p hvac _ w hwf]
    simp only [hjet]
    set Gt := Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _)
      (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p) with hGt
    set M := MvPolynomial.monomial (mon.mapDomain (fvar ch.G p)) (1 : ℂ)
    set Per := (mon.mapDomain (fvar ch.G p)).prod fun v e => period ch.S.Z.δ v.1 ^ e
    have hGi : ∀ i, Differentiable ℂ (fun z => κ * ((ζ i : ℂ) * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK ch.S.Z.δ) (s i) Gt z)) :=
      fun i => ((differentiable_U _ (s i) hdiff).const_mul _).const_mul _
    have hfun : (fun z => κ * ∑ i, ((oppQ p (c i) * ζ i : Qbar) : ℂ) * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK ch.S.Z.δ) (s i) Gt z) =
        ∑ i ∈ Finset.univ, ((oppQ p (c i) : Qbar) : ℂ) • fun z => κ * ((ζ i : ℂ) * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK ch.S.Z.δ) (s i) Gt z) := by
      funext z
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast; ring
    rw [hfun, GlobalTheory.NormSum.RepInv.applyAt0_sum _ _ _ hGi, Finset.mul_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [oppQ_coe]
    simp only [map_mul, opp_opp]
    ring

end GlobalTheory.DictFree

end
end
