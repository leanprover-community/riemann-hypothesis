import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelTensorIntegralIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIntegralMatrixIndicatorMemSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIndicatorGivesLocalVacuumSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunOPlaceModelApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunSplitPlaceSchroedingerModel
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsLatInd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletedHomLatticeStableSplitIdempotent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatTensorHalfAddPlaceIdempotent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatMulSplitHalfLatticeCoordinatesIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemHomLatticeOfIntegralFrameCoords
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndicatorLocalHomLatticeMemSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeAtPlacesCongrLocalLattices
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedSplitPlaceOfIsHalfConjSumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointWeilCharConductorOneOfUnits

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.SplitOrth

theorem place_mul_place {D : D7} {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v' ε') (hv : v ≠ v') : ε * ε' = 0 := by
  obtain ⟨α, rfl, -, h0⟩ := h
  obtain ⟨β, rfl, -, k0⟩ := h'
  refine Prod.ext (mul_zero (0 : Ainf D.host.F)) (show α * β = 0 from FiniteAdeleRing.ext _ fun w => ?_)
  change evalV D.host.F w (α * β) = evalV D.host.F w 0
  rw [map_mul, map_zero]
  by_cases hw : w = v
  · rw [k0 w (hw ▸ hv), mul_zero]
  · rw [h0 w hw, zero_mul]

theorem split_mul_split : ∀ (D : D7) (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (q : SplitPt D k) (q' : SplitPt D k'), q.v ≠ q'.v → q.e * q'.e = 0 := by
  intro D k k' _ _ _ _ _ _ _ _ q q' hv
  obtain ⟨ε, hε, he⟩ := q.above
  obtain ⟨ε', hε', he'⟩ := q'.above
  have h1 : q.e * q.e = q.e := q.split.1
  have h2 : q.e * cA D q.e = 0 := q.split.2.1
  have h1' : q'.e * q'.e = q'.e := q'.split.1
  have h2' : q'.e * cA D q'.e = 0 := q'.split.2.1
  have a : q.e = q.e * algebraMap _ _ ε := by rw [← he, mul_add, h1, h2, add_zero]
  have a' : q'.e = q'.e * algebraMap _ _ ε' := by rw [← he', mul_add, h1', h2', add_zero]
  rw [a, a', mul_mul_mul_comm, ← map_mul, place_mul_place hε hε' hv, map_zero, mul_zero]

end GlobalTheory.SplitOrth
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceIdempotent_mul_eq_zero_of_ne_place : ∀ (D : D7) (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (q : SplitPt D k) (q' : SplitPt D k'), q.v ≠ q'.v → q.e * q'.e = 0 := by
  atlas_forward_decl GlobalTheory.SplitOrth.split_mul_split
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.PlaceSumTheta

set_option synthInstance.maxHeartbeats 400000 in

theorem isThetaFunO_sum_placeModel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), Vac ψ S T M M' (fun _ => True) f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (∑ i, (L i).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T' → ∀ Φ, IsSBHalf (∑ i, (L i).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ → IsThetaFunO ψ S T (T' Φ) := by
  intro D ψ hψ S T M M' hM hM' n L inj f₀ T' hvac hT' Φ hΦ
  have hidem : (∑ i, (L i).q.e) * (∑ i, (L i).q.e) = ∑ i, (L i).q.e := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single i
      (fun j _ h => GlobalTheory.SeeSaw.LocPlModel.e_mul_e _ _ (fun h' => h (inj h').symm)) (fun h => (h (Finset.mem_univ _)).elim)]
    exact (L i).q.split.1
  have hinf : infPart D (∑ i, (L i).q.e) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => GlobalTheory.LocMod.LinTheta.infPart_of_isSplitIdem (L i).q.split
  exact GlobalTheory.PlaceThetaVal.isThetaFunO_placeModel_apply hψ S T M M' hM hM' _ f₀ Φ T' hidem hinf hT' hvac.1 hΦ

end GlobalTheory.PlaceSumTheta
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunO_splitPlaces_schrodingerModel_sum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), Vac ψ S T M M' (fun _ => True) f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (∑ i, (L i).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T' → ∀ Φ, IsSBHalf (∑ i, (L i).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ → IsThetaFunO ψ S T (T' Φ) := by
  atlas_forward_decl GlobalTheory.PlaceSumTheta.isThetaFunO_sum_placeModel
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.TensorLatO

theorem isSBHalf_tensorAt_of_bounds {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : Place D k) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y']
    [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (L : AddSubgroup (WO S T))
    (e : AE D) (he : e * p.e = 0) (hMap : ∀ u ∈ L, u.map (fun a => p.e * a) ∈ L)
    (A B : ℕ) (hA : 0 < A) (hB : 0 < B)
    (hAL : ∀ X : Matrix Y Y' k, (∀ r q, X r q ∈ 𝒪[k]) → A • p.up FS FT X ∈ L)
    (hBL : ∀ u ∈ L, ∀ r q, (B : k) * p.down FS FT u r q ∈ 𝒪[k])
    (Φ : WO S T → ℂ) (hΦ : IsSBHalf e L Φ) (Ψ : Matrix Y Y' k → ℂ) (hΨ : Ψ ∈ SB (Matrix Y Y' k)) :
    IsSBHalf (e + p.e) L (p.tensorAt FS FT Φ Ψ) := by
  classical
  unfold IsSBHalf at hΦ ⊢
  obtain ⟨hΦs, kΦ, hkΦ, hΦi, hΦl⟩ := hΦ
  obtain ⟨N, hN, hΨi, hΨl⟩ := GlobalTheory.SBUnif.uniform k Y Y' Ψ hΨ
  have hud : ∀ u : WO S T, p.up FS FT (p.down FS FT u) = u.map (fun a => p.e * a) := by
    intro u
    unfold Place.down Place.up
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
    ext i j
    exact p.ι_π _
  have hupn : ∀ (n : ℕ) (X : Matrix Y Y' k), p.up FS FT (n • X) = n • p.up FS FT X :=
    fun n X => map_nsmul (Witness.upH p FS FT) n X
  have hdownn : ∀ (n : ℕ) (u : WO S T), p.down FS FT (n • u) = n • p.down FS FT u :=
    fun n u => map_nsmul (Witness.downH p FS FT) n u
  have hsupp : ∀ t, p.tensorAt FS FT Φ Ψ t ≠ 0 →
      Φ (t - p.up FS FT (p.down FS FT t)) ≠ 0 ∧ Ψ (p.down FS FT t) ≠ 0 := fun t ht =>
    ⟨left_ne_zero_of_mul ht, right_ne_zero_of_mul ht⟩
  refine ⟨fun t ht => ?_, kΦ * (N * B * A), Nat.mul_pos hkΦ (Nat.mul_pos (Nat.mul_pos hN hB) hA),
    fun u hu hhu t => ?_, fun t ht => ?_⟩
  · obtain ⟨h1, -⟩ := hsupp t ht
    have hs := hΦs _ h1
    have hw := Witness.up_half p FS FT (p.down FS FT t)
    intro i j
    have a1 := hs i j
    have a2 := hw i j
    have e1 : t i j = (t - p.up FS FT (p.down FS FT t)) i j + p.up FS FT (p.down FS FT t) i j := by
      rw [Matrix.sub_apply, sub_add_cancel]
    rw [e1]
    linear_combination (1 - p.e) * a1 + (1 - e) * a2 +
      (p.up FS FT (p.down FS FT t) i j + (t - p.up FS FT (p.down FS FT t)) i j) * he
  · set X := p.down FS FT u with hX
    have hXL : p.up FS FT X ∈ L := by rw [hX, hud]; exact hMap u hu
    have hYi : ∀ r q, (((kΦ * A : ℕ) : k) • ((B : k) • X)) r q ∈ 𝒪[k] := fun r q => by
      rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      exact mul_mem (natCast_mem _ _) (hBL u hu r q)
    have hd : p.down FS FT (t + (kΦ * (N * B * A)) • u) = p.down FS FT t + (kΦ * (N * B * A)) • X := by
      rw [Witness.down_add, hdownn]
    have e3 : p.down FS FT t + (kΦ * (N * B * A)) • X =
        p.down FS FT t + (N : k) • (((kΦ * A : ℕ) : k) • ((B : k) • X)) := by
      congr 1
      rw [← Nat.cast_smul_eq_nsmul k, smul_smul, smul_smul]
      congr 1
      push_cast; ring
    set w : WO S T := (N * B * A) • (u - p.up FS FT X) with hw
    have e2 : t + (kΦ * (N * B * A)) • u - p.up FS FT (p.down FS FT t + (kΦ * (N * B * A)) • X) =
        (t - p.up FS FT (p.down FS FT t)) + kΦ • w := by
      rw [Witness.up_add, hupn, hw, smul_smul, nsmul_sub]
      abel
    have hwL : w ∈ L := nsmul_mem (sub_mem hu hXL) _
    have hwH : IsHalf e w := by
      intro i j
      rw [hw, hX, hud, Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, nsmul_eq_mul]
      linear_combination ((N * B * A : ℕ) : AE D) * hhu i j - ((N * B * A : ℕ) : AE D) * u i j * he
    show Φ (t + (kΦ * (N * B * A)) • u - p.up FS FT (p.down FS FT (t + (kΦ * (N * B * A)) • u))) *
        Ψ (p.down FS FT (t + (kΦ * (N * B * A)) • u)) =
      Φ (t - p.up FS FT (p.down FS FT t)) * Ψ (p.down FS FT t)
    rw [hd, e2, e3, hΦi w hwL hwH, hΨi _ _ hYi]
  · obtain ⟨h1, h2⟩ := hsupp t ht
    have a1 := hΦl _ h1
    have a2 : A • p.up FS FT (N • p.down FS FT t) ∈ L := hAL _ fun r q => by
      rw [Matrix.smul_apply, nsmul_eq_mul]; exact hΨl _ h2 r q
    rw [hupn] at a2
    have e1 : (kΦ * (N * B * A)) • t = (N * B * A) • (kΦ • (t - p.up FS FT (p.down FS FT t))) +
        kΦ • (B • (A • (N • p.up FS FT (p.down FS FT t)))) := by
      rw [smul_smul, smul_smul, smul_smul, smul_smul, mul_comm (N * B * A) kΦ,
        show kΦ * B * A * N = kΦ * (N * B * A) by ring, ← nsmul_add, sub_add_cancel]
    rw [e1]
    exact add_mem (nsmul_mem a1 _) (nsmul_mem (nsmul_mem a2 B) kΦ)

end GlobalTheory.TensorLatO
end

noncomputable section

namespace GlobalTheory.TensorLatO

theorem isSBHalf_tensorAt_latO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (P : LocPl ψ S T M M') (e : AE D), e * P.q.e = 0 → ∀ Φ : WO S T → ℂ, IsSBHalf e (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ → ∀ Ψ ∈ SB (Matrix P.Y P.Y' P.k), IsSBHalf (e + P.q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) ((ofSplit P.q).tensorAt P.FS P.FT Φ Ψ) := by
  classical
  intro D ψ S T M M' hS hT P e he Φ hΦ Ψ hΨ
  set L := latO S T (M : Set (Fin S.rank → D.host.E)) (M' : Set (Fin T.rank → D.host.E)) fun _ => True with hL
  set q := P.q with hq
  have hee : q.e * q.e = q.e := q.split.1

  have hMap : ∀ u ∈ L, u.map (fun a => (ofSplit q).e * a) ∈ L := fun u hu => by
    have h := GlobalTheory.SplitScalar.idem_smul_mem (LS := (M : Set (Fin S.rank → D.host.E)))
      (LT := (M' : Set (Fin T.rank → D.host.E))) hee u hu
    convert h using 1
    ext i j
    rfl

  obtain ⟨N₀, hN₀, h₀⟩ := GlobalTheory.FinPl.RdInt.exists_nat_mul_mem_fin
    (Sum.elim (fun x : Fin T.rank × P.Y => P.FT.β x.1 x.2) (fun x : P.Y' × Fin S.rank => P.FS.γ x.1 x.2))
  obtain ⟨K, hK, hmul⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hS.1 hT.1
  have hAL : ∀ X : Matrix P.Y P.Y' P.k, (∀ r q, X r q ∈ 𝒪[P.k]) →
      (K * (N₀ * N₀)) • (ofSplit q).up P.FS P.FT X ∈ L := by
    intro X hX
    have hent := GlobalTheory.FinPl.RdInt.entry_mem P.FT.β P.FS.γ (fun i a => h₀ (Sum.inl (i, a)))
      (fun a j => h₀ (Sum.inr (a, j))) X hX
    have hh : IsHalf q.e ((N₀ * N₀) • (ofSplit q).up P.FS P.FT X) := fun i j => by
      rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm]
      exact congrArg _ (Witness.up_half (ofSplit q) P.FS P.FT X i j)
    have hui : ∀ i j, toEAf D (((N₀ * N₀) • (ofSplit q).up P.FS P.FT X) i j) ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E := by
      intro i j
      have h1 : ((N₀ * N₀) • (ofSplit q).up P.FS P.FT X) i j =
          q.sec (((N₀ * N₀ : ℕ) : P.k) * (P.FT.β * X * P.FS.γ) i j) := by
        rw [← nsmul_eq_mul, map_nsmul]
        rfl
      rw [h1]
      exact GlobalTheory.PlaceCoord.toEAf_mem ((q.int_iff _).1 (hent i j))
    have h1 := hmul _ (GlobalTheory.PlaceDatum.infPart_of_half (GlobalTheory.PlaceCoord.infPart_split q.split) hh) hui
    rwa [mul_nsmul']

  obtain ⟨M₀, hM₀, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.1.fg hT.1.fg
  obtain ⟨K₁, hK₁, h₁⟩ := GlobalTheory.FinPl.RdBound.exists_nat_mul_mem_family
    (fun x : P.Y × Fin T.rank => P.FT.γ x.1 x.2)
  obtain ⟨K₂, hK₂, h₂⟩ := GlobalTheory.FinPl.RdBound.exists_nat_mul_mem_family
    (fun x : Fin S.rank × P.Y' => P.FS.β x.1 x.2)
  have hBL : ∀ u ∈ L, ∀ i j, ((K₁ * M₀ * K₂ : ℕ) : P.k) * (ofSplit q).down P.FS P.FT u i j ∈ 𝒪[P.k] := by
    intro u hu i j
    have heu := GlobalTheory.SplitScalar.idem_smul_mem (LS := (M : Set (Fin S.rank → D.host.E)))
      (LT := (M' : Set (Fin T.rank → D.host.E))) hee u hu
    have hint : ∀ a b, (M₀ : P.k) * q.pr (u a b) ∈ 𝒪[P.k] := fun a b => by
      rw [q.int_iff]
      have h1 : q.sec ((M₀ : P.k) * q.pr (u a b)) = (M₀ : AE D) * (q.e • u) a b := by
        rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, q.sec_pr]
        rfl
      rw [h1]
      refine GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_
      rw [RingHom.map_mul, map_natCast]
      exact hden _ heu a b
    change (_ : P.k) * (P.FT.γ * Matrix.map u q.pr * P.FS.β) i j ∈ 𝒪[P.k]
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine sum_mem fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine sum_mem fun a _ => ?_
    have e : ((K₁ * M₀ * K₂ : ℕ) : P.k) * (P.FT.γ i a * Matrix.map u q.pr a b * P.FS.β b j) =
        ((K₁ : P.k) * P.FT.γ i a) * ((M₀ : P.k) * q.pr (u a b)) * ((K₂ : P.k) * P.FS.β b j) := by
      rw [Matrix.map_apply]; push_cast; ring
    rw [e]
    exact mul_mem (mul_mem (h₁ (i, a)) (hint a b)) (h₂ (b, j))
  exact isSBHalf_tensorAt_of_bounds (ofSplit q) P.FS P.FT L e he hMap (K * (N₀ * N₀)) (K₁ * M₀ * K₂)
    (Nat.mul_pos hK (Nat.mul_pos hN₀ hN₀)) (Nat.mul_pos (Nat.mul_pos hK₁ hM₀) hK₂) hAL hBL Φ hΦ Ψ hΨ

end GlobalTheory.TensorLatO
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhatHalf_tensor_split_place_selfDual : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (P : LocPl ψ S T M M') (e : AE D), e * P.q.e = 0 → ∀ Φ : WO S T → ℂ, IsSBHalf e (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ → ∀ Ψ ∈ SB (Matrix P.Y P.Y' P.k), IsSBHalf (e + P.q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) ((ofSplit P.q).tensorAt P.FS P.FT Φ Ψ) := by
  atlas_forward_decl GlobalTheory.TensorLatO.isSBHalf_tensorAt_latO
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indicator_localHomLattice_mem_schwartzBruhat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (P : LocPl ψ S T M M'), Set.indicator {x | (ofSplit P.q).up P.FS P.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = P.q.v)} (fun _ => (1 : ℂ)) ∈ SB (Matrix P.Y P.Y' P.k) := by
  first | exact @GlobalTheory.LatIndSB.indicator_latO_mem_SB | exact GlobalTheory.LatIndSB.indicator_latO_mem_SB | (intros; apply GlobalTheory.LatIndSB.indicator_latO_mem_SB <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.LatIdemVac

variable {D : D7}

theorem latO_at_le {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (v : Pl D) : latO S T LS LT (· = v) ≤ latO S T LS LT fun _ => True := by
  unfold latO
  refine AddSubgroup.closure_mono ?_
  rintro w ⟨α, hα, -, rest⟩
  exact ⟨α, hα, fun _ h => absurd trivial h, rest⟩

theorem pairA_zero_mul (a b : Af D.host.F) :
    pairA D.host.F 0 a * pairA D.host.F 0 b = pairA D.host.F 0 (a * b) := by
  show ((0 : Ainf D.host.F), a) * ((0 : Ainf D.host.F), b) = ((0 : Ainf D.host.F), a * b)
  rw [Prod.mk_mul_mk, mul_zero]

theorem placeIdem_mul_mem {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    (Matrix.of fun i j => algebraMap (AF D.host.F) (AE D) ε * u i j : WO S T) ∈ latO S T LS LT (· = v) := by
  obtain ⟨α₀, rfl, h1, h0⟩ := hε
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α₀ * α, fun w => ?_, fun w hw => ?_, a, ha, s, hs, t, ht, ?_⟩
    · rw [map_mul]
      by_cases hwv : w = v
      · subst hwv; rw [h1, one_mul]; exact hα w
      · rw [h0 w hwv, zero_mul]; exact zero_mem _
    · rw [map_mul, h0 w hw, zero_mul]
    · ext i j
      simp only [Matrix.of_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        Algebra.algebraMap_self, RingHom.id_apply, pairA_zero_mul]
  | zero =>
    convert (latO S T LS LT (· = v)).zero_mem using 1
    ext i j; simp
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    ext i j; simp only [Matrix.of_apply, Matrix.add_apply, mul_add]
  | neg x _ hx =>
    convert neg_mem hx using 1
    ext i j; simp only [Matrix.of_apply, Matrix.neg_apply, mul_neg]

theorem splitIdem_mul_mem {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) {S T : HSp D} (LS : Lat S) (LT : Lat T) {u : WO S T}
    (hu : u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    u.map (fun a => q.e * a) ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) := by
  obtain ⟨ε, hε, hsum⟩ := q.above
  have h := (GlobalTheory.SplitVac.idem_latO D k q S T LS LT _ (placeIdem_mul_mem _ _ hε hu)).1
  convert h using 1
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply]
  rw [← hsum, ← mul_assoc, mul_add, q.split.1, q.split.2.1, add_zero]

end GlobalTheory.LatIdemVac

namespace GlobalTheory.LatIdemVac

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

def tensorWith (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Ψ : Matrix Y Y' k → ℂ) :
    (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun Φ := p.tensorAt FS FT Φ Ψ
  map_add' Φ Φ' := by
    funext t
    simp only [Place.tensorAt, Pi.add_apply, add_mul]
  map_smul' c Φ := by
    funext t
    simp only [Place.tensorAt, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem tensorWith_apply (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Ψ : Matrix Y Y' k → ℂ) (Φ : WO S T → ℂ) :
    tensorWith p FS FT Ψ Φ = p.tensorAt FS FT Φ Ψ := rfl

theorem tensorAt_trans (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D} (he : e * p.e = 0)
    (Φ : WO S T → ℂ) (Ψ : Matrix Y Y' k → ℂ) {x : WO S T} (hx : IsHalf e x) :
    p.tensorAt FS FT (fun t => Φ (t + x)) Ψ = fun t => p.tensorAt FS FT Φ Ψ (t + x) := by
  funext t
  simp only [Place.tensorAt]
  rw [GlobalTheory.LocMod.Witness.down_add p FS FT t x, GlobalTheory.LocMod.TOneModel.down_half_zero p FS FT he hx, add_zero,
    sub_add_eq_add_sub]

theorem tensorAt_modul (ψ : AddChar (AF D.host.F) ℂ) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D}
    (he : e * p.e = 0) (Φ : WO S T → ℂ) (Ψ : Matrix Y Y' k → ℂ) {y : WO S T} (hy : IsHalf (cA D e) y) :
    p.tensorAt FS FT (fun t => ψ (symplO S T t y) * Φ t) Ψ = fun t => ψ (symplO S T t y) * p.tensorAt FS FT Φ Ψ t := by
  funext t
  simp only [Place.tensorAt]
  rw [GlobalTheory.LocMod.TOneModel.symplO_sub_half p he t (GlobalTheory.LocMod.Witness.up_half p FS FT _) hy, mul_assoc]

open Classical in

theorem tensorAt_halfInd (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D} (he : e * p.e = 0)
    (Λ Λv : AddSubgroup (WO S T)) (hle : Λv ≤ Λ) (hstab : ∀ t ∈ Λ, t.map (fun a => p.e * a) ∈ Λv) :
    p.tensorAt FS FT ((1 : ℂ) • halfInd e Λ) (Set.indicator {x | p.up FS FT x ∈ Λv} fun _ => 1) =
      (1 : ℂ) • halfInd (e + p.e) Λ := by
  funext t
  simp only [one_smul, Place.tensorAt]
  rw [GlobalTheory.LocMod.TOneModel.up_down_eq p FS FT t, Set.indicator_apply]
  simp only [Set.mem_setOf_eq, GlobalTheory.LocMod.TOneModel.up_down_eq p FS FT t]
  set M : WO S T := t.map (fun a => p.e * a) with hMdef
  have key : ((t - M ∈ Λ ∧ IsHalf e (t - M)) ∧ M ∈ Λv) ↔ (t ∈ Λ ∧ IsHalf (e + p.e) t) := by
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨by simpa using add_mem h1 (hle h3), fun i j => ?_⟩
      have h := h2 i j
      simp only [hMdef, Matrix.sub_apply, Matrix.map_apply] at h
      linear_combination h + t i j * he
    · rintro ⟨h1, h2⟩
      have h3 : M ∈ Λv := hstab t h1
      refine ⟨⟨sub_mem h1 (hle h3), fun i j => ?_⟩, h3⟩
      simp only [hMdef, Matrix.sub_apply, Matrix.map_apply]
      linear_combination h2 i j - t i j * he
  unfold halfInd
  by_cases hR : t ∈ Λ ∧ IsHalf (e + p.e) t
  · obtain ⟨⟨h1, h2⟩, h3⟩ := key.2 hR
    rw [if_pos hR, if_pos ⟨h1, h2⟩, if_pos h3, mul_one]
  · rw [if_neg hR]
    by_cases h3 : M ∈ Λv
    · rw [if_pos h3, mul_one, if_neg fun h => hR (key.1 ⟨h, h3⟩)]
    · rw [if_neg h3, mul_zero]

end GlobalTheory.LatIdemVac

namespace GlobalTheory.LatIdemVac

theorem isPlaceModel_tensorLat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (P : LocPl ψ S T M M') (e : AE D), e * P.q.e = 0 → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) (e + P.q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T' → ∃ T'' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T'' ∧ ∀ Φ, T'' Φ = T' ((ofSplit P.q).tensorAt P.FS P.FT Φ (Set.indicator {x | (ofSplit P.q).up P.FS P.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = P.q.v)} fun _ => 1)) := by
  intro D ψ S T M M' hM hM' P e he f₀ T' hT'
  set p := ofSplit P.q with hp
  set Ψ : Matrix P.Y P.Y' P.k → ℂ :=
    Set.indicator {x | p.up P.FS P.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = P.q.v)} fun _ => 1 with hΨ
  have hpe : p.e = P.q.e := rfl
  have he' : e * p.e = 0 := he
  have hΨsb : Ψ ∈ SB (Matrix P.Y P.Y' P.k) := GlobalTheory.T.indicator_localHomLattice_mem_schwartzBruhat D ψ S T M M' hM hM' P
  have hsb : ∀ Φ, IsSBHalf e (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ →
      IsSBHalf (e + P.q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) (p.tensorAt P.FS P.FT Φ Ψ) :=
    fun Φ hΦ => GlobalTheory.T.schwartzBruhatHalf_tensor_split_place_selfDual D ψ S T M M' hM hM' P e he Φ hΦ Ψ hΨsb
  refine ⟨T' ∘ₗ tensorWith p P.FS P.FT Ψ, ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩, fun Φ => rfl⟩
  · rw [LinearMap.comp_apply, tensorWith_apply, tensorAt_trans p P.FS P.FT he' Φ Ψ hx]
    exact hT'.trans _ (hsb Φ hΦ) x (GlobalTheory.LocMod.TOneModel.half_sum p he' hx)
  · rw [LinearMap.comp_apply, tensorWith_apply, tensorAt_modul p ψ P.FS P.FT he' Φ Ψ hy]
    exact hT'.modul _ (hsb Φ hΦ) y (GlobalTheory.LocMod.TOneModel.half_sum_conj p he' hy)
  · rw [LinearMap.comp_apply, tensorWith_apply, tensorAt_halfInd p P.FS P.FT he' _ _ (latO_at_le _ _ P.q.v)
      (fun t ht => splitIdem_mul_mem P.q M M' ht)]
    exact hT'.vac

end GlobalTheory.LatIdemVac

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPlaceModel_tensor_splitPlaceLatticeIndicator : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (P : LocPl ψ S T M M') (e : AE D), e * P.q.e = 0 → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) (e + P.q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T' → ∃ T'' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T'' ∧ ∀ Φ, T'' Φ = T' ((ofSplit P.q).tensorAt P.FS P.FT Φ (Set.indicator {x | (ofSplit P.q).up P.FS P.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = P.q.v)} fun _ => 1)) := by
  atlas_forward_decl GlobalTheory.LatIdemVac.isPlaceModel_tensorLat
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPoint_weilChar_conductor_one_of_units : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → q.UnitAA → ∃ ψk : AddChar k Circle, (ofSplit q).IsChar ψ ψk ∧ HasConductor ψk 1 := by
  first | exact @GlobalTheory.SplitWeilChar.weil_char_conductor_one | exact GlobalTheory.SplitWeilChar.weil_char_conductor_one | (intros; apply GlobalTheory.SplitWeilChar.weil_char_conductor_one <;> assumption)
end

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.VecProd

section Gen
variable {D : D7}

theorem isHalf_add_iff {a b : AE D} (hab : b * a = 0) {m n : ℕ} (t : Mx D m n) :
    IsHalf (a + b) t ↔ IsHalf b (t - t.map (fun x => a * x)) := by
  constructor
  · intro h i j
    have h1 := h i j
    simp only [Matrix.sub_apply, Matrix.map_apply]
    rw [mul_sub, ← mul_assoc, hab, zero_mul, sub_zero]
    linear_combination h1
  · intro h i j
    have h1 := h i j
    simp only [Matrix.sub_apply, Matrix.map_apply] at h1
    rw [mul_sub, ← mul_assoc, hab, zero_mul, sub_zero] at h1
    linear_combination h1

theorem isHalf_zero_iff {m n : ℕ} (t : Mx D m n) : IsHalf (0 : AE D) t ↔ t = 0 := by
  constructor
  · intro h
    ext i j
    have h1 := h i j
    rw [zero_mul] at h1
    simpa using h1.symm
  · rintro rfl i j
    simp

theorem half_add_of_right {a b : AE D} (hab : b * a = 0) {m n : ℕ} {w : Mx D m n} (hw : IsHalf a w) :
    IsHalf (b + a) w := by
  intro i j
  have h : b * w i j = 0 := by rw [← hw i j, ← mul_assoc, hab, zero_mul]
  rw [add_mul, h, zero_add, hw i j]

theorem half_conj_add_of_right {a b : AE D} (hab : b * a = 0) {m n : ℕ} {y : Mx D m n} (hy : IsHalf (cA D a) y) :
    IsHalf (cA D (b + a)) y := by
  intro i j
  have h : cA D b * y i j = 0 := by rw [← hy i j, ← mul_assoc, ← map_mul, hab, map_zero, zero_mul]
  rw [map_add, add_mul, h, zero_add, hy i j]

theorem symplO_sub {S T : HSp D} (x w y : WO S T) :
    symplO S T (x - w) y = symplO S T x y - symplO S T w y := by
  have h : hO S T (x - w) y = hO S T x y - hO S T w y := by
    simp only [hO, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
  unfold symplO
  rw [h, mul_sub, map_sub]

theorem hO_zero' {S T : HSp D} {a b : AE D} (hab : b * a = 0) {w y : WO S T} (hw : IsHalf a w)
    (hy : IsHalf (cA D b) y) : hO S T w y = 0 := by
  unfold hO
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun c _ =>
    Finset.sum_eq_zero fun d _ => ?_
  have h1 : cA D (y c j) = b * cA D (y c j) := by
    conv_lhs => rw [← hy c j, map_mul, Formalism.L2.Theta.cA_cA]
  rw [h1, ← hw d i]
  linear_combination (incA D (S.gram⁻¹ i j) * cA D (y c j) * incA D (T.gram c d) * w d i) * hab

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem down_sub_mul (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) {a : AE D}
    (ha : a * p.e = 0) (t : WO S T) :
    p.down FS FT (t - t.map (fun x => a * x)) = p.down FS FT t := by
  have h0 : p.π a = 0 := TOneModel.pi_of_mul p ha
  unfold Place.down
  have h : (t - t.map (fun x => a * x) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π =
      (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π := by
    ext i j
    simp [Matrix.map_apply, map_sub, map_mul, h0]
  rw [h]

theorem up_add (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (x y : Matrix Y Y' k) :
    p.up FS FT (x + y) = p.up FS FT x + p.up FS FT y := by
  unfold Place.up
  rw [Matrix.mul_add, Matrix.add_mul]
  ext i j
  simp [Matrix.map_apply, map_add]

theorem down_up (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (x : Matrix Y Y' k) :
    p.down FS FT (p.up FS FT x) = x := by
  unfold Place.up Place.down
  have h : ((FT.β * x * FS.γ).map p.ι).map p.π = FT.β * x * FS.γ := by
    ext i j
    simp [Matrix.map_apply, p.π_ι]
  rw [h]
  calc FT.γ * (FT.β * x * FS.γ) * FS.β = (FT.γ * FT.β) * x * (FS.γ * FS.β) := by simp only [Matrix.mul_assoc]
    _ = x := by rw [FT.γβ, FS.γβ, Matrix.one_mul, Matrix.mul_one]

theorem tensorAt_shift (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (Φ : WO S T → ℂ)
    (Ψ : Matrix Y Y' k → ℂ) (x : Matrix Y Y' k) :
    p.tensorAt FS FT Φ (fun t => Ψ (t + x)) = fun t => p.tensorAt FS FT Φ Ψ (t + p.up FS FT x) := by
  funext t
  simp only [Place.tensorAt]
  rw [Witness.down_add p FS FT t (p.up FS FT x), down_up, up_add]
  congr 2
  abel

theorem tensorAt_modul (ψ : AddChar (AF D.host.F) ℂ) (FS : GlobalTheory.LocMod.Frame k S.rank Y')
    (FT : GlobalTheory.LocMod.Frame k T.rank Y) {e : AE D} (he : e * p.e = 0) (Φ : WO S T → ℂ)
    (hΦ : ∀ t, Φ t ≠ 0 → IsHalf e t) (Ψ : Matrix Y Y' k → ℂ) {y : WO S T} (hy : IsHalf (cA D p.e) y) :
    p.tensorAt FS FT Φ (fun t => ψ (symplO S T (p.up FS FT t) y) * Ψ t) =
      fun t => ψ (symplO S T t y) * p.tensorAt FS FT Φ Ψ t := by
  funext t
  simp only [Place.tensorAt]
  by_cases h0 : Φ (t - p.up FS FT (p.down FS FT t)) = 0
  · simp [h0]
  · have hh := hΦ _ h0
    have hz : symplO S T (t - p.up FS FT (p.down FS FT t)) y = 0 := by
      unfold symplO
      rw [hO_zero' (a := e) (b := p.e) (by rw [mul_comm]; exact he) hh hy, mul_zero, map_zero]
    have hs := symplO_sub t (p.up FS FT (p.down FS FT t)) y
    rw [hz] at hs
    have h2 : symplO S T t y = symplO S T (p.up FS FT (p.down FS FT t)) y := by linear_combination -hs
    rw [h2]
    ring

theorem tensorL_isModel (ψ : AddChar (AF D.host.F) ℂ) (FS : GlobalTheory.LocMod.Frame k S.rank Y')
    (FT : GlobalTheory.LocMod.Frame k T.rank Y) (e : AE D) (he : e * p.e = 0) (Λ : AddSubgroup (WO S T))
    (Φ : WO S T → ℂ) (hΦ : ∀ t, Φ t ≠ 0 → IsHalf e t) (f₀ : WO S T → ℂ)
    (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ))
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (e + p.e) Λ 1 f₀ T')
    (hθ : ∀ Φ', IsSBHalf (e + p.e) Λ Φ' → IsThetaFunO ψ S T (T' Φ'))
    (hsb : ∀ Ψ ∈ SB (Matrix Y Y' k), IsSBHalf (e + p.e) Λ (p.tensorAt FS FT Φ Ψ)) :
    p.IsModel ψ FS FT (T' ∘ₗ p.tensorL FS FT Φ) := by
  refine ⟨fun Ψ => hθ _ (hsb Ψ.1 Ψ.2), fun x Ψ Ψ' h => ?_, fun y hy Ψ Ψ' h => ?_⟩
  · have hfun : (Ψ' : Matrix Y Y' k → ℂ) = fun t => (Ψ : Matrix Y Y' k → ℂ) (t + x) := funext h
    simp only [LinearMap.comp_apply, Place.tensorL_apply]
    rw [hfun, tensorAt_shift]
    exact hT.trans _ (hsb Ψ.1 Ψ.2) _ (half_add_of_right he (Witness.up_half p FS FT x))
  · have hfun : (Ψ' : Matrix Y Y' k → ℂ) = fun t => ψ (symplO S T (p.up FS FT t) y) * (Ψ : Matrix Y Y' k → ℂ) t :=
      funext h
    simp only [LinearMap.comp_apply, Place.tensorL_apply]
    rw [hfun, tensorAt_modul p ψ FS FT he Φ hΦ _ hy]
    exact hT.modul _ (hsb Ψ.1 Ψ.2) _ (half_conj_add_of_right he hy)

end Gen

end GlobalTheory.VecProd

namespace GlobalTheory.VecProd

section Fam
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : Lat S} {M' : Lat T}

theorem orth_succ {n : ℕ} (L : Fin (n+1) → LocPl ψ S T M M') (hinj : Function.Injective fun i => (L i).q.v)
    (i : Fin n) : (L 0).q.e * (L i.succ).q.e = 0 :=
  GlobalTheory.T.splitPlaceIdempotent_mul_eq_zero_of_ne_place D _ _ (L 0).q (L i.succ).q fun h => Fin.succ_ne_zero i (hinj h).symm

theorem orth_sum {n : ℕ} (L : Fin (n+1) → LocPl ψ S T M M') (hinj : Function.Injective fun i => (L i).q.v) :
    (∑ i : Fin n, (L i.succ).q.e) * (L 0).q.e = 0 := by
  rw [Finset.sum_mul]
  exact Finset.sum_eq_zero fun i _ => by rw [mul_comm]; exact orth_succ L hinj i

theorem prodDat_zero (L : Fin 0 → LocPl ψ S T M M') (Λ : AddSubgroup (WO S T)) :
    prodDat L = halfInd (0 : AE D) Λ := by
  funext x
  unfold prodDat halfInd
  have hs : (∑ i, (L i).q.e) = 0 := Fin.sum_univ_zero _
  by_cases hx : x = 0
  · subst hx
    have h1 : IsHalf (∑ i, (L i).q.e) (0 : WO S T) := by rw [hs]; exact (isHalf_zero_iff _).2 rfl
    rw [if_pos h1, if_pos ⟨Λ.zero_mem, (isHalf_zero_iff _).2 rfl⟩, Fin.prod_univ_zero]
  · have h1 : ¬ IsHalf (∑ i, (L i).q.e) x := by rw [hs]; exact fun h => hx ((isHalf_zero_iff _).1 h)
    rw [if_neg h1, if_neg (fun h => hx ((isHalf_zero_iff _).1 h.2))]

theorem prodDat_succ {n : ℕ} (L : Fin (n+1) → LocPl ψ S T M M') (hinj : Function.Injective fun i => (L i).q.v) :
    prodDat L = (ofSplit (L 0).q).tensorAt (L 0).FS (L 0).FT (prodDat fun i : Fin n => L i.succ) (L 0).Φ.1 := by
  funext t
  have hup := TOneModel.up_down_eq (ofSplit (L 0).q) (L 0).FS (L 0).FT t
  have hpe : (ofSplit (L 0).q).e = (L 0).q.e := rfl
  simp only [prodDat, Place.tensorAt]
  rw [hup, hpe]
  have hd : ∀ i : Fin n, (ofSplit (L i.succ).q).down (L i.succ).FS (L i.succ).FT
      (t - t.map (fun a => (L 0).q.e * a)) = (ofSplit (L i.succ).q).down (L i.succ).FS (L i.succ).FT t :=
    fun i => down_sub_mul _ _ _ (orth_succ L hinj i) t
  simp only [hd]
  rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
  have hiff := isHalf_add_iff (a := (L 0).q.e) (b := ∑ i : Fin n, (L i.succ).q.e) (orth_sum L hinj) t
  by_cases h : IsHalf ((L 0).q.e + ∑ i : Fin n, (L i.succ).q.e) t
  · rw [if_pos h, if_pos (hiff.1 h)]
    ring
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h')), zero_mul]

theorem halfInd_zero_isSBHalf (Λ : AddSubgroup (WO S T)) : IsSBHalf (0 : AE D) Λ (halfInd 0 Λ) := by
  refine ⟨fun t h => ?_, 1, one_pos, fun u _ hh t => ?_, fun t h => ?_⟩
  · by_contra hc
    exact h (by simp [halfInd, hc])
  · rw [(isHalf_zero_iff u).1 hh]
    simp
  · rw [one_smul]
    by_contra hc
    exact h (by simp [halfInd, hc])

theorem prodDat_isSBHalf (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M') (n : ℕ) :
    ∀ (L : Fin n → LocPl ψ S T M M'), Function.Injective (fun i => (L i).q.v) →
      IsSBHalf (∑ i, (L i).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) (prodDat L) := by
  induction n with
  | zero =>
    intro L _
    rw [prodDat_zero L (latO S T (M : Set _) (M' : Set _) fun _ => True)]
    simpa using halfInd_zero_isSBHalf (D := D) (latO S T (M : Set _) (M' : Set _) fun _ => True)
  | succ n ih =>
    intro L hinj
    rw [prodDat_succ L hinj, Fin.sum_univ_succ, add_comm]
    exact GlobalTheory.T.schwartzBruhatHalf_tensor_split_place_selfDual D ψ S T M M' hM hM' (L 0) _ (orth_sum L hinj) _
      (ih (fun i => L i.succ) (hinj.comp (Fin.succ_injective n))) _ (L 0).Φ.2

end Fam

end GlobalTheory.VecProd

namespace GlobalTheory.VecProd

section Core
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : Lat S} {M' : Lat T}

theorem step (hψ : IsStdChar D ψ (-1)) (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M') {n : ℕ}
    (L : Fin (n+1) → LocPl ψ S T M M') (hinj : Function.Injective fun i => (L i).q.v) (f₀ : WO S T → ℂ)
    (hf₀ : Vac ψ S T M M' (fun _ => True) f₀) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ))
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (∑ i, (L i).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T') :
    ∃ Tm : SB (Matrix (L 0).Y (L 0).Y' (L 0).k) →ₗ[ℂ] (WO S T → ℂ),
      (ofSplit (L 0).q).IsModel ψ (L 0).FS (L 0).FT Tm ∧ Tm (L 0).Φ = T' (prodDat L) ∧
      ∃ T'' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
        IsPlaceModel ψ (symplO S T) (heisO ψ S T) (∑ i : Fin n, (L i.succ).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T'' ∧
        ∀ Φ₀ : SB (Matrix (L 0).Y (L 0).Y' (L 0).k),
          (Φ₀ : Matrix (L 0).Y (L 0).Y' (L 0).k → ℂ) = Set.indicator {x | (ofSplit (L 0).q).up (L 0).FS (L 0).FT x ∈
            latO S T (M : Set _) (M' : Set _) (· = (L 0).q.v)} (fun _ => 1) →
          Tm Φ₀ = T'' (prodDat fun i : Fin n => L i.succ) := by
  have horth := orth_sum L hinj
  have hsum : ∑ i, (L i).q.e = (∑ i : Fin n, (L i.succ).q.e) + (L 0).q.e := by
    rw [Fin.sum_univ_succ, add_comm]
  have hT2 := hT
  rw [hsum] at hT2
  have hθ : ∀ Φ', IsSBHalf ((∑ i : Fin n, (L i.succ).q.e) + (L 0).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ' →
      IsThetaFunO ψ S T (T' Φ') := by
    intro Φ' h
    rw [← hsum] at h
    exact GlobalTheory.T.isThetaFunO_splitPlaces_schrodingerModel_sum D ψ hψ S T M M' hM hM' (n+1) L hinj f₀ T' hf₀ hT Φ' h
  have hsbL := prodDat_isSBHalf hM hM' n (fun i => L i.succ) (hinj.comp (Fin.succ_injective n))
  have hsb : ∀ Ψ ∈ SB (Matrix (L 0).Y (L 0).Y' (L 0).k), IsSBHalf ((∑ i : Fin n, (L i.succ).q.e) + (L 0).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True)
      ((ofSplit (L 0).q).tensorAt (L 0).FS (L 0).FT (prodDat fun i : Fin n => L i.succ) Ψ) :=
    fun Ψ hΨ => GlobalTheory.T.schwartzBruhatHalf_tensor_split_place_selfDual D ψ S T M M' hM hM' (L 0) _ horth _ hsbL Ψ hΨ
  have hmodel := tensorL_isModel (ofSplit (L 0).q) ψ (L 0).FS (L 0).FT _ horth _
    (prodDat fun i : Fin n => L i.succ) hsbL.1 f₀ T' hT2 hθ hsb
  obtain ⟨T'', hT'', hT''eq⟩ := GlobalTheory.T.isPlaceModel_tensor_splitPlaceLatticeIndicator D ψ S T M M' hM hM' (L 0) _ horth f₀ T' hT2
  refine ⟨T' ∘ₗ (ofSplit (L 0).q).tensorL (L 0).FS (L 0).FT (prodDat fun i : Fin n => L i.succ), hmodel, ?_,
    T'', hT'', ?_⟩
  · rw [LinearMap.comp_apply, Place.tensorL_apply, prodDat_succ L hinj]
  · intro Φ₀ hΦ₀
    rw [LinearMap.comp_apply, Place.tensorL_apply, hΦ₀, hT''eq]

theorem isOne_intInd (P : LocPl ψ S T M M') :
    IsOne (⟨Place.intInd P.Y P.Y', Place.intInd_mem_SB _ _ _⟩ : SB (Matrix P.Y P.Y' P.k)) := rfl

theorem core (hψ : IsStdChar D ψ (-1)) (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M') (f₀ : WO S T → ℂ)
    (hf₀ : Vac ψ S T M M' (fun _ => True) f₀) (n : ℕ) :
    ∀ (L : Fin n → LocPl ψ S T M M'), Function.Injective (fun i => (L i).q.v) →
      ∀ T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
        IsPlaceModel ψ (symplO S T) (heisO ψ S T) (∑ i, (L i).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T' →
        T' (prodDat L) = (List.finRange n).foldr (fun i g => comb ψ S T (L i).e (comb ψ S T (L i).o g)) f₀ := by
  induction n with
  | zero =>
    intro L _ T' hT
    rw [prodDat_zero L (latO S T (M : Set _) (M' : Set _) fun _ => True)]
    have h := hT.vac
    rw [Fin.sum_univ_zero, one_smul] at h
    rw [h]
    rfl
  | succ n ih =>
    intro L hinj T' hT
    obtain ⟨Tm, hTm, hTmΦ, T'', hT'', hT''eq⟩ := step hψ hM hM' L hinj f₀ hf₀ T' hT
    have h1 := (L 0).e_is.2 Tm hTm _ (L 0).Φ (isOne_intInd (L 0)) rfl
    have h2 := (L 0).o_is Tm hTm ⟨_, GlobalTheory.T.indicator_localHomLattice_mem_schwartzBruhat D ψ S T M M' hM hM' (L 0)⟩ _ (isOne_intInd (L 0)) rfl
    have h3 := hT''eq ⟨_, GlobalTheory.T.indicator_localHomLattice_mem_schwartzBruhat D ψ S T M M' hM hM' (L 0)⟩ rfl
    rw [← hTmΦ, h1, h2, h3, ih _ (hinj.comp (Fin.succ_injective n)) T'' hT'', List.finRange_succ,
      List.foldr_cons, List.foldr_map]

end Core

end GlobalTheory.VecProd

namespace GlobalTheory.VecProd

section Fin2
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : Lat S} {M' : Lat T}

theorem comb_single_zero (f : WO S T → ℂ) : comb ψ S T (Finsupp.single 0 1) f = f := by
  have h0 : ∀ w : WO S T, symplOH S T w 0 = 0 := fun w => by simp [symplOH, symplO, hO]
  unfold comb
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]
  funext w
  simp only [heisO, add_zero, h0, AddChar.map_zero_eq_one, one_mul]

noncomputable def oneLoc (P : LocPl ψ S T M M') : LocPl ψ S T M M' where
  k := P.k
  q := P.q
  unit := P.unit
  Y := P.Y
  Y' := P.Y'
  FS := P.FS
  FT := P.FT
  Φ := ⟨Place.intInd P.Y P.Y', Place.intInd_mem_SB _ _ _⟩
  e := Finsupp.single 0 1
  e_is := by
    refine ⟨fun u hu => ?_, fun Tm _ Φ₀ Φ h0 hΦ => ?_⟩
    · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
      subst hu
      intro i j
      simp
    · rw [comb_single_zero]
      congr 1
      exact Subtype.ext (hΦ.trans h0.symm)
  o := P.o
  o_at := P.o_at
  o_is := P.o_is

theorem oneLoc_e (P : LocPl ψ S T M M') : (oneLoc P).e = Finsupp.single 0 1 := rfl
theorem oneLoc_o (P : LocPl ψ S T M M') : (oneLoc P).o = P.o := rfl

theorem prodDat_perm {n : ℕ} (L : Fin n → LocPl ψ S T M M') (σ : Equiv.Perm (Fin n)) :
    prodDat (fun i => L (σ i)) = prodDat L := by
  funext x
  unfold prodDat
  rw [Equiv.sum_comp σ (fun i => (L i).q.e),
    Equiv.prod_comp σ (fun i => (L i).Φ.1 ((ofSplit (L i).q).down (L i).FS (L i).FT x))]

theorem vac_at_of_model (hψ : IsStdChar D ψ (-1)) (P : LocPl ψ S T M M') (N : Lat S) (N' : Lat T)
    (hN : IsSelfDualC S N) (hN' : IsSelfDualC T N') (hI : IntIn P.q S P.FS N ∧ IntIn P.q T P.FT N')
    (g : WO S T → ℂ) (Tm : SB (Matrix P.Y P.Y' P.k) →ₗ[ℂ] (WO S T → ℂ))
    (hTm : (ofSplit P.q).IsModel ψ P.FS P.FT Tm)
    (hg : Tm ⟨Place.intInd P.Y P.Y', Place.intInd_mem_SB _ _ _⟩ = g) : Vac ψ S T N N' (· = P.q.v) g := by
  obtain ⟨ψk, hch, hcond⟩ := GlobalTheory.T.exists_splitPoint_weilChar_conductor_one_of_units D P.k P.q ψ hψ P.unit
  have h := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D P.k P.q P.unit P.Y P.Y' S T P.FS P.FT ψ ψk hψ hch hcond N N' hN hN' hI.1 hI.2).1
    Tm _ hTm (isOne_intInd P)
  rwa [hg] at h

end Fin2

theorem thetaAt_prodDat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ f₀ f, Vac ψ S T M M' (fun _ => True) f₀ → IsThetaAt ψ (symplO S T) (heisO ψ S T) (∑ i, (L i).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ (prodDat L) f → IsThetaFunO ψ S T f → f = (List.finRange n).foldr (fun i g => comb ψ S T (L i).e (comb ψ S T (L i).o g)) f₀ ∧ ∀ (N : Lat S) (N' : Lat T), IsSelfDualC S N → IsSelfDualC T N' → (∀ i, IntIn (L i).q S (L i).FS N ∧ IntIn (L i).q T (L i).FT N') → (∀ p, (∀ i, p ≠ (L i).q.v) → latV S N (· = p) = latV S M (· = p) ∧ latV T N' (· = p) = latV T M' (· = p)) → Vac ψ S T N N' (fun _ => True) ((List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) f₀) := by
  intro D ψ hψ S T M M' hM hM' n L hinj f₀ f hf₀ hθ _
  obtain ⟨⟨T', hT'⟩, hall⟩ := hθ
  have hcore := core hψ hM hM' f₀ hf₀
  refine ⟨(hall T' hT').trans (hcore n L hinj T' hT'), fun N N' hN hN' hI hV => ?_⟩

  have hg1 : T' (prodDat fun i => oneLoc (L i)) =
      (List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) f₀ := by
    rw [hcore n (fun i => oneLoc (L i)) hinj T' hT']
    simp only [oneLoc_e, oneLoc_o, comb_single_zero]

  have hloc : ∀ j : Fin n, Vac ψ S T N N' (· = (L j).q.v)
      ((List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) f₀) := by
    intro j
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := j.pos; omega⟩
    let L1 : Fin (m+1) → LocPl ψ S T M M' := fun i => oneLoc (L i)
    let σ : Equiv.Perm (Fin (m+1)) := Equiv.swap 0 j
    have hinjσ : Function.Injective fun i => (L1 (σ i)).q.v := hinj.comp σ.injective
    have hTσ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (∑ i, (L1 (σ i)).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T' := by
      rw [Equiv.sum_comp σ (fun i => (L1 i).q.e)]
      exact hT'
    obtain ⟨Tm, hTm, hTmΦ, -⟩ := step hψ hM hM' (fun i => L1 (σ i)) hinjσ f₀ hf₀ T' hTσ
    have hval : Tm (L1 (σ 0)).Φ = (List.finRange (m+1)).foldr (fun i g => comb ψ S T (L i).o g) f₀ := by
      rw [hTmΦ, prodDat_perm L1 σ]
      exact hg1
    have hv := vac_at_of_model hψ (L1 (σ 0)) N N' hN hN' (hI (σ 0)) _ Tm hTm hval
    have h0 : σ 0 = j := Equiv.swap_apply_left _ _
    have hq : (L1 (σ 0)).q.v = (L j).q.v := by rw [h0]; rfl
    rw [hq] at hv
    exact hv

  have hQc : Vac ψ S T N N' (fun p => ∀ i, p ≠ (L i).q.v)
      ((List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) f₀) := by
    have hbase : Vac ψ S T M M' (fun p => ∀ i, p ≠ (L i).q.v) f₀ := by
      have hiff := (GlobalTheory.DisjComb.main D ψ hψ S T (fun p => ∀ i, p ≠ (L i).q.v) (fun p => ∃ i, p = (L i).q.v)
        (fun p hp ⟨i, hi⟩ => hp i hi)).2.2.2.2 M M' f₀ hM hM'
      have hfun : (fun p => (∀ i, p ≠ (L i).q.v) ∨ ∃ i, p = (L i).q.v) = fun _ => True := by
        funext p
        apply propext
        constructor
        · intro _
          trivial
        · intro _
          by_cases h : ∃ i, p = (L i).q.v
          · exact Or.inr h
          · exact Or.inl fun i hi => h ⟨i, hi⟩
      rw [hfun] at hiff
      exact (hiff.1 hf₀).1
    have hbaseN : Vac ψ S T N N' (fun p => ∀ i, p ≠ (L i).q.v) f₀ := by
      refine ⟨hbase.1, ?_⟩
      rw [GlobalTheory.T.homLatticeAtPlaces_congr_localLattices D S T N M N' M' hN hM hN' hM' _ hV]
      exact hbase.2
    have hl : ∀ l : List (Fin n), Vac ψ S T N N' (fun p => ∀ i, p ≠ (L i).q.v)
        (l.foldr (fun i g => comb ψ S T (L i).o g) f₀) := by
      intro l
      induction l with
      | nil => exact hbaseN
      | cons i l ih =>
        rw [List.foldr_cons]
        have hdisj : ∀ p, p = (L i).q.v → ¬ ∀ i', p ≠ (L i').q.v := fun p hp h => h i hp
        have hc : CombAt (· = (L i).q.v) (L i).o := fun u hu => GlobalTheory.T.matrixSupported_splitPlace_of_isHalf_conjSum D _ (L i).q u ((L i).o_at u hu)
        exact ((GlobalTheory.DisjComb.main D ψ hψ S T (· = (L i).q.v) _ hdisj).2.1 _ hc).2 N N' _ ih
    exact hl _

  have hstep : ∀ j : ℕ, j ≤ n → Vac ψ S T N N' (fun p => (∀ i, p ≠ (L i).q.v) ∨ ∃ i : Fin n, i.val < j ∧ p = (L i).q.v)
      ((List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) f₀) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hfun : (fun p => (∀ i, p ≠ (L i).q.v) ∨ ∃ i : Fin n, i.val < 0 ∧ p = (L i).q.v) =
          fun p => ∀ i, p ≠ (L i).q.v := by
        funext p
        simp
      rw [hfun]
      exact hQc
    | succ j ih =>
      intro hj
      have hj' : j < n := hj
      let jj : Fin n := ⟨j, hj'⟩
      have hdisj : ∀ p, ((∀ i, p ≠ (L i).q.v) ∨ ∃ i : Fin n, i.val < j ∧ p = (L i).q.v) → ¬ (p = (L jj).q.v) := by
        rintro p (h | ⟨i, hi, rfl⟩) hp
        · exact h jj hp
        · have h2 : i = jj := hinj hp
          rw [h2] at hi
          exact lt_irrefl _ hi
      have hiff := (GlobalTheory.DisjComb.main D ψ hψ S T _ _ hdisj).2.2.2.2 N N'
        ((List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) f₀) hN hN'
      have hfun : (fun p => ((∀ i, p ≠ (L i).q.v) ∨ ∃ i : Fin n, i.val < j ∧ p = (L i).q.v) ∨ p = (L jj).q.v) =
          fun p => (∀ i, p ≠ (L i).q.v) ∨ ∃ i : Fin n, i.val < j + 1 ∧ p = (L i).q.v := by
        funext p
        apply propext
        constructor
        · rintro ((h | ⟨i, hi, h⟩) | h)
          · exact Or.inl h
          · exact Or.inr ⟨i, by omega, h⟩
          · exact Or.inr ⟨jj, by simp [jj], h⟩
        · rintro (h | ⟨i, hi, h⟩)
          · exact Or.inl (Or.inl h)
          · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
            · exact Or.inl (Or.inr ⟨i, hi, h⟩)
            · exact Or.inr (by rw [h, show i = jj from Fin.ext hi])
      rw [hfun] at hiff
      exact hiff.2 ⟨ih (by omega), hloc jj⟩
  have hfin := hstep n le_rfl
  have hfun : (fun p => (∀ i, p ≠ (L i).q.v) ∨ ∃ i : Fin n, i.val < n ∧ p = (L i).q.v) = fun _ => True := by
    funext p
    apply propext
    constructor
    · intro _
      trivial
    · intro _
      by_cases h : ∃ i, p = (L i).q.v
      · obtain ⟨i, hi⟩ := h
        exact Or.inr ⟨i, i.isLt, hi⟩
      · exact Or.inl fun i hi => h ⟨i, hi⟩
  rw [hfun] at hfin
  exact hfin

end GlobalTheory.VecProd

end
end
