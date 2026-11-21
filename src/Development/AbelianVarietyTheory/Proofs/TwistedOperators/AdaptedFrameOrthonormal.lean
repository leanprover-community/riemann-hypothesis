import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqConjOfInFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuumMaximalCompactCharacterRealPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsColIntertwiner
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedVectorDefinitePairThetaFockVacuum

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowReal

section FockAll

open Classical

variable {D : D7}

def fockSubOn {m n : ℕ} (s : Finset D.what₂.Tau) (pS pT : D.what₂.Tau → ℕ) (κS : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (κT : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) : MvPolynomial (FVar D m n) ℂ →ₐ[ℂ] MvPolynomial (FVar D m n) ℂ :=
  MvPolynomial.aeval fun y : FVar D m n =>
    if y.1 ∈ s then
      ∑ i, ∑ j, MvPolynomial.C (if (y.2.1.val < pT y.1 ↔ y.2.2.val < pS y.1) then κT y.1 i y.2.1 * (κS y.1)⁻¹ y.2.2 j
        else (starRingEnd ℂ) (κT y.1 i y.2.1 * (κS y.1)⁻¹ y.2.2 j)) * MvPolynomial.X (y.1, i, j)
    else MvPolynomial.X y

variable {m n : ℕ} (pS pT : D.what₂.Tau → ℕ) (κS : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (κT : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)

theorem fockSubOn_empty (Q : MvPolynomial (FVar D m n) ℂ) : fockSubOn ∅ pS pT κS κT Q = Q := by
  have e : fockSubOn (∅ : Finset D.what₂.Tau) pS pT κS κT = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro y
    simp only [fockSubOn, MvPolynomial.aeval_X, Finset.notMem_empty, if_false, AlgHom.id_apply]
  rw [e, AlgHom.id_apply]

theorem fockSubOn_univ : fockSubOn Finset.univ pS pT κS κT = fockSubAll pS pT κS κT := by
  apply MvPolynomial.algHom_ext
  intro y
  simp only [fockSubOn, fockSubAll, MvPolynomial.aeval_X, Finset.mem_univ, if_true]

theorem fockSub_fockSubOn {τ : D.what₂.Tau} {s : Finset D.what₂.Tau} (hτ : τ ∉ s) (Q : MvPolynomial (FVar D m n) ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockSub τ (pS τ) (pT τ) (κS τ) (κT τ) (fockSubOn s pS pT κS κT Q) =
      fockSubOn (insert τ s) pS pT κS κT Q := by
  suffices e : (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockSub τ (pS τ) (pT τ) (κS τ) (κT τ)).comp (fockSubOn s pS pT κS κT) =
      fockSubOn (insert τ s) pS pT κS κT from DFunLike.congr_fun e Q
  apply MvPolynomial.algHom_ext
  intro y
  rw [AlgHom.comp_apply]
  by_cases hy : y.1 ∈ s
  · have hne : y.1 ≠ τ := fun h => hτ (h ▸ hy)
    simp only [fockSubOn, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockSub, MvPolynomial.aeval_X, Finset.mem_insert, hy, if_true, or_true,
      map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, hne, if_false]
  · by_cases h2 : y.1 = τ
    · obtain ⟨ρ, a, b⟩ := y
      simp only at h2 hy
      subst h2
      simp only [fockSubOn, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockSub, MvPolynomial.aeval_X, Finset.mem_insert, hy, if_false, true_or,
        if_true]
    · simp only [fockSubOn, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockSub, MvPolynomial.aeval_X, Finset.mem_insert, hy, h2, if_false,
        or_false]

theorem om_pureTensorO_compact_all (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (χS χT : (AE D)ˣ →* Circle) (om : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.OmT S T) (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (pS pT : D.what₂.Tau → ℕ) (hpS : ∀ ρ, pS ρ ≤ S.rank) (hpT : ∀ ρ, pT ρ ≤ T.rank)
    (hS : ∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) (hT : ∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ))
    (hBS : ∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) (hBT : ∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ))
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) (hvac : ∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f)
    (κS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (κT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hκS : ∀ ρ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat (pS ρ) (κS ρ)) (hκT : ∀ ρ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat (pT ρ) (κT ρ))
    (x : GA D S) (y : GA D T) (hx : x ∈ GinfC S) (hy : y ∈ GinfC T)
    (hxc : ∀ ρ, compAt θ ρ (mt S x) = BS ρ * κS ρ * (BS ρ)⁻¹)
    (hyc : ∀ ρ, compAt θ ρ (mt T y) = BT ρ * κT ρ * (BT ρ)⁻¹)
    (c : ℂ) (hc : om (x, y) f = c • f) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    om (x, y) (pureTensorO ψ θ S T sS sT BS BT f Q) =
      c • pureTensorO ψ θ S T sS sT BS BT f (fockSubAll pS pT κS κT Q) := by
  have hUS : ∀ ρ, compAt θ ρ (mt S x) ∈ Formalism.QuantumDeterminants.UH (gramAt D S ρ) := fun ρ =>
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S x ρ
  have hUT : ∀ ρ, compAt θ ρ (mt T y) ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ) := fun ρ =>
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ T y ρ
  have hAS : ∀ τ, IsAtTau θ S τ (BS τ * κS τ * (BS τ)⁻¹) (atTau θ S τ (compAt θ τ (mt S x))) := fun τ => by
    rw [← hxc τ]; exact GlobalTheory.PointAtPlaceHom.atTau_spec hθ S τ (hUS τ)
  have hAT : ∀ τ, IsAtTau θ T τ (BT τ * κT τ * (BT τ)⁻¹) (atTau θ T τ (compAt θ τ (mt T y))) := fun τ => by
    rw [← hyc τ]; exact GlobalTheory.PointAtPlaceHom.atTau_spec hθ T τ (hUT τ)
  have hev : ∀ τ, ∃ e : ℂ, om (atTau θ S τ (compAt θ τ (mt S x)), atTau θ T τ (compAt θ τ (mt T y))) f = e • f :=
    fun τ => by
      obtain ⟨mS, mT, h⟩ := GlobalTheory.VacCharAtPlace.vacuum_char_at_place D ψ θ S T χS χT om hom hθ τ
      exact ⟨_, h sS BS sT BT pS pT hpS hpT hS hT hBS hBT f hf hvac (κS τ) (κT τ) (hκS τ) (hκT τ) _ _ (hAS τ) (hAT τ)⟩
  choose e he using hev
  let MSs : Finset D.what₂.Tau → D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ :=
    fun s ρ => if ρ ∈ s then compAt θ ρ (mt S x) else 1
  let MTs : Finset D.what₂.Tau → D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ :=
    fun s ρ => if ρ ∈ s then compAt θ ρ (mt T y) else 1
  have hUSs : ∀ s ρ, MSs s ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D S ρ) := fun s ρ => by
    by_cases h : ρ ∈ s
    · simp only [MSs, if_pos h]; exact hUS ρ
    · simp only [MSs, if_neg h]; exact GlobalTheory.PointAtPlaceHom.one_mem_UH _
  have hUTs : ∀ s ρ, MTs s ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ) := fun s ρ => by
    by_cases h : ρ ∈ s
    · simp only [MTs, if_pos h]; exact hUT ρ
    · simp only [MTs, if_neg h]; exact GlobalTheory.PointAtPlaceHom.one_mem_UH _
  have key : ∀ s : Finset D.what₂.Tau, ∀ Q, om (realAll θ S (MSs s), realAll θ T (MTs s)) (pureTensorO ψ θ S T sS sT BS BT f Q) =
      (∏ τ ∈ s, e τ) • pureTensorO ψ θ S T sS sT BS BT f (fockSubOn s pS pT κS κT Q) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro Q
      have h1 : MSs ∅ = 1 := by funext ρ; simp [MSs]
      have h2 : MTs ∅ = 1 := by funext ρ; simp [MTs]
      rw [h1, h2, realAll_one hθ, realAll_one hθ, Prod.mk_one_one, map_one, Module.End.one_apply, Finset.prod_empty,
        one_smul, fockSubOn_empty]
    · intro τ s hτ ih Q
      have eS : realAll θ S (MSs (insert τ s)) = atTau θ S τ (compAt θ τ (mt S x)) * realAll θ S (MSs s) := by
        rw [realAll_eq_atTau_mul hθ (hUSs (insert τ s)) τ]
        congr 2
        · simp [MSs]
        · funext ρ
          by_cases h : ρ = τ
          · subst h; simp [MSs, hτ]
          · simp [MSs, Function.update_of_ne h, h]
      have eT : realAll θ T (MTs (insert τ s)) = atTau θ T τ (compAt θ τ (mt T y)) * realAll θ T (MTs s) := by
        rw [realAll_eq_atTau_mul hθ (hUTs (insert τ s)) τ]
        congr 2
        · simp [MTs]
        · funext ρ
          by_cases h : ρ = τ
          · subst h; simp [MTs, hτ]
          · simp [MTs, Function.update_of_ne h, h]
      rw [eS, eT, ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, ih Q, map_smul,
        GlobalTheory.FockCompact.om_pureTensorO_compact D ψ θ S T χS χT om hom hθ sS BS sT BT pS pT hpS hpT hS hT hBS hBT f hf τ
          (κS τ) (κT τ) (hκS τ) (hκT τ) _ _ (hAS τ) (hAT τ) (e τ) (he τ),
        smul_smul, fockSub_fockSubOn pS pT κS κT hτ, Finset.prod_insert hτ, mul_comm (e τ)]
  have hxr : realAll θ S (MSs Finset.univ) = x :=
    realAll_eq hθ (hUSs _) ⟨hx, fun ρ => by simp only [MSs, Finset.mem_univ, if_true]; rfl⟩
  have hyr : realAll θ T (MTs Finset.univ) = y :=
    realAll_eq hθ (hUTs _) ⟨hy, fun ρ => by simp only [MTs, Finset.mem_univ, if_true]; rfl⟩
  have hall := key Finset.univ
  rw [hxr, hyr, fockSubOn_univ] at hall
  have hE : om (x, y) f = (∏ τ, e τ) • f := by
    have h1 := hall 1
    rw [map_one (fockSubAll pS pT κS κT)] at h1
    simpa only [GlobalTheory.FiniteFock.pureTensorO_one] using h1
  rw [hall Q]
  by_cases hf0 : f = 0
  · subst hf0
    have z : ∀ P, pureTensorO ψ θ S T sS sT BS BT 0 P = 0 := fun P => by
      have := GlobalTheory.FiniteFock.pureTensorO_smul ψ θ S T sS sT BS BT 0 0 P
      rwa [zero_smul, zero_smul] at this
    simp only [z, smul_zero]
  · have hce : c = ∏ τ, e τ := smul_left_injective ℂ hf0 (hc.symm.trans hE)
    rw [hce]

end FockAll

theorem om_fock_compact_all : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (p : Pair T), p.InRange D.R.m →
    ∀ (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ (G.pS p).rank) → (∀ ρ, pT ρ ≤ (G.pT p).rank) →
    (∀ ρ, IsCartanInv (gramAt D (G.pS p) ρ) (G.cartS W.cart p ρ)) →
    (∀ ρ, IsCartanInv (gramAt D (G.pT p) ρ) (G.onT W.cart p ρ)) →
    (∀ ρ, IsONBasis (gramAt D (G.pS p) ρ) (G.cartS W.cart p ρ) (G.onS W.onb p ρ) (pS ρ)) →
    (∀ ρ, IsONBasis (gramAt D (G.pT p) ρ) (G.onT W.cart p ρ) (G.onT W.onb p ρ) (pT ρ)) →
    ∀ f : WO (G.pS p) (G.pT p) → ℂ, IsThetaFunO W.ψ _ _ f →
    (∀ ρ, IsFockVacAt (heisO W.ψ _ _) W.θ ρ (cplxO (G.cartS W.cart p ρ) (G.onT W.cart p ρ)) f) →
    ∀ (κS : D.what₂.Tau → Matrix (Fin (G.pS p).rank) (Fin (G.pS p).rank) ℂ)
      (κT : D.what₂.Tau → Matrix (Fin (G.pT p).rank) (Fin (G.pT p).rank) ℂ),
    (∀ ρ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat (pS ρ) (κS ρ)) → (∀ ρ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat (pT ρ) (κT ρ)) →
    ∀ (x : GA D (G.pS p)) (y : GA D (G.pT p)), x ∈ GinfC (G.pS p) → y ∈ GinfC (G.pT p) →
    (∀ ρ, compAt W.θ ρ (mt _ x) = G.onS W.onb p ρ * κS ρ * (G.onS W.onb p ρ)⁻¹) →
    (∀ ρ, compAt W.θ ρ (mt _ y) = G.onT W.onb p ρ * κT ρ * (G.onT W.onb p ρ)⁻¹) →
    ∀ c : ℂ, W.om p (x, y) f = c • f → ∀ Q : PolF D (G.pT p).rank (G.pS p).rank,
    W.om p (x, y) (W.fock p f Q) = c • W.fock p f (GlobalTheory.RowReal.fockSubAll pS pT κS κT Q) := by
  intro D T L sc G W p hp pS pT hpS hpT hS hT hBS hBT f hf hvac κS κT hκS hκT x y hx hy hxc hyc c hc Q
  exact om_pureTensorO_compact_all D W.ψ W.θ (G.pS p) (G.pT p) (G.chrS p) (G.chrT p) (W.om p) (W.om_is p hp) W.θ_is
    (G.cartS W.cart p) (G.onS W.onb p) (G.onT W.cart p) (G.onT W.onb p) pS pT hpS hpT hS hT hBS hBT f hf hvac κS κT hκS hκT
    x y hx hy hxc hyc c hc Q

end GlobalTheory.RowReal
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_compactRealPoint_fockVector_substitution : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (p : Pair T), p.InRange D.R.m →
    ∀ (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ (G.pS p).rank) → (∀ ρ, pT ρ ≤ (G.pT p).rank) →
    (∀ ρ, IsCartanInv (gramAt D (G.pS p) ρ) (G.cartS W.cart p ρ)) →
    (∀ ρ, IsCartanInv (gramAt D (G.pT p) ρ) (G.onT W.cart p ρ)) →
    (∀ ρ, IsONBasis (gramAt D (G.pS p) ρ) (G.cartS W.cart p ρ) (G.onS W.onb p ρ) (pS ρ)) →
    (∀ ρ, IsONBasis (gramAt D (G.pT p) ρ) (G.onT W.cart p ρ) (G.onT W.onb p ρ) (pT ρ)) →
    ∀ f : WO (G.pS p) (G.pT p) → ℂ, IsThetaFunO W.ψ _ _ f →
    (∀ ρ, IsFockVacAt (heisO W.ψ _ _) W.θ ρ (cplxO (G.cartS W.cart p ρ) (G.onT W.cart p ρ)) f) →
    ∀ (κS : D.what₂.Tau → Matrix (Fin (G.pS p).rank) (Fin (G.pS p).rank) ℂ)
      (κT : D.what₂.Tau → Matrix (Fin (G.pT p).rank) (Fin (G.pT p).rank) ℂ),
    (∀ ρ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat (pS ρ) (κS ρ)) → (∀ ρ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat (pT ρ) (κT ρ)) →
    ∀ (x : GA D (G.pS p)) (y : GA D (G.pT p)), x ∈ GinfC (G.pS p) → y ∈ GinfC (G.pT p) →
    (∀ ρ, compAt W.θ ρ (mt _ x) = G.onS W.onb p ρ * κS ρ * (G.onS W.onb p ρ)⁻¹) →
    (∀ ρ, compAt W.θ ρ (mt _ y) = G.onT W.onb p ρ * κT ρ * (G.onT W.onb p ρ)⁻¹) →
    ∀ c : ℂ, W.om p (x, y) f = c • f → ∀ Q : PolF D (G.pT p).rank (G.pS p).rank,
    W.om p (x, y) (W.fock p f Q) = c • W.fock p f (GlobalTheory.RowReal.fockSubAll pS pT κS κT Q) := by
  atlas_forward_decl GlobalTheory.RowReal.om_fock_compact_all
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section EigTop

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem cart_eq_one_of_posOnb (W : G.Weil) {X : Node} (hX : X.InRange D.R.m) (hP : PosOnb W X) (τ : D.what₂.Tau) :
    W.cart X τ = 1 := by
  obtain ⟨ε, h1, h2⟩ := W.onb_is X hX τ
  rw [hP τ] at h1
  rw [← h1, Matrix.mul_one] at h2
  have hd : IsUnit (W.onb X τ).det := Matrix.isUnit_det_of_left_inverse (hP τ)
  calc W.cart X τ = W.cart X τ * W.onb X τ * (W.onb X τ)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    _ = 1 := by rw [h2, Matrix.mul_nonsing_inv _ hd]

theorem compAt_mt_eq_archM (θ : InfFam D) (V : HSp D) (k : GA D V) (τ : D.what₂.Tau) :
    compAt θ τ (mt V k) = Formalism.L2.Pj.archM V (θ τ) k := by
  have e := GlobalTheory.RealType.realFr_coe θ V 1 k τ
  rw [GlobalTheory.RealType.realFr_one] at e
  rw [show compAt θ τ (mt V k) = ((GlobalTheory.CoefModel.realGL θ V k τ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) from rfl, e]
  simp

theorem det_conj_submatrix {a b : ℕ} (h : a = b) {B : Matrix (Fin b) (Fin b) ℂ} (hB : IsUnit B.det)
    (u : Matrix (Fin a) (Fin a) ℂ) :
    (B * u.submatrix (Fin.cast h.symm) (Fin.cast h.symm) * B⁻¹).det = u.det := by
  subst h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', mul_comm, ← mul_assoc,
    inv_mul_cancel₀ hB.ne_zero, one_mul]
  rfl

end EigTop

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section EigTop2

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem det_compAt_ptTop (W : G.Weil) (μ0 : T) (hL : L.Is μ0) {U : Set T} (N : Std G U)
    (g : Gc D.what₂.Tau (rowSizes D)) (n : Fin (D.R.m + 1)) (τ : D.what₂.Tau) :
    (compAt W.θ τ (mt (G.V (.top n)) (ptTop W g n))).det =
      (rowComp (rowSizes D) g n τ).1.det := by
  induction n using Fin.lastCases with
  | last =>
    show (compAt W.θ τ (mt (G.V (.top D.R.m)) (ptTop W g D.R.m))).det = _
    have hP : PosOnb W (.grid D.R.m D.R.m) :=
      posOnb_of_defNode W μ0 hL (X := .grid D.R.m D.R.m) ⟨le_rfl, rfl⟩
    have hd := fun τ => Matrix.isUnit_det_of_left_inverse (hP τ)
    rw [ptTop_m, kappaTop_apply, compAt_mt_eq_archM]
    have e1 : ∀ (X : Node) (k : GA D (G.V X)), (Formalism.L2.Pj.archM (G.V X) (W.θ τ) k).det =
        ((GlobalTheory.RealType.realAt W.θ N X k τ : GL (Fin (G.V X).rank) ℂ) : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ).det :=
      fun X k => by rw [GlobalTheory.RealType.realAt, GlobalTheory.RealType.realFr_coe, Matrix.det_units_conj']
    rw [e1, (GlobalTheory.RealType.isBlock_realAt W.θ_is N _ τ).det, mul_one, ← e1, ← compAt_mt_eq_archM]
    have e2 := compAt_kappa_snd g (Fin.last _) hP τ
    erw [e2, det_conj_submatrix (rank_gridM G le_rfl).symm (hd τ)]
    have e : rowComp (rowSizes D) g (Fin.last D.R.m) = embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) := by
      simp only [rowComp, MonoidHom.coe_mk, OneHom.coe_mk]
      exact Fin.snoc_last (α := fun j : Fin ((rowSizes D).m + 1) => UG D.what₂.Tau ((rowSizes D).nR j)) _ _
    erw [e]
    show _ = (Matrix.reindex (finSumFinEquiv.trans (finCongr (rowSizes D).nC_succ)) (finSumFinEquiv.trans (finCongr (rowSizes D).nC_succ))
      (Matrix.fromBlocks (g.2 (Fin.last D.R.m) τ).1 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))).det
    rw [Matrix.det_reindex_self]
    exact ((Matrix.det_fromBlocks_zero₂₁ _ _ _).trans (by rw [Matrix.det_one, mul_one]; rfl)).symm
  | cast j =>
    show (compAt W.θ τ (mt (G.V (.top j)) (ptTop W g j))).det = _
    have hP : PosOnb W (.top j) := posOnb_of_defNode W μ0 hL (X := .top j) j.2.le
    rw [ptTop_lt W g j.2, compAt_kappa_fst g j hP τ, det_conj_submatrix (rank_top G j.2.le).symm (Matrix.isUnit_det_of_left_inverse (hP τ))]
    have e : rowComp (rowSizes D) g j.castSucc = g.1 j := by
      simp only [rowComp, MonoidHom.coe_mk, OneHom.coe_mk]
      exact Fin.snoc_castSucc (α := fun j : Fin ((rowSizes D).m + 1) => UG D.what₂.Tau ((rowSizes D).nR j)) _ _ j
    rw [e]

end EigTop2

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section EigTop3

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem movedVec_theta_fock (W : G.Weil) (μ0 : T) (hL : L.Is μ0) {U : Set T} (S : GridChoice W U) (t : T) {j : ℕ}
    (hj : j + 1 ≤ D.R.m) (d : FinDatum G t (.top t j)) (hd : S.Z.HasVec d) :
    IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) (movedVec t S d) ∧
      ∀ τ, IsFockVacAt (heisO W.ψ (G.pS (.top t j)) (G.pT (.top t j))) W.θ τ (cplxO 1 1) (movedVec t S d) := by
  have hr : (Pair.top t j : Pair T).InRange D.R.m := hj
  have hW := W.om_is _ hr
  have hX0 : DefNode D.R.m (.top j) := by show j ≤ D.R.m; omega
  have hX1 : DefNode D.R.m (.top (j + 1)) := hj
  have hc0 := cart_eq_one_of_posOnb W hX0.inRange (posOnb_of_defNode W μ0 hL hX0)
  have hc1 := cart_eq_one_of_posOnb W hX1.inRange (posOnb_of_defNode W μ0 hL hX1)
  obtain ⟨hv1, hv2⟩ := GlobalTheory.FockRealVec.vec_theta_fock W S.Z (p := .top t j) hj d hd
  have hv : ∀ τ, IsFockVacAt (heisO W.ψ (G.pS (.top t j)) (G.pT (.top t j))) W.θ τ (cplxO 1 1) (S.Z.vec d) := fun τ => by
    have := hv2 τ
    rwa [show G.cartS W.cart (.top t j) τ = 1 from hc0 τ, show G.onT W.cart (.top t j) τ = 1 from hc1 τ] at this
  refine ⟨hW.om_pres _ _ hv1, fun τ z => ?_⟩
  unfold movedVec
  generalize G.toPair (.top t j) (S.N.u (Pair.top t j).small).1 (S.N.u (Pair.top t j).big).1 = q
  obtain ⟨a, b⟩ := q
  obtain ⟨z₀, rfl⟩ : ∃ z₀ : Matrix (Fin (G.pT (.top t j)).rank) (Fin (G.pS (.top t j)).rank) ℂ, z = compAt W.θ τ (mt _ b) * z₀ * compAt W.θ τ (mt _ a⁻¹) := by
    refine ⟨compAt W.θ τ (mt _ b⁻¹) * z * compAt W.θ τ (mt _ a), ?_⟩
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.OrientedHeis.compAt_mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      GlobalTheory.OrientedHeis.compAt_mt_mul_inv, Matrix.mul_one]
  have h0 := congrArg (W.om _ (a, b)) (hv τ z₀)
  rw [GlobalTheory.FockMove.om_annih hW W.θ_is a b τ (by rw [Matrix.one_mul, Matrix.mul_one])
    (by rw [Matrix.one_mul, Matrix.mul_one]) z₀ hv1, map_zero] at h0
  exact h0

theorem cast_half {K : Type} [Field K] [CharZero K] {n : ℕ} (hn : Even n) : (((n / 2 : ℕ) : ℤ) : K) = (n : K) / 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [show (k + k) / 2 = k by omega]
  push_cast
  ring

end EigTop3

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

theorem om_ptTop_movedVec : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) {U : Set T} (S : GridChoice W U) (g : Gc D.what₂.Tau (GlobalTheory.RowReal.rowSizes D)) (t : T) (j : Fin D.R.m)
    (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    W.om (.top t j) (G.toPair (.top t j) (GlobalTheory.RowReal.ptTop W g j) (GlobalTheory.RowReal.ptTop W g (j + 1))) (movedVec t S d) =
      GlobalTheory.RowReal.rowScal (GlobalTheory.RowReal.rowEntries D sc.cGap) j g • movedVec t S d := by
  intro D T L sc G μ0 hL W U S g t j d hd
  have hj : (j : ℕ) + 1 ≤ D.R.m := j.2
  have hr : (Pair.top t (j : ℕ) : Pair T).InRange D.R.m := hj
  have hW := W.om_is _ hr
  have hX0 : DefNode D.R.m (.top j) := j.2.le
  have hX1 : DefNode D.R.m (.top ((j : ℕ) + 1)) := hj
  have hc0 := cart_eq_one_of_posOnb W hX0.inRange (posOnb_of_defNode W μ0 hL hX0)
  have hc1 := cart_eq_one_of_posOnb W hX1.inRange (posOnb_of_defNode W μ0 hL hX1)
  have hS : ∀ τ, IsCartanInv (gramAt D (G.V (.top j)) τ) 1 := fun τ => by
    have := W.cart_is _ hX0.inRange τ
    rwa [hc0 τ] at this
  have hT : ∀ τ, IsCartanInv (gramAt D (G.V (.top ((j : ℕ) + 1))) τ) 1 := fun τ => by
    have := W.cart_is _ hX1.inRange τ
    rwa [hc1 τ] at this
  obtain ⟨hm, hv⟩ := movedVec_theta_fock W μ0 hL S t hj d hd
  have ev0 : Even (G.V (.top j)).rank := by rw [rank_top G j.2.le]; exact even_nR _
  have ev1 : Even (G.V (.top ((j : ℕ) + 1))).rank := by rw [rank_top G hj]; exact even_nR _
  have hχS : G.chrS (.top t j) = L.mu t ((j : ℕ) + 1) := by
    show Formalism.IndefR.Lift.attChr (L.mu t ((j : ℕ) + 1)) L.eta (G.V (.top j)).rank = _
    simp [Formalism.IndefR.Lift.attChr, Nat.not_odd_iff_even.2 ev0]
  have hχT : G.chrT (.top t j) = L.mu t ((j : ℕ) + 1) := by
    show Formalism.IndefR.Lift.attChr (L.mu t ((j : ℕ) + 1)) L.eta (G.V (.top ((j : ℕ) + 1))).rank = _
    simp [Formalism.IndefR.Lift.attChr, Nat.not_odd_iff_even.2 ev1]
  have hexp : ∀ τ, HasInfExp D (L.mu t ((j : ℕ) + 1)) τ (-(((rowEntries D sc.cGap τ).e j : ℤ) : ℚ)) := fun τ => by
    have h := GlobalTheory.GridJoin.ColIt.hasInfExp_mu L hL t j τ
    have e : (((rowEntries D sc.cGap τ).e j : ℤ) : ℚ) = (D.hc τ).e j := by
      show (((num D sc.cGap τ).e ((j : ℕ) + 1) : ℤ) : ℚ) = _
      rw [num_e D sc.cGap τ (by omega) hj]
      rfl
    rwa [e]
  have key := GlobalTheory.VacuumCharacter.vacuum_character D W.ψ W.θ (G.V (.top j)) (G.V (.top ((j : ℕ) + 1)))
    (G.chrS (.top t j)) (G.chrT (.top t j)) (W.om (.top t j)) hW W.θ_is (hX0.sigOK G) (hX1.sigOK G) (fun _ => 1) hS hT
    (fun τ => -(((rowEntries D sc.cGap τ).e j : ℤ) : ℚ)) (fun τ => -(((rowEntries D sc.cGap τ).e j : ℤ) : ℚ))
    (fun τ => by rw [hχS]; exact hexp τ) (fun τ => by rw [hχT]; exact hexp τ)
    (fun τ => -(rowEntries D sc.cGap τ).e j + ((rowSizes D).nR j.castSucc / 2 : ℕ))
    (fun τ => -(rowEntries D sc.cGap τ).e j - ((rowSizes D).nR j.castSucc / 2 : ℕ))
    (fun τ => (rowEntries D sc.cGap τ).e j - ((rowSizes D).nR j.succ / 2 : ℕ))
    (fun τ => by
      rw [Int.cast_add, Int.cast_neg, Fin.val_castSucc, cast_half (even_nR (S := rowSizes D) j), rank_top G j.2.le])
    (fun τ => by
      rw [Int.cast_sub, Int.cast_neg, Fin.val_castSucc, cast_half (even_nR (S := rowSizes D) j), rank_top G j.2.le])
    (fun τ => by
      rw [Matrix.trace_one, Fintype.card_fin, rank_top G hj, Int.cast_sub, Fin.val_succ,
        cast_half (even_nR (S := rowSizes D) ((j : ℕ) + 1))]
      push_cast
      ring)
    (movedVec t S d) hm hv (ptTop W g j) (ptTop_mem W g j) (ptTop W g ((j : ℕ) + 1)) (ptTop_mem W g _)
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
  rw [show G.toPair (.top t j) (ptTop W g j) (ptTop W g ((j : ℕ) + 1)) = (ptTop W g j, ptTop W g ((j : ℕ) + 1)) from rfl, key]
  congr 1
  clear key hexp hχS hχT ev0 ev1 hm hv hS hT hc0 hc1 hW hr hd
  have a1 : (1 / 2 : ℂ) • ((1 : Matrix (Fin (G.V (.top ((j : ℕ) + 1))).rank) (Fin (G.V (.top ((j : ℕ) + 1))).rank) ℂ) + 1) = 1 := by
    module
  simp only [a1, sub_self, smul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add, Matrix.det_one, one_zpow, mul_one]
  have hg : ∀ τ, (compAt W.θ τ (mt (G.V (.top j)) (ptTop W g j))).det = (rowComp (rowSizes D) g j.castSucc τ).1.det :=
    fun τ => det_compAt_ptTop W μ0 hL S.N g j.castSucc τ
  have hh : ∀ τ, (compAt W.θ τ (mt (G.V (.top ((j : ℕ) + 1))) (ptTop W g ((j : ℕ) + 1)))).det =
      (rowComp (rowSizes D) g j.succ τ).1.det :=
    fun τ => det_compAt_ptTop W μ0 hL S.N g j.succ τ
  simp only [hg, hh]
  simp [rowScal, detChar, detU, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun τ _ => mul_comm _ _

end GlobalTheory.RowReal
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactChain_topPair_movedVector_rowCharacter : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) {U : Set T} (S : GridChoice W U) (g : Gc D.what₂.Tau (GlobalTheory.RowReal.rowSizes D)) (t : T) (j : Fin D.R.m)
    (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    W.om (.top t j) (G.toPair (.top t j) (GlobalTheory.RowReal.ptTop W g j) (GlobalTheory.RowReal.ptTop W g (j + 1))) (movedVec t S d) =
      GlobalTheory.RowReal.rowScal (GlobalTheory.RowReal.rowEntries D sc.cGap) j g • movedVec t S d := by
  atlas_forward_decl GlobalTheory.RowReal.om_ptTop_movedVec
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem hasInfExp_attChr_chi {μ0 : T} (hL : L.Is μ0) {i : ℕ} (hi : i < D.R.m) (n : ℕ) (τ : D.what₂.Tau) :
    HasInfExp D (Formalism.IndefR.Lift.attChr (G.ch.chi (D.R.m - i)) L.eta n) τ
      ((cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd n then 1 / 2 else 0) := by
  have hm1 : 1 ≤ D.R.m - i := by omega
  have hm2 : D.R.m - i ≤ D.R.m := by omega
  have h0 : HasInfExp D (G.ch.chi (D.R.m - i)) τ (cen D sc.cGap τ (D.R.m - i) : ℚ) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ)) (G.ch.chi_eq _ hm1 hm2)
      ⟨fun τ => 2 * cen D sc.cGap τ (D.R.m - i), fun τ => by push_cast; ring, G.ch.inf _ hm1 hm2⟩ τ
  have heta : HasInfExp D L.eta τ (1 / 2) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
      (GlobalTheory.Chain.StepVac.hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  unfold Formalism.IndefR.Lift.attChr
  split_ifs
  · rw [sub_eq_add_neg]
    exact GlobalTheory.Chain.StepVac.hasInfExp_mul h0 (GlobalTheory.Chain.StepVac.hasInfExp_inv heta)
  · simpa using h0

theorem rowEntries_c_rev (τ : D.what₂.Tau) (i : Fin D.R.m) :
    (rowEntries D sc.cGap τ).c i.rev = cen D sc.cGap τ (D.R.m - i) := by
  show (num D sc.cGap τ).cen ((i.rev : ℕ) + 1) = _
  rw [Fin.val_rev, show D.R.m - (i + 1) + 1 = D.R.m - i by omega]
  rfl

theorem half_ceil (n : ℕ) : (((n + 1) / 2 : ℕ) : ℚ) = (n : ℚ) / 2 + if Odd n then 1 / 2 else 0 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [if_neg (Nat.not_odd_iff_even.2 ⟨k, hk⟩), hk, show (k + k + 1) / 2 = k by omega]
    push_cast; ring
  · rw [if_pos ⟨k, hk⟩, hk, show (2 * k + 1 + 1) / 2 = k + 1 by omega]
    push_cast; ring

theorem det_compAt_ptGrid {μ0 : T} (hL : L.Is μ0) (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (n : ℕ) (hn : n < D.R.m + 1)
    (τ : D.what₂.Tau) :
    (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid n D.R.m)) (ptGrid W g n))).det =
      Matrix.det (g.2 ⟨n, hn⟩ τ).1 := by
  have hX : DefNode D.R.m (.grid n D.R.m) := ⟨Nat.lt_succ_iff.1 hn, rfl⟩
  have hW := posOnb_of_defNode W μ0 hL hX
  have hB : IsUnit (W.onb (.grid n D.R.m) τ).det := by
    have h := congrArg Matrix.det (hW τ)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at h
    exact isUnit_iff_ne_zero.2 fun h0 => by rw [h0, mul_zero] at h; exact zero_ne_one h
  rw [ptGrid_le W g hn, compAt_kappa_snd g ⟨n, hn⟩ hW τ, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv,
    mul_right_comm, Ring.mul_inverse_cancel _ hB, one_mul]
  exact Matrix.det_submatrix_equiv_self (finCongr (rank_gridM G (Nat.lt_succ_iff.1 hn))) _

theorem om_ptGrid_movedVec : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) {U : Set T} (S : GridChoice W U) (g : Gc D.what₂.Tau (GlobalTheory.RowReal.rowSizes D)) (t : T) (i : Fin D.R.m)
    (d : FinDatum G t (.chi i D.R.m)), S.Z.HasVec d →
    W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (GlobalTheory.RowReal.ptGrid W g i) (GlobalTheory.RowReal.ptGrid W g (i + 1))) (movedVec t S d) =
      GlobalTheory.RowReal.colScal (GlobalTheory.RowReal.rowEntries D sc.cGap) i g • movedVec t S d := by
  intro D T L sc G μ0 hL W U S g t i d hd
  have hp : DefPair D.R.m (.chi (i : ℕ) D.R.m : Pair T) := ⟨i.2, rfl⟩
  have hn := DefPair.nodes hp
  have hom := W.om_is (.chi (i : ℕ) D.R.m) (by
    simp only [DefPair, DefNode] at hp hn; simp only [Pair.InRange, Node.InRange]; omega)
  obtain ⟨h1, h2⟩ := GlobalTheory.T.gridFiniteDatumVector_theta_fockVacuum W S.Z hp d hd
  have hf : IsThetaFunO W.ψ _ _ (movedVec t S d) ∧ ∀ τ, IsFockVacAt (heisO W.ψ _ _) W.θ τ
      (cplxO (G.cartS W.cart (.chi (i : ℕ) D.R.m) τ) (G.onT W.cart (.chi (i : ℕ) D.R.m) τ)) (movedVec t S d) :=
    GlobalTheory.T.weil_finitePoint_preserves_fockVacuum D W.ψ W.θ _ _ _ _ (W.om _) hom W.θ_is _ _ _ h1 h2 _
      (GlobalTheory.FockReal.negGA_mem_GfC _ (S.N.u _).2) _ (S.N.u _).2
  have hrS : (G.pS (.chi (i : ℕ) D.R.m : Pair T)).rank = (rowSizes D).nC ((i : ℕ) + 1) := rank_gridM G (by omega)
  have hrT : (G.pT (.chi (i : ℕ) D.R.m : Pair T)).rank = (rowSizes D).nC (i : ℕ) := rank_gridM G (by omega)
  have key := GlobalTheory.FockReal.om_fockIn hL W W.onb hp (fun X hX τ => GlobalTheory.FockReal.onb_def hL W hX τ)
    (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd (G.pS (.chi (i : ℕ) D.R.m : Pair T)).rank then 1 / 2 else 0)
    (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd (G.pT (.chi (i : ℕ) D.R.m : Pair T)).rank then 1 / 2 else 0)
    (fun τ => hasInfExp_attChr_chi hL i.2 _ τ) (fun τ => hasInfExp_attChr_chi hL i.2 _ τ)
    (fun τ => (rowEntries D sc.cGap τ).c i.rev - (((rowSizes D).nC i.succ + 1) / 2 : ℕ))
    (fun τ => -(rowEntries D sc.cGap τ).c i.rev + (((rowSizes D).nC i.castSucc + 1) / 2 : ℕ))
    (fun τ => ?_) (fun τ => ?_) _ hf.1 hf.2 (ptGrid W g i) (ptGrid_mem W g i) (ptGrid W g (i + 1))
    (ptGrid_mem W g (i + 1)) 1
  · have e1 : fockIn W W.onb (.chi (i : ℕ) D.R.m) (movedVec t S d) 1 = movedVec t S d :=
      GlobalTheory.FiniteFock.pureTensorO_one _ _ _ _ _ _ _ _ _
    rw [show GlobalTheory.FockReal.realSubst W W.onb (.chi (i : ℕ) D.R.m) (ptGrid W g i) (ptGrid W g (i + 1)) 1 = 1 from
      map_one _, e1] at key
    rw [key]
    congr 1
    simp only [GlobalTheory.FockReal.realChar, GridData.toPair, mt_negGA]
    simp only [det_compAt_ptGrid hL W g (i : ℕ) (by omega), det_compAt_ptGrid hL W g ((i : ℕ) + 1) (by omega)]
    simp only [colScal, detChar, detU, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul, Units.coe_prod,
      Units.val_zpow_eq_zpow_val, MonoidHom.coe_toHomUnits, MonoidHom.coe_comp, Function.comp_apply]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [mul_comm]
    rfl
  · simp only [GlobalTheory.FockReal.sgnP, rowEntries_c_rev, Fin.val_succ, rank_gridM G (show (i : ℕ) + 1 ≤ D.R.m by omega),
      Int.cast_sub, Int.cast_natCast, half_ceil]
    ring
  · simp only [GlobalTheory.FockReal.sgnP, rowEntries_c_rev, Fin.val_castSucc, hrT, Int.cast_add, Int.cast_neg, Int.cast_natCast,
      half_ceil]
    ring

end GlobalTheory.RowReal
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactChain_chiPair_movedVector_columnCharacter : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) {U : Set T} (S : GridChoice W U) (g : Gc D.what₂.Tau (GlobalTheory.RowReal.rowSizes D)) (t : T) (i : Fin D.R.m)
    (d : FinDatum G t (.chi i D.R.m)), S.Z.HasVec d →
    W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (GlobalTheory.RowReal.ptGrid W g i) (GlobalTheory.RowReal.ptGrid W g (i + 1))) (movedVec t S d) =
      GlobalTheory.RowReal.colScal (GlobalTheory.RowReal.rowEntries D sc.cGap) i g • movedVec t S d := by
  atlas_forward_decl GlobalTheory.RowReal.om_ptGrid_movedVec
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

theorem fockSubAll_rename_unitary {D : D7} {m n a b : ℕ} (ha : n = a) (hb : m = b)
    (u : UG D.what₂.Tau a) (v : UG D.what₂.Tau b) (Q : MvPolynomial (FVar D m n) ℂ) :
    MvPolynomial.rename (fun x : FVar D m n => (x.1, Fin.cast hb x.2.1, Fin.cast ha x.2.2))
      (fockSubAll (fun _ => n) (fun _ => m)
        (fun τ => ((u τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast ha) (Fin.cast ha))
        (fun τ => ((v τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast hb) (Fin.cast hb)) Q) =
      linSub (homMat a b (u, v))
        (MvPolynomial.rename (fun x : FVar D m n => (x.1, Fin.cast hb x.2.1, Fin.cast ha x.2.2)) Q) := by
  subst ha hb
  have hinv : ∀ τ, ((u τ : Matrix (Fin n) (Fin n) ℂ))⁻¹ = star (u τ : Matrix (Fin n) (Fin n) ℂ) :=
    fun τ => Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 (u τ).2)
  have hc : ∀ k : ℕ, (Fin.cast (rfl : k = k)) = id := fun k => by funext i; rfl
  rw [hc, hc]
  have hid : (fun x : FVar D m n => (x.1, (id x.2.1 : Fin m), (id x.2.2 : Fin n))) = id := rfl
  rw [hid, MvPolynomial.rename_id, AlgHom.id_apply, AlgHom.id_apply]
  have hs : ∀ k (M : Matrix (Fin k) (Fin k) ℂ), M.submatrix id id = M := fun _ _ => rfl
  simp only [hs]
  show _ = (MvPolynomial.aeval (R := ℂ) fun p : D.what₂.Tau × (Fin m × Fin n) => ∑ j, MvPolynomial.C ((homMat n m (u, v)) p.1 j p.2) *
    (MvPolynomial.X (p.1, j) : MvPolynomial (D.what₂.Tau × (Fin m × Fin n)) ℂ)) Q
  refine DFunLike.congr_fun ?_ Q
  refine MvPolynomial.algHom_ext fun y => ?_
  obtain ⟨τ, p, q⟩ := y
  simp only [fockSubAll, MvPolynomial.aeval_X, hinv, homMat, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Fin.is_lt, iff_self, if_true, Matrix.transpose_apply, Matrix.star_apply]

theorem trCol_fockSubAll_unitary : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (j : Fin D.R.m)
    (u : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nR j)) (v : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nR (j + 1)))
    (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank),
    GlobalTheory.RowReal.trCol G j (GlobalTheory.RowReal.fockSubAll (fun _ => (G.V (.top j)).rank) (fun _ => (G.V (.top (j + 1))).rank)
      (fun τ => ((u τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j) j.2.le))
        (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j) j.2.le)))
      (fun τ => ((v τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j + 1) j.2))
        (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j + 1) j.2))) Q) =
      linSub (homMat _ _ (u, v)) (GlobalTheory.RowReal.trCol G j Q) := by
  intro D T L sc G j u v Q
  exact fockSubAll_rename_unitary _ _ u v Q

end GlobalTheory.RowReal
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockSubstitution_rowStep_rename_unitary : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (j : Fin D.R.m)
    (u : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nR j)) (v : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nR (j + 1)))
    (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank),
    GlobalTheory.RowReal.trCol G j (GlobalTheory.RowReal.fockSubAll (fun _ => (G.V (.top j)).rank) (fun _ => (G.V (.top (j + 1))).rank)
      (fun τ => ((u τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j) j.2.le))
        (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j) j.2.le)))
      (fun τ => ((v τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j + 1) j.2))
        (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j + 1) j.2))) Q) =
      linSub (homMat _ _ (u, v)) (GlobalTheory.RowReal.trCol G j Q) := by
  atlas_forward_decl GlobalTheory.RowReal.trCol_fockSubAll_unitary
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Kronecker

namespace GlobalTheory.RowReal

theorem sum_conjSub_cast {ι : Type} {a a' b b' : ℕ} (ha : a = a') (hb : b = b') (U : Matrix (Fin a') (Fin a') ℂ)
    (V : Matrix (Fin b') (Fin b') ℂ) (hV : star V * V = 1) (τ : ι) (p : Fin a) (q : Fin b) :
    ∑ x : Fin a, ∑ y : Fin b, MvPolynomial.C ((starRingEnd ℂ) (U.submatrix (Fin.cast ha) (Fin.cast ha) x p) *
        (starRingEnd ℂ) ((V.submatrix (Fin.cast hb) (Fin.cast hb))⁻¹ q y)) *
        (MvPolynomial.X (τ, Fin.cast hb y, Fin.cast ha x) : MvPolynomial (ι × Fin b' × Fin a') ℂ) =
      ∑ x : Fin b', ∑ y : Fin a', MvPolynomial.C ((V ⊗ₖ (star U)ᵀ) (x, y) (Fin.cast hb q, Fin.cast ha p)) *
        MvPolynomial.X (τ, x, y) := by
  subst ha hb
  have e : ∀ {n : ℕ} (h : n = n) (M : Matrix (Fin n) (Fin n) ℂ), M.submatrix (Fin.cast h) (Fin.cast h) = M := fun _ _ => by
    ext; simp
  simp only [e, Fin.cast_eq_self]
  rw [Matrix.inv_eq_left_inv hV, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  congr 2
  simp only [Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.star_apply, RCLike.star_def, RingHomCompTriple.comp_apply,
    RingHom.id_apply, Complex.conj_conj]
  ring

theorem trRow_fockSubAll : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i : Fin D.R.m)
    (u : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nC i)) (v : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nC (i + 1)))
    (Q : PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank),
    GlobalTheory.RowReal.trRow G i (GlobalTheory.RowReal.fockSubAll (fun _ => 0) (fun _ => (G.V (.grid i D.R.m)).rank)
      (fun τ => ((v τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i + 1) i.2))
        (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i + 1) i.2)))
      (fun τ => ((u τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i) i.2.le))
        (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i) i.2.le))) Q) =
      linSub (homMat _ _ (u, v)) (GlobalTheory.RowReal.trRow G i Q) := by
  intro D T L sc G i u v Q
  have hL : ∀ P, linSub (homMat _ _ (u, v)) P = MvPolynomial.aeval (R := ℂ) (fun p : D.what₂.Tau × (Fin ((rowSizes D).nC (i + 1)) × Fin ((rowSizes D).nC i)) => ∑ j, MvPolynomial.C ((homMat _ _ (u, v)) p.1 j p.2) * (MvPolynomial.X (p.1, j) : MvPolynomial _ ℂ)) P := fun _ => rfl
  rw [hL, ← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  rintro ⟨τ, p, q⟩
  simp only [AlgHom.comp_apply, fockSubAll, trRow, MvPolynomial.aeval_X, MvPolynomial.rename_X, map_sum, map_mul, MvPolynomial.rename_C, Fintype.sum_prod_type]
  have hc : ¬ ((p : ℕ) < (G.V (.grid i D.R.m)).rank ↔ (q : ℕ) < 0) := by simp [p.2]
  simp only [if_neg hc]
  have hH : ∀ τ', homMat _ _ (u, v) τ' = ((v τ' : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) ⊗ₖ (star ((u τ' : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ))ᵀ := fun _ => rfl
  simp only [hH]
  exact sum_conjSub_cast _ _ _ _ (v τ).2.1 τ p q

end GlobalTheory.RowReal
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockSubstitution_columnStep_rename_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i : Fin D.R.m)
    (u : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nC i)) (v : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nC (i + 1)))
    (Q : PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank),
    GlobalTheory.RowReal.trRow G i (GlobalTheory.RowReal.fockSubAll (fun _ => 0) (fun _ => (G.V (.grid i D.R.m)).rank)
      (fun τ => ((v τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i + 1) i.2))
        (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i + 1) i.2)))
      (fun τ => ((u τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i) i.2.le))
        (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i) i.2.le))) Q) =
      linSub (homMat _ _ (u, v)) (GlobalTheory.RowReal.trRow G i Q) := by
  atlas_forward_decl GlobalTheory.RowReal.trRow_fockSubAll
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedVector_definitePair_theta_fockVacuum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T}
    (S : GridChoice W U) (t : T) (p : Pair T), DefPair D.R.m p → ∀ d : FinDatum G t p, S.Z.HasVec d →
    IsThetaFunO W.ψ (G.pS p) (G.pT p) (movedVec t S d) ∧
      ∀ ρ, IsFockVacAt (heisO W.ψ (G.pS p) (G.pT p)) W.θ ρ (cplxO (G.cartS W.cart p ρ) (G.onT W.cart p ρ)) (movedVec t S d) := by
  first | exact @GlobalTheory.RowReal.movedVec_theta_fockVac | exact GlobalTheory.RowReal.movedVec_theta_fockVac | (intros; apply GlobalTheory.RowReal.movedVec_theta_fockVac <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowReal

section DefOnb

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem gramAt_negSp (V : HSp D) (ρ : D.what₂.Tau) : gramAt D (negSp V) ρ = -gramAt D V ρ := by
  unfold gramAt
  rw [negSp_gram]
  exact Matrix.map_neg _ (map_neg (tauE D ρ)) _

theorem isCartanInv_neg {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : IsCartanInv (-G) (-s) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [neg_mul_neg, h1], ?_, ?_⟩
  · rw [Matrix.conjTranspose_neg, neg_mul_neg, Matrix.mul_neg, h2]
  · rw [neg_mul_neg]; exact h3

theorem defNode_cart_onb {μ0 : T} (hL : L.Is μ0) (W : G.Weil) (X : Node) (hX : DefNode D.R.m X) (ρ : D.what₂.Tau) :
    IsCartanInv (gramAt D (G.V X) ρ) (W.cart X ρ) ∧ IsONBasis (gramAt D (G.V X) ρ) (W.cart X ρ) (W.onb X ρ) (G.V X).rank ∧
    IsCartanInv (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) ∧
      IsONBasis (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) (W.onb X ρ) 0 := by
  have hC := W.cart_is X hX.inRange ρ
  have hP : (W.onb X ρ)ᴴ * gramAt D (G.V X) ρ * W.onb X ρ = 1 := posOnb_of_defNode W μ0 hL hX ρ
  obtain ⟨ε, h1, h2⟩ := W.onb_is X hX.inRange ρ
  have hJ : Formalism.REAL.Jm ε = 1 := h1.symm.trans hP
  rw [hJ, Matrix.mul_one] at h2
  have hn : gramAt D (negSp (G.V X)) ρ = -gramAt D (G.V X) ρ := gramAt_negSp _ _
  refine ⟨hC, ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, ?_⟩, ?_, ⟨fun _ => -1, fun a => Or.inr ⟨rfl, Nat.zero_le _⟩, ?_, ?_⟩⟩
  · rw [hP]; simp [Matrix.diagonal_one]
  · rw [h2]; simp [Matrix.diagonal_one]
  · rw [hn]; exact isCartanInv_neg hC
  · rw [hn, Matrix.mul_neg, Matrix.neg_mul, hP]
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, h]
  · rw [Matrix.neg_mul, h2]
    ext i j
    simp [Matrix.mul_diagonal]

theorem defNode_cart_onb_all : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) (X : Node), DefNode D.R.m X → ∀ ρ,
    IsCartanInv (gramAt D (G.V X) ρ) (W.cart X ρ) ∧ IsONBasis (gramAt D (G.V X) ρ) (W.cart X ρ) (W.onb X ρ) (G.V X).rank ∧
    IsCartanInv (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) ∧
      IsONBasis (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) (W.onb X ρ) 0 :=
  fun hL W X hX ρ => defNode_cart_onb hL W X hX ρ

end DefOnb

end GlobalTheory.RowReal
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) (X : Node), DefNode D.R.m X → ∀ ρ,
    IsCartanInv (gramAt D (G.V X) ρ) (W.cart X ρ) ∧ IsONBasis (gramAt D (G.V X) ρ) (W.cart X ρ) (W.onb X ρ) (G.V X).rank ∧
    IsCartanInv (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) ∧
      IsONBasis (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) (W.onb X ρ) 0 := by
  atlas_forward_decl GlobalTheory.RowReal.defNode_cart_onb_all
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowReal

theorem mul_adaptedFrame_of_blocks {N r c N' : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (F : Matrix (Fin N) (Fin r) ℂ)
    (O Mmm : Matrix (Fin r) (Fin r) ℂ) (Zc : Matrix (Fin N) (Fin 1) ℂ) (y : Matrix (Fin c) (Fin c) ℂ)
    (hr : r = c) (hc : c + 1 = N') (hN : N = N') (hO : IsUnit O.det)
    (h1 : A * F = F * Mmm) (h2 : Mmm = O * y.submatrix (Fin.cast hr) (Fin.cast hr) * O⁻¹) (h3 : A * Zc = Zc) :
    A * Matrix.of (fun a k => Sum.elim (fun b : Fin c => (F * O) a (Fin.cast hr.symm b)) (fun _ : Fin 1 => Zc a 0)
      ((finSumFinEquiv.trans (finCongr hc)).symm (Fin.cast hN k))) =
    Matrix.of (fun a k => Sum.elim (fun b : Fin c => (F * O) a (Fin.cast hr.symm b)) (fun _ : Fin 1 => Zc a 0)
      ((finSumFinEquiv.trans (finCongr hc)).symm (Fin.cast hN k))) *
      (Matrix.reindex (finSumFinEquiv.trans (finCongr hc)) (finSumFinEquiv.trans (finCongr hc))
        (Matrix.fromBlocks y 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))).submatrix (Fin.cast hN) (Fin.cast hN) := by
  subst hr hc hN
  set e := finSumFinEquiv (m := r) (n := 1)
  have hT : Matrix.of (fun a k => Sum.elim (fun b : Fin r => (F * O) a (Fin.cast rfl b)) (fun _ : Fin 1 => Zc a 0)
      ((e.trans (finCongr rfl)).symm (Fin.cast rfl k))) = (Matrix.fromCols (F * O) Zc).submatrix id e.symm := by
    ext a k
    simp only [Matrix.of_apply, Fin.cast_eq_self, Matrix.submatrix_apply, id]
    rcases h : e.symm k with b | b
    · simp [h, Matrix.fromCols]
    · simp [h, Matrix.fromCols, Subsingleton.elim b 0]
  have hK : (Matrix.reindex (e.trans (finCongr rfl)) (e.trans (finCongr rfl))
        (Matrix.fromBlocks y 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))).submatrix (Fin.cast rfl) (Fin.cast rfl) =
      (Matrix.fromBlocks y 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix e.symm e.symm := by
    ext a k
    simp [Matrix.reindex_apply]
  rw [hT, hK, Matrix.submatrix_mul_equiv]
  have hL : A * (Matrix.fromCols (F * O) Zc).submatrix id e.symm = (A * Matrix.fromCols (F * O) Zc).submatrix id e.symm := by
    ext a k
    rfl
  rw [hL, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, h3]
  congr 2
  · rw [← Matrix.mul_assoc, h1, h2]
    simp only [Fin.cast_eq_self, Matrix.submatrix_id_id, Matrix.mul_zero, add_zero, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hO, Matrix.mul_one]
    congr 2
  · simp

theorem ptTop_inOnb : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) (g : Gc D.what₂.Tau (GlobalTheory.RowReal.rowSizes D)) (n : Fin (D.R.m + 1)),
    ((n : ℕ) = D.R.m → ∀ τ, W.onb (.top D.R.m) τ = GlobalTheory.RowReal.topFrame W τ) → ∀ τ,
    (W.onb (.top n) τ)⁻¹ * compAt W.θ τ (mt _ (GlobalTheory.RowReal.ptTop W g n)) * W.onb (.top n) τ =
      (rowComp (GlobalTheory.RowReal.rowSizes D) g n τ).1.submatrix (Fin.cast (GlobalTheory.RowReal.rank_top G (Nat.lt_succ_iff.1 n.2)))
        (Fin.cast (GlobalTheory.RowReal.rank_top G (Nat.lt_succ_iff.1 n.2))) := by
  intro D T L sc G μ0 hL W g n hn τ
  by_cases h : (n : ℕ) < D.R.m
  · have hP : PosOnb W (.top (⟨n, h⟩ : Fin D.R.m)) := posOnb_of_defNode W μ0 hL (X := .top (⟨n, h⟩ : Fin D.R.m)) h.le
    have hd : IsUnit (W.onb (.top (⟨n, h⟩ : Fin D.R.m)) τ).det := Matrix.isUnit_det_of_left_inverse (hP τ)
    have e1 := compAt_kappa_fst g ⟨n, h⟩ hP τ
    have e2 : ∀ k : Fin D.R.m, (rowComp (rowSizes D) g (Fin.castSucc k) τ).1 = (g.1 k τ).1 := fun k => by
      simp only [rowComp, MonoidHom.coe_mk, OneHom.coe_mk]
      exact congrArg (fun x => (x τ).1) (Fin.snoc_castSucc (α := fun j : Fin ((rowSizes D).m + 1) => UG D.what₂.Tau ((rowSizes D).nR j))
        (embed (rowSizes D).nC_succ (g.2 (Fin.last _))) g.1 k)
    obtain ⟨k, rfl⟩ : ∃ k : Fin D.R.m, n = Fin.castSucc k := ⟨⟨n, h⟩, Fin.ext rfl⟩
    rw [ptTop_lt W g h]
    erw [e1]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
    erw [e2 k]
    rfl
  · have hm : (n : ℕ) = D.R.m := by have := n.2; omega
    obtain rfl : n = Fin.last D.R.m := Fin.ext hm
    have hF := hn rfl
    have hPt : PosOnb W (.top D.R.m) := posOnb_of_defNode W μ0 hL (X := .top D.R.m) le_rfl
    have hPg : PosOnb W (.grid (Fin.last D.R.m : Fin (D.R.m + 1)) D.R.m) :=
      posOnb_of_defNode W μ0 hL (X := .grid (Fin.last D.R.m : Fin (D.R.m + 1)) D.R.m) ⟨Nat.lt_succ_iff.1 (Fin.last D.R.m).2, rfl⟩
    have hdT : IsUnit (topFrame W τ).det := by
      rw [← hF τ]; exact Matrix.isUnit_det_of_left_inverse (hPt τ)
    have hdO : IsUnit (W.onb (.grid D.R.m D.R.m) τ).det := Matrix.isUnit_det_of_left_inverse (hPg τ)
    have h1 : compAt W.θ τ (mt (G.V (.top D.R.m)) (kappaTop W g)) *
        (frameMat (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) G.sp.topDec.ι).map (tauE D τ) =
        (frameMat (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) G.sp.topDec.ι).map (tauE D τ) *
          compAt W.θ τ (mt (G.V (.grid D.R.m D.R.m)) ((kappa W g).2 (Fin.last D.R.m))) := (archM_kappaTop W g τ).1
    have h3 : compAt W.θ τ (mt (G.V (.top D.R.m)) (kappaTop W g)) * G.sp.topDec.a.map (tauE D τ) =
        G.sp.topDec.a.map (tauE D τ) := (archM_kappaTop W g τ).2
    have h2 : compAt W.θ τ (mt (G.V (.grid D.R.m D.R.m)) ((kappa W g).2 (Fin.last D.R.m))) =
        W.onb (.grid D.R.m D.R.m) τ * (g.2 (Fin.last D.R.m) τ).1.submatrix (Fin.cast (rank_gridM G (i := D.R.m) le_rfl))
          (Fin.cast (rank_gridM G (i := D.R.m) le_rfl)) * (W.onb (.grid D.R.m D.R.m) τ)⁻¹ :=
      compAt_kappa_snd g (Fin.last D.R.m) hPg τ
    have hA := mul_adaptedFrame_of_blocks (c := (rowSizes D).nC D.R.m) _ _ _ _ _
      ((g.2 (Fin.last D.R.m) τ).1 : Matrix (Fin ((rowSizes D).nC D.R.m)) (Fin ((rowSizes D).nC D.R.m)) ℂ)
      (rank_gridM G (i := D.R.m) le_rfl) (rowSizes D).nC_succ (rank_top G (j := D.R.m) le_rfl) hdO h1 h2 h3
    have key : (topFrame W τ)⁻¹ * compAt W.θ τ (mt _ (kappaTop W g)) * topFrame W τ =
        (embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) τ).1.submatrix
          (Fin.cast (rank_top G (j := D.R.m) le_rfl)) (Fin.cast (rank_top G (j := D.R.m) le_rfl)) := by
      have hA' : compAt W.θ τ (mt _ (kappaTop W g)) * topFrame W τ = topFrame W τ *
          (embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) τ).1.submatrix
            (Fin.cast (rank_top G (j := D.R.m) le_rfl)) (Fin.cast (rank_top G (j := D.R.m) le_rfl)) := hA
      rw [Matrix.mul_assoc, hA', ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdT, Matrix.one_mul]
    have hlast : rowComp (rowSizes D) g (Fin.last D.R.m) = embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) := by
      simp only [rowComp, MonoidHom.coe_mk, OneHom.coe_mk]; exact Fin.snoc_last (α := fun j : Fin ((rowSizes D).m + 1) => UG D.what₂.Tau ((rowSizes D).nR j)) _ _
    rw [show ptTop W g ((Fin.last D.R.m : Fin (D.R.m + 1)) : ℕ) = kappaTop W g from ptTop_m W g]
    erw [hlast, hF τ]
    exact key

end GlobalTheory.RowReal
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactChainTopRowRealPoint_inOrthonormalBasis : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) (g : Gc D.what₂.Tau (GlobalTheory.RowReal.rowSizes D)) (n : Fin (D.R.m + 1)),
    ((n : ℕ) = D.R.m → ∀ τ, W.onb (.top D.R.m) τ = GlobalTheory.RowReal.topFrame W τ) → ∀ τ,
    (W.onb (.top n) τ)⁻¹ * compAt W.θ τ (mt _ (GlobalTheory.RowReal.ptTop W g n)) * W.onb (.top n) τ =
      (rowComp (GlobalTheory.RowReal.rowSizes D) g n τ).1.submatrix (Fin.cast (GlobalTheory.RowReal.rank_top G (Nat.lt_succ_iff.1 n.2)))
        (Fin.cast (GlobalTheory.RowReal.rank_top G (Nat.lt_succ_iff.1 n.2))) := by
  atlas_forward_decl GlobalTheory.RowReal.ptTop_inOnb
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem om_fock_chi {μ0 : T} (hL : L.Is μ0) (W : G.Weil) {U : Set T} (S : GridChoice W U)
    (g : Gc D.what₂.Tau (rowSizes D)) (t : T) (i : Fin D.R.m)
    (d : FinDatum G t (.chi i D.R.m)) (hd : S.Z.HasVec d)
    (Q Q' : PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank)
    (hQ : trRow G i Q' = colFock (rowEntries D sc.cGap) i g (trRow G i Q)) :
    W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (ptGrid W g i) (ptGrid W g (i + 1)))
        (W.fock (.chi i D.R.m) (movedVec t S d) Q) =
      W.fock (.chi i D.R.m) (movedVec t S d) Q' := by
  have hX : DefNode D.R.m (.grid (i : ℕ) D.R.m) := ⟨i.2.le, rfl⟩
  have hY : DefNode D.R.m (.grid ((i : ℕ) + 1) D.R.m) := ⟨i.2, rfl⟩
  have hp : DefPair D.R.m (Pair.chi (i : ℕ) D.R.m : Pair T) := ⟨i.2, rfl⟩
  obtain ⟨hf, hv⟩ := GlobalTheory.T.movedVector_definitePair_theta_fockVacuum W S t (.chi i D.R.m) hp d hd
  have hc := GlobalTheory.T.compactChain_chiPair_movedVector_columnCharacter hL W S g t i d hd
  let u : UG D.what₂.Tau ((rowSizes D).nC (i : ℕ)) := g.2 ⟨(i : ℕ), Nat.lt_succ_of_lt i.2⟩
  let v : UG D.what₂.Tau ((rowSizes D).nC ((i : ℕ) + 1)) := g.2 ⟨(i : ℕ) + 1, Nat.succ_lt_succ i.2⟩
  have c1 : ∀ τ, compAt W.θ τ (mt (G.V (.grid ((i : ℕ) + 1) D.R.m)) (ptGrid W g ((i : ℕ) + 1))) =
      W.onb (.grid ((i : ℕ) + 1) D.R.m) τ * (v τ).1.submatrix
        (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) *
        (W.onb (.grid ((i : ℕ) + 1) D.R.m) τ)⁻¹ := fun τ => by
    rw [ptGrid_le W g (Nat.succ_lt_succ i.2)]
    exact compAt_kappa_snd g ⟨(i : ℕ) + 1, Nat.succ_lt_succ i.2⟩ (posOnb_of_defNode W μ0 hL hY) τ
  have c1' : ∀ τ, compAt W.θ τ (mt (negSp (G.V (.grid ((i : ℕ) + 1) D.R.m)))
      (negGA (G.V (.grid ((i : ℕ) + 1) D.R.m)) (ptGrid W g ((i : ℕ) + 1)))) =
      W.onb (.grid ((i : ℕ) + 1) D.R.m) τ * (v τ).1.submatrix
        (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) *
        (W.onb (.grid ((i : ℕ) + 1) D.R.m) τ)⁻¹ := fun τ => by
    rw [mt_negGA]; exact c1 τ
  have c2 : ∀ τ, compAt W.θ τ (mt (G.V (.grid (i : ℕ) D.R.m)) (ptGrid W g i)) =
      W.onb (.grid (i : ℕ) D.R.m) τ * (u τ).1.submatrix
        (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)) (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)) *
        (W.onb (.grid (i : ℕ) D.R.m) τ)⁻¹ := fun τ => by
    rw [ptGrid_le W g (Nat.lt_succ_of_lt i.2)]
    exact compAt_kappa_snd g ⟨(i : ℕ), Nat.lt_succ_of_lt i.2⟩ (posOnb_of_defNode W μ0 hL hX) τ
  have key := GlobalTheory.T.weil_compactRealPoint_fockVector_substitution W (.chi i D.R.m) ⟨i.2, le_rfl⟩ (fun _ => 0) (fun _ => (G.V (.grid (i : ℕ) D.R.m)).rank)
    (fun _ => Nat.zero_le _) (fun _ => le_rfl) (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hY ρ).2.2.1) (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hX ρ).1)
    (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hY ρ).2.2.2) (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hX ρ).2.1) _ hf hv
    (fun τ => (v τ).1.submatrix (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)))
    (fun τ => (u τ).1.submatrix (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)) (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)))
    (fun ρ => isKMat_cast _ _ (Or.inr rfl)) (fun ρ => isKMat_cast _ _ (Or.inl rfl))
    (negGA _ (ptGrid W g ((i : ℕ) + 1))) (ptGrid W g i) (GlobalTheory.FockReal.negGA_mem_GinfC _ (ptGrid_mem W g _)) (ptGrid_mem W g _)
    c1' c2 _ hc Q
  have hQ' : Q' = colScal (rowEntries D sc.cGap) i g • fockSubAll (fun _ => 0)
      (fun _ => (G.V (.grid (i : ℕ) D.R.m)).rank)
      (fun τ => (v τ).1.submatrix (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)))
      (fun τ => (u τ).1.submatrix (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)) (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)))
      Q := by
    apply trRow_injective G i
    rw [hQ, map_smul, GlobalTheory.T.fockSubstitution_columnStep_rename_conj G i u v Q]
    rfl
  exact key.trans (by rw [hQ', LinearMap.map_smul])

end GlobalTheory.RowReal
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

theorem adaptedFrame_orthonormal {N r c N' : ℕ} (Γ : Matrix (Fin N) (Fin N) ℂ) (Γ' O : Matrix (Fin r) (Fin r) ℂ)
    (F : Matrix (Fin N) (Fin r) ℂ) (Zc : Matrix (Fin N) (Fin 1) ℂ) (hr : r = c) (hc : c + 1 = N') (hN : N = N')
    (hΓ : Γᴴ = Γ) (h1 : Fᴴ * Γ * F = Γ') (hO : Oᴴ * Γ' * O = 1) (h2 : Fᴴ * Γ * Zc = 0) (h3 : Zcᴴ * Γ * Zc = 1) :
    (Matrix.of (fun a k => Sum.elim (fun b : Fin c => (F * O) a (Fin.cast hr.symm b)) (fun _ : Fin 1 => Zc a 0)
      ((finSumFinEquiv.trans (finCongr hc)).symm (Fin.cast hN k))))ᴴ * Γ *
    Matrix.of (fun a k => Sum.elim (fun b : Fin c => (F * O) a (Fin.cast hr.symm b)) (fun _ : Fin 1 => Zc a 0)
      ((finSumFinEquiv.trans (finCongr hc)).symm (Fin.cast hN k))) = 1 := by
  subst hr hc hN
  set e := finSumFinEquiv (m := r) (n := 1)
  have hT : Matrix.of (fun a k => Sum.elim (fun b : Fin r => (F * O) a (Fin.cast rfl b)) (fun _ : Fin 1 => Zc a 0)
      ((e.trans (finCongr rfl)).symm (Fin.cast rfl k))) = (Matrix.fromCols (F * O) Zc).submatrix id e.symm := by
    ext a k
    simp only [Matrix.of_apply, Fin.cast_eq_self, Matrix.submatrix_apply, id]
    rcases h : e.symm k with b | b
    · simp [h, Matrix.fromCols]
    · simp [h, Matrix.fromCols, Subsingleton.elim b 0]
  have h4 : Zcᴴ * Γ * F = 0 := by
    have := congrArg Matrix.conjTranspose h2
    simpa [Matrix.conjTranspose_mul, hΓ, Matrix.mul_assoc] using this
  have a1 : ((Matrix.fromCols (F * O) Zc).submatrix id e.symm)ᴴ * Γ * (Matrix.fromCols (F * O) Zc).submatrix id e.symm =
      ((Matrix.fromCols (F * O) Zc)ᴴ * Γ * Matrix.fromCols (F * O) Zc).submatrix e.symm e.symm := rfl
  have b1 : (F * O)ᴴ * Γ * (F * O) = 1 := by
    rw [← hO, ← h1]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have b2 : (F * O)ᴴ * Γ * Zc = 0 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ, h2, Matrix.mul_zero]
  have b3 : Zcᴴ * Γ * (F * O) = 0 := by rw [← Matrix.mul_assoc, h4, Matrix.zero_mul]
  rw [hT, a1, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
    b1, b2, b3, h3, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem topFrame_orthonormal {μ0 : T} (hL : L.Is μ0) (W : G.Weil) (τ : D.what₂.Tau) :
    (topFrame W τ)ᴴ * gramAt D (G.V (.top D.R.m)) τ * topFrame W τ = 1 := by
  have hPt : PosOnb W (.top D.R.m) := posOnb_of_defNode W μ0 hL (X := .top D.R.m) le_rfl
  have hPg : PosOnb W (.grid D.R.m D.R.m) := posOnb_of_defNode W μ0 hL (X := .grid D.R.m D.R.m) ⟨le_rfl, rfl⟩
  have hm : ∀ {a b : ℕ} (X : Matrix (Fin (G.V (.top D.R.m)).rank) (Fin a) D.host.E)
      (Z : Matrix (Fin (G.V (.top D.R.m)).rank) (Fin b) D.host.E),
      (X.map (tauE D τ))ᴴ * gramAt D (G.V (.top D.R.m)) τ * Z.map (tauE D τ) =
        (Xᴴ * (G.V (.top D.R.m)).gram * Z).map (tauE D τ) := fun X Z => by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_map _ (GlobalTheory.FockCompare.tauE_star τ)]; rfl
  have hΓ : (gramAt D (G.V (.top D.R.m)) τ)ᴴ = gramAt D (G.V (.top D.R.m)) τ := by
    have hB := hPt τ
    generalize W.onb (.top D.R.m) τ = B at hB
    generalize gramAt D (G.V (.top D.R.m)) τ = Γ at hB
    have hd : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hB
    have h1 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
    have hG : Γ = (B⁻¹)ᴴ * B⁻¹ := by
      calc Γ = (B * B⁻¹)ᴴ * Γ * (B * B⁻¹) := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
        _ = (B⁻¹)ᴴ * (Bᴴ * Γ * B) * B⁻¹ := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [hB, Matrix.mul_one]
    rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  refine adaptedFrame_orthonormal (c := (rowSizes D).nC D.R.m) _ (gramAt D (G.V (.grid D.R.m D.R.m)) τ) _ _ _
    (rank_gridM G (i := D.R.m) le_rfl) (rowSizes D).nC_succ (rank_top G (j := D.R.m) le_rfl) hΓ ?_ (hPg τ) ?_ ?_
  · exact (hm _ _).trans (congrArg (fun M => Matrix.map M (tauE D τ))
      (GlobalTheory.AutFunCounterexample.gram_pull (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) G.sp.topDec.ι G.sp.topDec.isom))
  · refine (hm _ _).trans ((congrArg (fun M => Matrix.map M (tauE D τ)) G.sp.topDec.perp).trans ?_)
    ext i j; simp
  · refine (hm _ _).trans ((congrArg (fun M => Matrix.map M (tauE D τ)) G.sp.topDec.gram).trans ?_)
    ext i j
    obtain rfl := Subsingleton.elim i j
    simp [antiDiagonalSignGramMatrix]

theorem kappaTop_mul_topFrame {μ0 : T} (hL : L.Is μ0) (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (τ : D.what₂.Tau) :
    compAt W.θ τ (mt _ (kappaTop W g)) * topFrame W τ = topFrame W τ *
      (embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) τ).1.submatrix
        (Fin.cast (rank_top G (j := D.R.m) le_rfl)) (Fin.cast (rank_top G (j := D.R.m) le_rfl)) := by
  have hPg : PosOnb W (.grid (Fin.last D.R.m : Fin (D.R.m + 1)) D.R.m) :=
    posOnb_of_defNode W μ0 hL (X := .grid (Fin.last D.R.m : Fin (D.R.m + 1)) D.R.m) ⟨Nat.lt_succ_iff.1 (Fin.last D.R.m).2, rfl⟩
  have hdO : IsUnit (W.onb (.grid D.R.m D.R.m) τ).det := Matrix.isUnit_det_of_left_inverse (hPg τ)
  have h1 : compAt W.θ τ (mt (G.V (.top D.R.m)) (kappaTop W g)) *
      (frameMat (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) G.sp.topDec.ι).map (tauE D τ) =
      (frameMat (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) G.sp.topDec.ι).map (tauE D τ) *
        compAt W.θ τ (mt (G.V (.grid D.R.m D.R.m)) ((kappa W g).2 (Fin.last D.R.m))) := (archM_kappaTop W g τ).1
  have h3 : compAt W.θ τ (mt (G.V (.top D.R.m)) (kappaTop W g)) * G.sp.topDec.a.map (tauE D τ) =
      G.sp.topDec.a.map (tauE D τ) := (archM_kappaTop W g τ).2
  have h2 : compAt W.θ τ (mt (G.V (.grid D.R.m D.R.m)) ((kappa W g).2 (Fin.last D.R.m))) =
      W.onb (.grid D.R.m D.R.m) τ * (g.2 (Fin.last D.R.m) τ).1.submatrix (Fin.cast (rank_gridM G (i := D.R.m) le_rfl))
        (Fin.cast (rank_gridM G (i := D.R.m) le_rfl)) * (W.onb (.grid D.R.m D.R.m) τ)⁻¹ :=
    compAt_kappa_snd g (Fin.last D.R.m) hPg τ
  exact mul_adaptedFrame_of_blocks (c := (rowSizes D).nC D.R.m) _ _ _ _ _
    ((g.2 (Fin.last D.R.m) τ).1 : Matrix (Fin ((rowSizes D).nC D.R.m)) (Fin ((rowSizes D).nC D.R.m)) ℂ)
    (rank_gridM G (i := D.R.m) le_rfl) (rowSizes D).nC_succ (rank_top G (j := D.R.m) le_rfl) hdO h1 h2 h3

theorem exists_unitary_change {a b : ℕ} (h : a = b) {Γ B F : Matrix (Fin a) (Fin a) ℂ} (hB : Bᴴ * Γ * B = 1)
    (hF : Fᴴ * Γ * F = 1) : ∃ c : Matrix.unitaryGroup (Fin b) ℂ, ∀ (A : Matrix (Fin a) (Fin a) ℂ) (v : Matrix.unitaryGroup (Fin b) ℂ),
      A * F = F * v.1.submatrix (Fin.cast h) (Fin.cast h) →
      A = B * (c * v * c⁻¹).1.submatrix (Fin.cast h) (Fin.cast h) * B⁻¹ := by
  subst h
  have hd : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hB
  have hdF : IsUnit F.det := Matrix.isUnit_det_of_left_inverse hF
  have h1 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hu : (B⁻¹ * F)ᴴ * (B⁻¹ * F) = 1 := by
    calc (B⁻¹ * F)ᴴ * (B⁻¹ * F) = (B⁻¹ * F)ᴴ * (Bᴴ * Γ * B) * (B⁻¹ * F) := by rw [hB, Matrix.mul_one]
      _ = Fᴴ * ((B * B⁻¹)ᴴ * Γ * (B * B⁻¹)) * F := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hF]
  have hu' : (B⁻¹ * F) * (B⁻¹ * F)ᴴ = 1 := mul_eq_one_comm.1 hu
  refine ⟨⟨B⁻¹ * F, Matrix.mem_unitaryGroup_iff'.2 hu⟩, fun A v hA => ?_⟩
  have hA' : A * F = F * v.1 := hA
  show A = B * (B⁻¹ * F * v.1 * (B⁻¹ * F)ᴴ) * B⁻¹
  calc A = A * (B * ((B⁻¹ * F) * (B⁻¹ * F)ᴴ) * B⁻¹) := by rw [hu', Matrix.mul_one, h1, Matrix.mul_one]
    _ = A * (B * B⁻¹) * F * (B⁻¹ * F)ᴴ * B⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (B * B⁻¹) * (F * v.1) * (B⁻¹ * F)ᴴ * B⁻¹ := by rw [h1, Matrix.mul_one, Matrix.one_mul, hA']
    _ = _ := by simp only [Matrix.mul_assoc]

theorem exists_ptTop_conj {μ0 : T} (hL : L.Is μ0) (W : G.Weil) (n : Fin (D.R.m + 1)) :
    ∃ c : UG D.what₂.Tau ((rowSizes D).nR n), ∀ (g : Gc D.what₂.Tau (rowSizes D)) τ,
      compAt W.θ τ (mt _ (ptTop W g n)) = W.onb (.top n) τ *
        ((c * rowComp (rowSizes D) g n * c⁻¹) τ).1.submatrix (Fin.cast (rank_top G (Nat.lt_succ_iff.1 n.2)))
          (Fin.cast (rank_top G (Nat.lt_succ_iff.1 n.2))) * (W.onb (.top n) τ)⁻¹ := by
  have hP : PosOnb W (.top n) := posOnb_of_defNode W μ0 hL (X := .top n) (Nat.lt_succ_iff.1 n.2)
  by_cases h : (n : ℕ) = D.R.m
  · obtain rfl : n = Fin.last D.R.m := Fin.ext h
    choose c hc using fun τ => exists_unitary_change (rank_top G (j := D.R.m) le_rfl) (hP τ) (topFrame_orthonormal hL W τ)
    refine ⟨c, fun g τ => ?_⟩
    have hlast : rowComp (rowSizes D) g (Fin.last D.R.m) = embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) := by
      simp only [rowComp, MonoidHom.coe_mk, OneHom.coe_mk]
      exact Fin.snoc_last (α := fun j : Fin ((rowSizes D).m + 1) => UG D.what₂.Tau ((rowSizes D).nR j)) _ _
    rw [show ptTop W g ((Fin.last D.R.m : Fin (D.R.m + 1)) : ℕ) = kappaTop W g from ptTop_m W g]
    erw [hlast]
    exact hc τ _ _ (kappaTop_mul_topFrame hL W g τ)
  · refine ⟨1, fun g τ => ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact eq_conj_of_inFrame (Matrix.isUnit_det_of_left_inverse (hP τ)) (GlobalTheory.T.compactChainTopRowRealPoint_inOrthonormalBasis hL W g n (fun e => absurd e h) τ)

def trColEquiv (G : GridData L sc) (j : Fin D.R.m) :
    PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank ≃ₗ[ℂ] Pol D.what₂.Tau ((rowSizes D).nR j) ((rowSizes D).nR (j + 1)) :=
  LinearEquiv.ofBijective (trCol G j).toLinearMap ⟨trCol_injective G j, MvPolynomial.rename_surjective _ fun y =>
    ⟨(y.1, Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2).symm y.2.1, Fin.cast (rank_top G j.2.le).symm y.2.2), rfl⟩⟩

def trRowEquiv (G : GridData L sc) (i : Fin D.R.m) :
    PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank ≃ₗ[ℂ]
      Pol D.what₂.Tau ((rowSizes D).nC i) ((rowSizes D).nC (i + 1)) :=
  LinearEquiv.ofBijective (trRow G i).toLinearMap ⟨trRow_injective G i, MvPolynomial.rename_surjective _ fun y =>
    ⟨(y.1, Fin.cast (rank_gridM G i.2.le).symm y.2.2, Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2).symm y.2.1), rfl⟩⟩

def subEquiv {ι : Type} [Fintype ι] {a b : ℕ} (x : UG ι a × UG ι b) : Pol ι a b ≃ₗ[ℂ] Pol ι a b :=
  LinearEquiv.ofLinear (linSub (homMat a b x)) (linSub (homMat a b x⁻¹))
    (by rw [← Module.End.mul_eq_comp, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]; rfl)

theorem linSub_homMat_mul {ι : Type} [Fintype ι] {a b : ℕ} (x y : UG ι a × UG ι b) (p : Pol ι a b) :
    linSub (homMat a b x) (linSub (homMat a b y) p) = linSub (homMat a b (x * y)) p := by
  rw [map_mul, map_mul]; rfl

theorem om_fock_top_of_mat {μ0 : T} (hL : L.Is μ0) (W : G.Weil) {U : Set T} (S : GridChoice W U)
    (g : Gc D.what₂.Tau (rowSizes D)) (t : T) (j : Fin D.R.m)
    (u : UG D.what₂.Tau ((rowSizes D).nR j)) (v : UG D.what₂.Tau ((rowSizes D).nR (j + 1)))
    (c1 : ∀ τ, compAt W.θ τ (mt _ (ptTop W g j)) = W.onb (.top (j : ℕ)) τ *
      (u τ).1.submatrix (Fin.cast (rank_top G (j := j) j.2.le)) (Fin.cast (rank_top G (j := j) j.2.le)) *
      (W.onb (.top (j : ℕ)) τ)⁻¹)
    (c2 : ∀ τ, compAt W.θ τ (mt _ (ptTop W g ((j : ℕ) + 1))) = W.onb (.top ((j : ℕ) + 1)) τ *
      (v τ).1.submatrix (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)) (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)) *
      (W.onb (.top ((j : ℕ) + 1)) τ)⁻¹)
    (d : FinDatum G t (.top t j)) (hd : S.Z.HasVec d) (Q Q' : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank)
    (hQ : trCol G j Q' = rowScal (rowEntries D sc.cGap) j g • linSub (homMat _ _ (u, v)) (trCol G j Q)) :
    W.om (.top t j) (G.toPair (.top t j) (ptTop W g j) (ptTop W g (j + 1))) (W.fock (.top t j) (movedVec t S d) Q) =
      W.fock (.top t j) (movedVec t S d) Q' := by
  have hX : DefNode D.R.m (.top (j : ℕ)) := j.2.le
  have hY : DefNode D.R.m (.top ((j : ℕ) + 1)) := j.2
  have hp : DefPair D.R.m (Pair.top t (j : ℕ)) := j.2
  obtain ⟨hf, hv⟩ := GlobalTheory.T.movedVector_definitePair_theta_fockVacuum W S t (.top t j) hp d hd
  have hc := GlobalTheory.T.compactChain_topPair_movedVector_rowCharacter hL W S g t j d hd
  have key := GlobalTheory.T.weil_compactRealPoint_fockVector_substitution W (.top t j) j.2 (fun _ => (G.V (.top (j : ℕ))).rank) (fun _ => (G.V (.top ((j : ℕ) + 1))).rank)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hX ρ).1) (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hY ρ).1)
    (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hX ρ).2.1) (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hY ρ).2.1) _ hf hv
    (fun τ => (u τ).1.submatrix (Fin.cast (rank_top G (j := j) j.2.le)) (Fin.cast (rank_top G (j := j) j.2.le)))
    (fun τ => (v τ).1.submatrix (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)) (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)))
    (fun ρ => isKMat_cast _ _ (Or.inl rfl)) (fun ρ => isKMat_cast _ _ (Or.inl rfl))
    (ptTop W g j) (ptTop W g (j + 1)) (ptTop_mem W g _) (ptTop_mem W g _) c1 c2 _ hc Q
  have hQ' : Q' = rowScal (rowEntries D sc.cGap) j g • fockSubAll (fun _ => (G.V (.top (j : ℕ))).rank)
      (fun _ => (G.V (.top ((j : ℕ) + 1))).rank)
      (fun τ => (u τ).1.submatrix (Fin.cast (rank_top G (j := j) j.2.le)) (Fin.cast (rank_top G (j := j) j.2.le)))
      (fun τ => (v τ).1.submatrix (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)) (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)))
      Q := by
    apply trCol_injective G j
    rw [hQ, map_smul, GlobalTheory.T.fockSubstitution_rowStep_rename_unitary G j u v Q]
  show W.om (.top t j) (ptTop W g j, ptTop W g (j + 1)) _ = _
  rw [key, hQ', LinearMap.map_smul]

theorem exists_fock_transport : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T} (hL : L.Is μ0)
    (W : G.Weil), ∃ (tc : ∀ j : Fin D.R.m, PolF D (G.V (.top ((j : ℕ) + 1))).rank (G.V (.top j)).rank ≃ₗ[ℂ]
        Pol D.what₂.Tau ((rowSizes D).nR (j.castSucc : Fin ((rowSizes D).m + 1))) ((rowSizes D).nR (j.succ : Fin ((rowSizes D).m + 1))))
      (tr : ∀ i : Fin D.R.m, PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid ((i : ℕ) + 1) D.R.m)).rank ≃ₗ[ℂ]
        Pol D.what₂.Tau ((rowSizes D).nC (i.castSucc : Fin ((rowSizes D).m + 1))) ((rowSizes D).nC (i.succ : Fin ((rowSizes D).m + 1)))),
      ∀ {U : Set T} (S : GridChoice W U) (g : Gc D.what₂.Tau (rowSizes D)) (t : T),
        (∀ (j : Fin D.R.m) (d : FinDatum G t (.top t j)), S.Z.HasVec d → ∀ Q,
          W.om (.top t j) (G.toPair (.top t j) (ptTop W g j) (ptTop W g (j + 1))) (W.fock (.top t j) (movedVec t S d) Q) =
            W.fock (.top t j) (movedVec t S d) ((tc j).symm (rowFock (rowEntries D sc.cGap) j g (tc j Q)))) ∧
        (∀ (i : Fin D.R.m) (d : FinDatum G t (.chi i D.R.m)), S.Z.HasVec d → ∀ Q,
          W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (ptGrid W g i) (ptGrid W g (i + 1)))
              (W.fock (.chi i D.R.m) (movedVec t S d) Q) =
            W.fock (.chi i D.R.m) (movedVec t S d) ((tr i).symm (colFock (rowEntries D sc.cGap) i g (tr i Q)))) := by
  intro D T L sc G μ0 hL W
  choose c hc using exists_ptTop_conj hL W
  refine ⟨fun j => (trColEquiv G j).trans (subEquiv (c j.castSucc, c j.succ)).symm, fun i => trRowEquiv G i,
    fun S g t => ⟨fun j d hd Q => ?_, fun i d hd Q => ?_⟩⟩
  · refine om_fock_top_of_mat hL W S g t j _ _ (hc j.castSucc g) (hc j.succ g) d hd Q _ ?_
    have e : ∀ y, trCol G j ((trColEquiv G j).symm y) = y := fun y => (trColEquiv G j).apply_symm_apply y
    refine (e _).trans ?_
    show linSub (homMat _ _ (c j.castSucc, c j.succ)) (rowScal (rowEntries D sc.cGap) j g •
      linSub (homMat _ _ (rowComp (rowSizes D) g j.castSucc, rowComp (rowSizes D) g j.succ))
        (linSub (homMat _ _ (c j.castSucc, c j.succ)⁻¹) (trCol G j Q))) = _
    rw [LinearMap.map_smul, linSub_homMat_mul, linSub_homMat_mul]
    rfl
  · exact om_fock_chi hL W S g t i d hd Q _ ((trRowEquiv G i).apply_symm_apply _)

end GlobalTheory.RowReal
end
end
