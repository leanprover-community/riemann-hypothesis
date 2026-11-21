import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridRowZeroBasePointCarriesLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SuppTwoOfOffTypeData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthAtSumLatO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualCOfGramOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegLineLatticeAndBesselCoreLatticeSelfDualSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridRowMovedLatticeSplitsBesselLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiVertexLatticeSplitsAlongWittAtPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbeddingColumnLatticeIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrimAtOfMonoId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSquareFittedIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiPrimitiveStandardFramesFourierJacobiLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeColumnsOffFiniteSet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StaircaseLatticeIsotropicLineIdealIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanSingletonMulIdealCompletionIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAdjYZeroMulVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridStandardVacuumScalarEqProdLocalPlaces

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl

noncomputable section
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseTiltMove

variable {D : D7}

theorem incA_inj : Function.Injective (incA D) := by
  haveI : Nontrivial (AF D.host.F) :=
    (NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers D.host.F) D.host.F).nontrivial
  exact Algebra.TensorProduct.includeRight_injective (algebraMap D.host.F (AF D.host.F)).injective

theorem incA_apply (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

theorem mulVec_latV_of_rat (S : HSp D) (γ : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (L M : Lat S)
    (hLM : ∀ x ∈ L, γ *ᵥ x ∈ M) (P : Pl D → Prop) (y : Fin S.rank → AE D) (hy : y ∈ latV S L P) :
    γ.map (incA D) *ᵥ y ∈ latV S M P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, hαP, a, ha, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at ha
    subst ha
    refine AddSubgroup.subset_closure ⟨α, hα, hαP, 1, rfl, γ *ᵥ x, hLM x hx, ?_⟩
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, incA_apply, one_mul, Algebra.TensorProduct.tmul_mul_tmul,
      ← TensorProduct.tmul_sum]
  | zero => simp only [Matrix.mulVec_zero]; exact (latV S M P).zero_mem
  | add u v _ _ hu hv => rw [Matrix.mulVec_add]; exact (latV S M P).add_mem hu hv
  | neg u _ hu => rw [Matrix.mulVec_neg]; exact (latV S M P).neg_mem hu

theorem exists_rat_of_GQ (S : HSp D) (δ : GA D S) (h : δ ∈ GQ S) :
    ∃ γ : GL (Fin S.rank) D.host.E, mt S δ = γ.val.map (incA D) ∧ mt S δ⁻¹ = (γ⁻¹).val.map (incA D) := by
  obtain ⟨γ, -, hγ⟩ := h
  have e : matHom S δ = Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γ := hγ.symm
  refine ⟨γ, ?_, ?_⟩
  · show (matHom S δ).val = _
    rw [e]; rfl
  · show (matHom S δ⁻¹).val = _
    rw [map_inv, e, ← map_inv]; rfl

theorem moves_of_rat (S : HSp D) (δ : GA D S) (γ γ' : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (h : mt S δ = γ.map (incA D)) (h' : mt S δ⁻¹ = γ'.map (incA D)) (L M : Lat S)
    (hLM : ∀ x ∈ L, γ *ᵥ x ∈ M) (hML : ∀ x ∈ M, γ' *ᵥ x ∈ L) (P : Pl D → Prop) : Moves S δ L M P := by
  intro y _
  refine ⟨fun hy => h ▸ mulVec_latV_of_rat S γ L M hLM P y hy, fun hy => ?_⟩
  have e : mt S δ⁻¹ *ᵥ (mt S δ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, ← GlobalTheory.FinPl.PlacesAdeles.mt_mul, inv_mul_cancel, GlobalTheory.FinPl.PlacesAdeles.mt_one,
      Matrix.one_mulVec]
  rw [← e, h']
  exact mulVec_latV_of_rat S γ' M L hML P _ hy

theorem moves_of_isFinOf (S : HSp D) {δ b : GA D S} (hb : IsFinOf δ b) (L M : Lat S)
    (h : Moves S δ L M (fun _ => True)) : Moves S b L M (fun _ => True) := by
  obtain ⟨-, a, ha, hab⟩ := hb
  have hb' : b = a⁻¹ * δ := by rw [← hab, inv_mul_cancel_left]
  intro y hy
  have hy' := GlobalTheory.FinPl.PlacesAdeles.supp_mulVec S _ δ hy
  rw [hb', GlobalTheory.FinPl.PlacesAdeles.mt_mul, ← Matrix.mulVec_mulVec,
    GlobalTheory.FinPl.PlacesAdeles.mulVec_off (GlobalTheory.FinPl.SuppTwoAsm.ginf_le_grpOff S _ (inv_mem ha)) hy']
  exact h y hy

theorem moves_one (S : HSp D) (L : Lat S) (P : Pl D → Prop) : Moves S 1 L L P := by
  intro y _
  rw [GlobalTheory.FinPl.PlacesAdeles.mt_one, Matrix.one_mulVec]

theorem sumLat_mulVec {n k c : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (M₀ : Matrix (Fin n) (Fin k) D.host.E)
    (Λ : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (a : Matrix (Fin n) (Fin c) D.host.E)
    (𝔟 𝔟' : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (t : Fin c → D.host.E) (hM : γ * M₀ = M₀)
    (ha : γ * a = a * diagonal t) (ht : ∀ p, ∀ u ∈ 𝔟 p, t p * u ∈ 𝔟' p) :
    ∀ x ∈ sumLat M₀ Λ a 𝔟, γ *ᵥ x ∈ sumLat M₀ Λ a 𝔟' := by
  rintro _ ⟨y, hy, u, hu, rfl⟩
  refine ⟨y, hy, fun p => t p * u p, fun p => ht p _ (hu p), ?_⟩
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hM, Matrix.mulVec_mulVec, ha, ← Matrix.mulVec_mulVec]
  congr 2
  funext p
  exact Matrix.mulVec_diagonal _ _ _

section Grid

variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem lat_grid (j : ℕ) (h1 : 1 ≤ j) (h : j < D.R.m) :
    G.Λ (.grid D.R.m j) = (G.rowDec j h).lat (G.Λ (.top j)) (stairId D.host.AA D.host.AAbar (D.R.m - 1 - j)) := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  exact G.sp.rowLat j' h

variable {G}

theorem tilt_cols {j : ℕ} (hj : j < D.R.m) (hodd : Odd j) {δ : GA D (G.V (.grid D.R.m j))} (hδ : IsTilt G j δ)
    (γ : Matrix (Fin (G.V (.grid D.R.m j)).rank) (Fin (G.V (.grid D.R.m j)).rank) D.host.E)
    (hγ : mt _ δ = γ.map (incA D)) :
    γ * frameMat _ _ (G.rowDec j hj).ι = frameMat _ _ (G.rowDec j hj).ι ∧
      γ * (G.rowDec j hj).a = (G.rowDec j hj).a * diagonal (GlobalTheory.RowShape.tiltSc D j) := by
  obtain ⟨σ, hσ⟩ : ∃ σ, D.R.m - 1 - j = 2 * σ := by
    obtain ⟨a, ha⟩ := D.R.m_even; obtain ⟨b, hb⟩ := hodd; exact ⟨(D.R.m - 1 - j) / 2, by omega⟩
  obtain ⟨h0, he, he'⟩ := hδ.2.2 σ hj hσ
  rw [hγ, ← Matrix.map_mul] at h0 he he'
  have h0 := Matrix.map_injective incA_inj h0
  have he := Matrix.map_injective incA_inj he
  have he' := Matrix.map_injective incA_inj he'
  refine ⟨h0, Matrix.ext fun k p => ?_⟩
  rw [Matrix.mul_diagonal]
  by_cases hp : 2 * p.1 < D.R.m - 1 - j
  · have := congrFun (congrFun he k) ⟨p.1, by omega⟩
    simp only [Matrix.mul_diagonal] at this
    have e1 : (γ * (rowJac G j hj σ hσ).e) k ⟨p.1, by omega⟩ = (γ * (G.rowDec j hj).a) k p := rfl
    have e2 : (rowJac G j hj σ hσ).e k ⟨p.1, by omega⟩ = (G.rowDec j hj).a k p := rfl
    rw [← e1, this, e2]
    simp [GlobalTheory.RowShape.tiltSc, hodd, hp]
  · have := congrFun (congrFun he' k) ⟨D.R.m - 1 - j - 1 - p.1, by omega⟩
    simp only [Matrix.mul_diagonal] at this
    have hq : (Fin.castLE (by omega : σ ≤ D.R.m - 1 - j) (⟨D.R.m - 1 - j - 1 - p.1, by omega⟩ : Fin σ)).rev = p :=
      Fin.ext (by simp only [Fin.val_rev, Fin.val_castLE]; omega)
    have e1 : (γ * (rowJac G j hj σ hσ).e') k ⟨D.R.m - 1 - j - 1 - p.1, by omega⟩ = (γ * (G.rowDec j hj).a) k p := by
      simp only [Matrix.mul_apply, GlobalTheory.RowUnf.rowJac, GlobalTheory.RowUnf.jacDec, Matrix.submatrix_apply, id_eq, hq]
    have e2 : (rowJac G j hj σ hσ).e' k ⟨D.R.m - 1 - j - 1 - p.1, by omega⟩ = (G.rowDec j hj).a k p := by
      simp only [GlobalTheory.RowUnf.rowJac, GlobalTheory.RowUnf.jacDec, Matrix.submatrix_apply, id_eq, hq]
    rw [← e1, this, e2]
    simp [GlobalTheory.RowShape.tiltSc, hodd, hp]

end Grid

section Main

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem tiltSc_ne_zero (j : ℕ) (p : Fin (D.R.m - 1 - j)) : GlobalTheory.RowShape.tiltSc D j p ≠ 0 := by
  unfold GlobalTheory.RowShape.tiltSc
  split_ifs
  · exact inv_ne_zero (pow_ne_zero _ cmHost_imaginaryGenerator_ne_zero)
  · exact star_ne_zero.2 (pow_ne_zero _ cmHost_imaginaryGenerator_ne_zero)
  · exact one_ne_zero

theorem moves_idx (t : T) (B : Frames G) (b : Pts G) (hb : IsBase t B b) (j : ℕ) (hj : j ∈ idx D) :
    Moves _ (b j) (G.Λ (.grid D.R.m j)) (GlobalTheory.RowShape.rowN G j) fun _ => True := by
  have hj' : 1 ≤ j ∧ j < 1 + (D.R.m - 2) := List.mem_range'_1.1 hj
  have hjm : j < D.R.m := by omega
  obtain ⟨δ, hδ, hfin⟩ := hb.2.1 j hj
  refine moves_of_isFinOf _ hfin _ _ ?_
  have hN : GlobalTheory.RowShape.rowN G j = (G.rowDec j hjm).lat (G.Λ (.top j)) (GlobalTheory.RowShape.rowId D j) := by
    unfold GlobalTheory.RowShape.rowN; rw [dif_pos hjm]
  rw [lat_grid G j hj'.1 hjm, hN]
  by_cases hodd : Odd j
  · obtain ⟨γ, hγ, hγ'⟩ := exists_rat_of_GQ _ δ hδ.1
    obtain ⟨h0, ha⟩ := tilt_cols hjm hodd hδ γ.val hγ
    set t := GlobalTheory.RowShape.tiltSc D j
    have hinv : (γ⁻¹).val * γ.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h0' : (γ⁻¹).val * frameMat _ _ (G.rowDec j hjm).ι = frameMat _ _ (G.rowDec j hjm).ι := by
      conv_lhs => rw [← h0]
      rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
    have hdd : diagonal t * diagonal (fun p => (t p)⁻¹) = 1 := by
      rw [Matrix.diagonal_mul_diagonal,
        show (fun p => t p * (t p)⁻¹) = fun _ => (1 : D.host.E) from funext fun p => mul_inv_cancel₀ (tiltSc_ne_zero j p)]
      exact Matrix.diagonal_one
    have ha' : (γ⁻¹).val * (G.rowDec j hjm).a = (G.rowDec j hjm).a * diagonal (fun p => (t p)⁻¹) := by
      calc (γ⁻¹).val * (G.rowDec j hjm).a
          = (γ⁻¹).val * ((G.rowDec j hjm).a * (diagonal t * diagonal (fun p => (t p)⁻¹))) := by
            rw [hdd, Matrix.mul_one]
        _ = (γ⁻¹).val * (γ.val * (G.rowDec j hjm).a) * diagonal (fun p => (t p)⁻¹) := by
            simp only [ha, Matrix.mul_assoc]
        _ = _ := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
    refine moves_of_rat _ δ γ.val (γ⁻¹).val hγ hγ' _ _ ?_ ?_ _
    · refine sumLat_mulVec _ _ _ _ _ _ t h0 ha fun p u hu => ?_
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hu
    · refine sumLat_mulVec _ _ _ _ _ _ (fun p => (t p)⁻¹) h0' ha' fun p u hu => ?_
      obtain ⟨z, hz, rfl⟩ := (FractionalIdeal.mem_singleton_mul).1 hu
      rw [← mul_assoc, inv_mul_cancel₀ (tiltSc_ne_zero j p), one_mul]
      exact hz
  · have h1 : δ = 1 := hδ.2.1 (Nat.not_odd_iff_even.1 hodd)
    subst h1
    have hI : GlobalTheory.RowShape.rowId D j = stairId D.host.AA D.host.AAbar (D.R.m - 1 - j) := by
      funext p
      simp [GlobalTheory.RowShape.rowId, GlobalTheory.RowShape.tiltSc, hodd]
    rw [hI]
    exact moves_one _ _ _

theorem moves_rowN (t : T) (B : Frames G) (b : Pts G) (hb : IsBase t B b) (j : ℕ) (h1 : 1 ≤ j) (hm : j ≤ D.R.m) :
    Moves _ (b j) (G.Λ (.grid D.R.m j)) (GlobalTheory.RowShape.rowN G j) fun _ => True := by
  by_cases hj : j ∈ idx D
  · exact moves_idx t B b hb j hj
  rw [hb.2.2 j (by omega) hj]
  by_cases hjm : j < D.R.m
  · have hc : D.R.m - 1 - j = 0 := by
      have : ¬ (1 ≤ j ∧ j < 1 + (D.R.m - 2)) := fun h => hj (List.mem_range'_1.2 h)
      omega
    have hN : GlobalTheory.RowShape.rowN G j = G.Λ (.grid D.R.m j) := by
      unfold GlobalTheory.RowShape.rowN
      rw [dif_pos hjm, lat_grid G j h1 hjm]
      congr 1
      funext p
      exact absurd p.2 (by omega)
    rw [hN]
    exact moves_one _ _ _
  · have hN : GlobalTheory.RowShape.rowN G j = G.Λ (.grid D.R.m j) := by
      unfold GlobalTheory.RowShape.rowN; rw [dif_neg hjm]
    rw [hN]
    exact moves_one _ _ _

end Main

theorem base_moves_rowN : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ (t : T) (b : Pts ch.G), IsBase t ch.S.B b → ∀ j, 1 ≤ j → j ≤ D.R.m → GlobalTheory.FinPl.Moves _ (b j) (ch.G.Λ (.grid D.R.m j)) (GlobalTheory.RowShape.rowN ch.G j) fun _ => True := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ t b hb j h1 hm
  exact moves_rowN t ch.S.B b hb j h1 hm

end GlobalTheory.BaseTiltMove
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_base_point_moves_row_lattices : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ (t : T) (b : Pts ch.G), IsBase t ch.S.B b → ∀ j, 1 ≤ j → j ≤ D.R.m → GlobalTheory.FinPl.Moves _ (b j) (ch.G.Λ (.grid D.R.m j)) (GlobalTheory.RowShape.rowN ch.G j) fun _ => True := by
  atlas_forward_decl GlobalTheory.BaseTiltMove.base_moves_rowN
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowShape

variable {D : D7}

theorem pLine_gram_eq_one : (pLine D).gram = 1 := by
  rw [pLine_gram]
  ext i j
  fin_cases i; fin_cases j
  simp [antiDiagonalSignGramMatrix]
  rfl

theorem mem_topL_iff (z : Fin (pLine D).rank → D.host.E) : z ∈ topL D ↔ z ∈ GlobalTheory.AdForm.intVec D (pLine D).rank := by
  simp only [topL, latPi, Submodule.mem_pi, Set.mem_univ, true_implies, FractionalIdeal.coe_one, Submodule.mem_one]
  show _ ↔ ∀ k, IsIntegral ℤ (z k)
  refine forall_congr' fun k => ⟨?_, fun h => ⟨⟨z k, h⟩, rfl⟩⟩
  rintro ⟨b, hb⟩
  rw [← hb]
  exact b.2

theorem isSelfDualC_topL : IsSelfDualC (pLine D) (topL D) :=
  GlobalTheory.LocMod.IntFrameStd.isSelfDualC_of_gram_one pLine_gram_eq_one _ mem_topL_iff

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem topLat_eq_sumLatO (G : GridData L sc) :
    G.Λ (.top D.R.m) = GlobalTheory.Core.Rk.SumBox.sumLatO (topOrth G) (G.Λ (.grid D.R.m D.R.m)) (topL D) := by
  have e : G.Λ (.top D.R.m) = G.sp.topDec.lat (G.Λ (.grid D.R.m D.R.m)) (fun _ => 1) := G.sp.topLat
  rw [e]
  ext x
  rw [GlobalTheory.Core.Rk.SumBox.mem_sumLatO]
  constructor
  · rintro ⟨y, hy, u, hu, rfl⟩
    exact ⟨y, hy, u, Submodule.mem_pi.2 fun p _ => hu p, rfl⟩
  · rintro ⟨y, hy, u, hu, rfl⟩
    exact ⟨y, hy, u, fun p => Submodule.mem_pi.1 hu p (Set.mem_univ _), rfl⟩

theorem topLat_orthAt (G : GridData L sc) (v : Pl D) :
    OrthAt (topOrth G) (G.Λ (.top D.R.m)) (G.Λ (.grid D.R.m D.R.m)) (topL D) v := by
  rw [topLat_eq_sumLatO G]
  exact GlobalTheory.Core.Rk.SumSplit.orthAt_sumLatO D _ _ _ (topOrth G) _ _ v

theorem topL_selfDual_orthAt : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => IsSelfDualC _ (GlobalTheory.RowShape.topL D) ∧
    ∀ v, GlobalTheory.FinPl.OrthAt (topOrth ch.G) (ch.G.Λ (.top D.R.m)) (ch.G.Λ (.grid D.R.m D.R.m)) (GlobalTheory.RowShape.topL D) v :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ =>
    ⟨isSelfDualC_topL, fun v => topLat_orthAt ch.G v⟩⟩⟩

end GlobalTheory.RowShape
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.posNormLine_selfDual_and_topLattice_splits : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => IsSelfDualC _ (GlobalTheory.RowShape.topL D) ∧
    ∀ v, GlobalTheory.FinPl.OrthAt (topOrth ch.G) (ch.G.Λ (.top D.R.m)) (ch.G.Λ (.grid D.R.m D.R.m)) (GlobalTheory.RowShape.topL D) v := by
  atlas_forward_decl GlobalTheory.RowShape.topL_selfDual_orthAt
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negLineLattice_and_besselCoreLattice_selfDual_split : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ, j + 2 * σ + 2 = D.R.m → IsSelfDualC _ (GlobalTheory.RowShape.lineL D j) ∧
    IsSelfDualC _ (GlobalTheory.RowShape.coreL ch.G j) ∧ ∀ v, GlobalTheory.FinPl.OrthAt (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (GlobalTheory.RowShape.coreL ch.G j) (ch.G.Λ (.top j)) (GlobalTheory.RowShape.lineL D j) v := by
  first | exact @GlobalTheory.RowShape.coreL_selfDual_split | exact GlobalTheory.RowShape.coreL_selfDual_split | (intros; apply GlobalTheory.RowShape.coreL_selfDual_split <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

open GlobalTheory.AscFin GlobalTheory.AscFin.MonoJac GlobalTheory.RowShape
open GlobalTheory.SeeSaw.SplitLat (colProj)
open scoped nonZeroDivisors

namespace GlobalTheory.RowShape.MonoRow

variable {D : D7}

def cfR (c : ℕ) {ρ : ℕ} (r : Fin ρ → D.host.E) : Matrix (Fin ρ) (Fin c) D.host.E :=
  fun p q => if p.1 = q.1 then (r p)⁻¹ else 0

theorem cols_mul_coeff_eq_reflected_sum {n c ρ : ℕ} (a : Matrix (Fin n) (Fin c) D.host.E) (hc : c = 2 * ρ) (h : ρ ≤ c) (r s : Fin ρ → D.host.E)
    (hr : ∀ p, r p ≠ 0) (hs : ∀ p, s p ≠ 0) :
    a = (colsOf a (Fin.castLE h) r : Matrix (Fin n) (Fin ρ) D.host.E) * (cfR c r : Matrix (Fin ρ) (Fin c) D.host.E) +
      (colsOf a (fun p : Fin ρ => (Fin.castLE h p : Fin c).rev) s : Matrix (Fin n) (Fin ρ) D.host.E) *
        (cfE' c s : Matrix (Fin ρ) (Fin c) D.host.E) := by
  refine Matrix.ext fun k q => ?_
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [colsOf, cfR, cfE']
  by_cases hq : q.1 < ρ
  · rw [Finset.sum_eq_single ⟨q.1, hq⟩, Finset.sum_eq_zero]
    · rw [if_pos rfl, add_zero, show (Fin.castLE h ⟨q.1, hq⟩ : Fin c) = q from Fin.ext rfl, mul_comm,
        ← mul_assoc, inv_mul_cancel₀ (hr _), one_mul]
    · intro p _
      rw [if_neg (by omega), mul_zero]
    · intro p _ hp
      rw [if_neg (fun e => hp (Fin.ext e)), mul_zero]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  · have hp' : c - 1 - q.1 < ρ := by have := q.2; omega
    rw [Finset.sum_eq_zero, Finset.sum_eq_single ⟨c - 1 - q.1, hp'⟩]
    · rw [if_pos (by have := q.2; simp only [Fin.val_mk]; omega), zero_add,
        show ((Fin.castLE h ⟨c - 1 - q.1, hp'⟩ : Fin c).rev) = q from Fin.ext (by simp [Fin.val_rev]; omega),
        mul_comm, ← mul_assoc, inv_mul_cancel₀ (hs _), one_mul]
    · intro p _ hp
      rw [if_neg (fun e => hp (Fin.ext (show p.1 = c - 1 - q.1 by omega))), mul_zero]
    · intro hn; exact absurd (Finset.mem_univ _) hn
    · intro p _
      rw [if_neg (by have := p.2; omega), mul_zero]

theorem mono_at_lattice_of_column_frames {A B : HSp D} {c ρ : ℕ} {ε : D.host.E} (t : HermitianOrthogonalExtensionData A B c ε) (d : HypDec B A ρ) (hc : c = 2 * ρ)
    (hρ : ρ ≤ c) (r s : Fin ρ → D.host.E) (hr : ∀ p, r p ≠ 0) (hs : ∀ p, s p ≠ 0)
    (he : d.e = colsOf t.a (Fin.castLE hρ) r) (he' : d.e' = colsOf t.a (fun p : Fin ρ => (Fin.castLE hρ p : Fin c).rev) s)
    (hi : d.i₀ = frameMat B A t.ι) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : GlobalTheory.FinPl.Pl D) : GlobalTheory.FinPl.MonoAt d (t.lat Λ 𝔟) Λ v := by
  have ha := cols_mul_coeff_eq_reflected_sum t.a hc hρ r s hr hs
  rw [← he, ← he'] at ha
  have hX : d.qX * t.a = cfR c r := by
    rw [ha, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.SeeSaw.SplitLat.qX_e, GlobalTheory.SeeSaw.SplitLat.qX_e',
      Matrix.one_mul, Matrix.zero_mul, add_zero]
  have hY : d.qY * t.a = cfE' c s := by
    rw [ha, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.SeeSaw.SplitLat.qY_e, GlobalTheory.SeeSaw.SplitLat.qY_e',
      Matrix.one_mul, Matrix.zero_mul, zero_add]
  have h0 : d.q0 * t.a = 0 := by
    rw [ha, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.SeeSaw.SplitLat.wittDecomposition_coreProj_mul_e_eq_zero, GlobalTheory.SeeSaw.SplitLat.wittZeroProjection_mul_dualBasis_eq_zero,
      Matrix.zero_mul, Matrix.zero_mul, add_zero]
  refine monoAt_of_proj d _ _ (fun i => ?_) (fun i => ?_) ?_ ?_ v
  · refine sumLat_map _ (Pi.single (Fin.castLE hρ i) 1) ?_ ?_ ?_
    · rw [colProj_mul, ← hi, GlobalTheory.SeeSaw.SplitLat.qX_i₀, colProj_zero]
    · rw [colProj_mul, hX]
      refine Matrix.ext fun k q => ?_
      rw [Matrix.mul_diagonal, he]
      simp only [colProj, Matrix.of_apply, colsOf, cfR]
      by_cases hq : i.1 = q.1
      · have e : (Fin.castLE hρ i : Fin c) = q := Fin.ext hq
        subst e
        rw [if_pos hq, Pi.single_eq_same, mul_one, mul_comm (r i), mul_assoc, mul_inv_cancel₀ (hr _), mul_one]
      · have e : q ≠ (Fin.castLE hρ i : Fin c) := fun e => hq (by rw [e]; rfl)
        rw [if_neg hq, mul_zero, Pi.single_apply, if_neg e, mul_zero]
    · intro p
      rw [Pi.single_apply]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
  · refine sumLat_map _ (Pi.single (Fin.castLE hρ i : Fin c).rev 1) ?_ ?_ ?_
    · rw [colProj_mul, ← hi, GlobalTheory.SeeSaw.SplitLat.qY_i₀, colProj_zero]
    · rw [colProj_mul, hY]
      refine Matrix.ext fun k q => ?_
      rw [Matrix.mul_diagonal, he']
      simp only [colProj, Matrix.of_apply, colsOf, cfE']
      by_cases hq : q.1 + i.1 + 1 = c
      · have e : (Fin.castLE hρ i : Fin c).rev = q := Fin.ext (by simp [Fin.val_rev]; omega)
        subst e
        rw [if_pos hq, Pi.single_eq_same, mul_one, mul_comm (s i), mul_assoc, mul_inv_cancel₀ (hs _), mul_one]
      · have e : q ≠ (Fin.castLE hρ i : Fin c).rev := fun e => hq (by rw [e]; simp [Fin.val_rev]; omega)
        rw [if_neg hq, mul_zero, Pi.single_apply, if_neg e, mul_zero]
    · intro p
      rw [Pi.single_apply]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
  · exact sumLat_proj d.q0 (by rw [← hi]; exact GlobalTheory.SeeSaw.SplitLat.wittDecomposition_coreProj_mul_core_eq_one d) h0
  · intro x hx
    rw [hi]
    exact mem_sumLat_of hx

theorem monoAt_jacDec {A B : HSp D} {c σ : ℕ} {ε : D.host.E} (t : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (v : GlobalTheory.FinPl.Pl D) : GlobalTheory.FinPl.MonoAt (GlobalTheory.RowUnf.jacDec t h) (t.lat Λ 𝔟) Λ v := by
  have hρ : σ ≤ c := by omega
  refine mono_at_lattice_of_column_frames t _ h hρ 1 1 (fun _ => one_ne_zero) (fun _ => one_ne_zero) ?_ ?_ rfl Λ 𝔟 v
  · refine Matrix.ext fun k p => ?_
    simp only [colsOf, Pi.one_apply, one_mul]
    rfl
  · refine Matrix.ext fun k p => ?_
    simp only [colsOf, Pi.one_apply, one_mul]
    rfl

end GlobalTheory.RowShape.MonoRow

theorem GlobalTheory.RowShape.rowN_monoAt : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ n (hn : n < D.R.m) σ
    (h : D.R.m - 1 - n = 2 * σ) v, GlobalTheory.FinPl.MonoAt (rowJac ch.G n hn σ h) (GlobalTheory.RowShape.rowN ch.G n) (ch.G.Λ (.top n)) v := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ => ?_⟩⟩
  intro n hn σ h v
  rw [GlobalTheory.RowShape.rowN, dif_pos hn]
  exact GlobalTheory.RowShape.MonoRow.monoAt_jacDec _ h _ _ v

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridRowMovedLattice_splits_jacobi_largeDepth : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ n (hn : n < D.R.m) σ (h : D.R.m - 1 - n = 2 * σ) v, GlobalTheory.FinPl.MonoAt (rowJac ch.G n hn σ h) (GlobalTheory.RowShape.rowN ch.G n) (ch.G.Λ (.top n)) v := by
  atlas_forward_decl GlobalTheory.RowShape.rowN_monoAt
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowShape

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem colMul_besDecAt (G : GridData L sc) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (hjm : j < D.R.m) (i : Fin σ)
    (t : AE D) : colMul (besDecAt G j σ hj).jX i t = fun k => (incA D (D.host.xi0 ^ (i : ℕ)) * t) *
      incA D ((G.rowDec j hjm).a k (Fin.castLE (by omega) i)) := by
  funext k
  simp only [colMul, HypDec.jX, rat, Matrix.map_apply, besDecAt, diagDec, rowBes, besDec, HermitianOrthogonalExtensionData.iso,
    Matrix.mul_diagonal, Matrix.submatrix_apply, lam, id, map_mul]
  ring

theorem rowId_even {j : ℕ} (hj : ¬ Odd j) (p : Fin (D.R.m - 1 - j)) :
    rowId D j p = stairId D.host.AA D.host.AAbar (D.R.m - 1 - j) p := by
  rw [rowId, tiltSc, if_neg hj, FractionalIdeal.spanSingleton_one, one_mul]

theorem stairId_ne_zero (c : ℕ) (p : Fin c) : stairId D.host.AA D.host.AAbar c p ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (GlobalTheory.CuspCharLattice.host_AA_ne_zero _))
    (inv_ne_zero (pow_ne_zero _ (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D)))

theorem primAt_rowN {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (G : GridData L sc) (j σ : ℕ)
    (hj : j + 2 * σ + 2 = D.R.m) (v : Pl D) : PrimAt ψ (besDecAt G j σ hj) (rowN G j) v := by
  have hjm : j < D.R.m := by omega
  have hodd : ¬ Odd j := by
    obtain ⟨a, ha⟩ := D.R.m_even
    rintro ⟨b, hb⟩
    omega
  obtain ⟨-, f2, f3, -, f5, -, -⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.LocFrame.cmHost_imaginaryGenerator_ne_zero

  set I : Fin σ → FI D := fun i => FractionalIdeal.spanSingleton _ (D.host.xi0 ^ (i : ℕ))⁻¹ *
    stairId D.host.AA D.host.AAbar (D.R.m - 1 - j) (Fin.castLE (by omega) i) with hIdef
  have hI0 : ∀ i, I i ≠ 0 := fun i => mul_ne_zero
    ((FractionalIdeal.spanSingleton_ne_zero_iff).2 (inv_ne_zero (pow_ne_zero _ hξ))) (stairId_ne_zero _ _)
  have sub : ∀ (𝔞 : FI D) a, a ∈ idV 𝔞 v → a ∈ idAt D (· = v) := fun 𝔞 a ha => by
    have := (f3 𝔞 1 one_ne_zero a).1 (by rwa [FractionalIdeal.spanSingleton_one, one_mul])
    exact this.2
  have line : ∀ i (t : AE D), t ∈ idAt D (· = v) →
      (colMul (besDecAt G j σ hj).jX i t ∈ latV _ (rowN G j) (· = v) ↔ t ∈ idV (I i) v) := by
    intro i t ht
    rw [colMul_besDecAt G j σ hj hjm, rowN, dif_pos hjm,
      (GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff (G.rowDec j hjm) (neg_ne_zero.2 one_ne_zero) _ _ _ v _).1, rowId_even hodd,
      hIdef, f3 _ _ (inv_ne_zero (pow_ne_zero _ hξ)), inv_inv]
    exact ⟨fun h => ⟨h, ht⟩, fun h => h.1⟩
  intro i i' hii s hs
  have key : (∀ a : AE D, colMul (besDecAt G j σ hj).jX i' a ∈ latV _ (rowN G j) (· = v) →
      colMul (besDecAt G j σ hj).jX i (s * a) ∈ latV _ (rowN G j) (· = v)) ↔
      ∀ a ∈ idV (I i') v, s * a ∈ idV (I i) v := by
    constructor
    · intro h a ha
      have haA := sub _ a ha
      exact (line i (s * a) (Ideal.mul_mem_left _ _ haA)).1 (h a ((line i' a haA).2 ha))
    · intro h a hc
      have haA := GlobalTheory.SeeSaw.PrimSplit.idAt_of_colMul _ hc
      exact (line i (s * a) (Ideal.mul_mem_left _ _ haA)).2 (h a ((line i' a haA).1 hc))
  have hratio : I i * (I i')⁻¹ = dI D := by
    have hst := stairId_succ (𝔞 := D.host.AA) (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) (Fin.castLE (by omega) i : Fin (D.R.m - 1 - j))
      (Fin.castLE (by omega) i') (by simp only [Fin.val_castLE]; exact hii)
    have e : I i = dI D * I i' := by
      simp only [hIdef, dI, hst, hii]
      have e2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (D.host.xi0 ^ (i : ℕ))⁻¹ =
          FractionalIdeal.spanSingleton _ D.host.xi0 * FractionalIdeal.spanSingleton _ (D.host.xi0 ^ ((i : ℕ) + 1))⁻¹ := by
        rw [FractionalIdeal.spanSingleton_mul_spanSingleton]
        congr 1
        rw [pow_succ, mul_inv, mul_comm (D.host.xi0 ^ (i : ℕ))⁻¹, ← mul_assoc, mul_inv_cancel₀ hξ, one_mul]
      rw [e2]
      ring
    rw [e, mul_inv_cancel_right₀ (hI0 i')]
  rw [key, f2 _ _ (hI0 i') (hI0 i) s hs, hratio]
  exact f5 s hs

end GlobalTheory.RowShape

namespace GlobalTheory.RowShape

theorem big_primAt_rowN : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v,
    GlobalTheory.FinPl.PrimAt ch.W.ψ (besDecAt ch.G j σ hj) (GlobalTheory.RowShape.rowN ch.G j) v :=
  big_mono (fun ch h j σ hj v => primAt_rowN h ch.G j σ hj v) GlobalTheory.BigTop.Fun.OneSqTie.big_std

end GlobalTheory.RowShape

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselFlag_character_primitive_rowTest_movedLattice : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v, GlobalTheory.FinPl.PrimAt ch.W.ψ (besDecAt ch.G j σ hj) (GlobalTheory.RowShape.rowN ch.G j) v := by
  atlas_forward_decl GlobalTheory.RowShape.big_primAt_rowN
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped nonZeroDivisors

namespace GlobalTheory.RowShape

namespace PrimJac

theorem rowJac_line {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (n : ℕ) (hn : n < D.R.m) (σ : ℕ)
    (h : D.R.m - 1 - n = 2 * σ) (v : Pl D) (p : Fin σ) (a : AE D) :
    colMul (rowJac G n hn σ h).jX p a ∈ latV _ (rowN G n) (· = v) ↔
      a ∈ idV (rowId D n (Fin.castLE (by omega) p)) v := by
  have e1 : colMul (rowJac G n hn σ h).jX p a =
      fun k => a * incA D (1 * (G.rowDec n hn).a k (Fin.castLE (by omega) p)) := by
    funext k
    simp [colMul, HypDec.jX, rat, Matrix.map_apply, rowJac, jacDec, HermitianOrthogonalExtensionData.iso]
  have e2 : rowN G n = (G.rowDec n hn).lat (G.Λ (.top n)) (rowId D n) := by
    unfold rowN; rw [dif_pos hn]
  rw [e1, e2, GlobalTheory.StairLine.line_mem_iff _ _ _ _ (by simp only [Fin.coe_castLE]; omega) one_ne_zero v a, inv_one,
    FractionalIdeal.spanSingleton_one, one_mul]

theorem stairId_ne_zero (D : D7) (c : ℕ) (p : Fin c) : stairId D.host.AA D.host.AAbar c p ≠ 0 := by
  unfold stairId
  exact mul_ne_zero (pow_ne_zero _ (GlobalTheory.CuspCharLattice.host_AA_ne_zero _))
    (inv_ne_zero (pow_ne_zero _ (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D)))

theorem tiltSc_first {D : D7} {n : ℕ} (hodd : Odd n) (p : Fin (D.R.m - 1 - n)) (hp : 2 * p.1 < D.R.m - 1 - n) :
    tiltSc D n p = (D.host.xi0 ^ p.1)⁻¹ := by
  unfold tiltSc; rw [if_pos hodd, if_pos hp]

theorem rowId_ratio {D : D7} {n : ℕ} (hodd : Odd n) (p q : Fin (D.R.m - 1 - n)) (hpq : q.1 = p.1 + 1)
    (hq : 2 * q.1 < D.R.m - 1 - n) : rowId D n p * (rowId D n q)⁻¹ = dI D := by
  have hx : D.host.xi0 ≠ 0 := cmHost_imaginaryGenerator_ne_zero
  unfold rowId
  rw [tiltSc_first hodd p (by omega), tiltSc_first hodd q hq,
    stairId_succ (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) p q hpq]
  have hS := stairId_ne_zero D (D.R.m - 1 - n) q
  revert hS
  generalize stairId D.host.AA D.host.AAbar (D.R.m - 1 - n) q = S
  intro hS
  rw [mul_inv, FractionalIdeal.spanSingleton_inv, inv_inv]
  unfold dI
  calc _ = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (D.host.xi0 ^ p.1)⁻¹ *
        FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (D.host.xi0 ^ q.1) * D.host.AA * D.host.AAbar * (S * S⁻¹) := by ring
    _ = _ := by
      rw [mul_inv_cancel₀ hS, mul_one, FractionalIdeal.spanSingleton_mul_spanSingleton, hpq, pow_succ,
        ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hx), one_mul]

end PrimJac

open PrimJac

theorem primAt_rowJac {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (ψ : AddChar (AF D.host.F) ℂ)
    (hψ : IsStdChar D ψ (-1)) (n : ℕ) (hn : n < D.R.m) (σ : ℕ) (h : D.R.m - 1 - n = 2 * σ) (v : Pl D) :
    PrimAt ψ (rowJac G n hn σ h) (rowN G n) v := by
  have hodd : Odd n := by
    obtain ⟨k, hk⟩ := D.R.m_even
    exact ⟨k - σ - 1, by omega⟩
  intro i j hij s hs
  have key : (∀ a : AE D, colMul (rowJac G n hn σ h).jX j a ∈ latV _ (rowN G n) (· = v) →
      colMul (rowJac G n hn σ h).jX i (s * a) ∈ latV _ (rowN G n) (· = v)) ↔
      ∀ a ∈ idV (rowId D n (Fin.castLE (by omega) j)) v, s * a ∈ idV (rowId D n (Fin.castLE (by omega) i)) v :=
    ⟨fun H a ha => (rowJac_line G n hn σ h v i _).1 (H a ((rowJac_line G n hn σ h v j a).2 ha)),
      fun H a hc => (rowJac_line G n hn σ h v i _).2 (H a ((rowJac_line G n hn σ h v j a).1 hc))⟩
  have hne : ∀ p : Fin (D.R.m - 1 - n), rowId D n p ≠ 0 := fun p => mul_ne_zero
    (by
      rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
      unfold tiltSc
      split_ifs <;> simp [cmHost_imaginaryGenerator_ne_zero])
    (stairId_ne_zero D _ p)
  rw [key, GlobalTheory.IdealQuot.mul_subset_iff D v _ _ (hne _) (hne _) s hs,
    rowId_ratio hodd _ _ (by simp only [Fin.coe_castLE]; exact hij) (by simp only [Fin.coe_castLE]; have := j.2; omega)]
  exact DiffDual.idV_dI_iff D ψ hψ v s hs

theorem big_primAt_rowJac : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ n (hn : n < D.R.m) σ
    (h : D.R.m - 1 - n = 2 * σ) v, GlobalTheory.FinPl.PrimAt ch.W.ψ (rowJac ch.G n hn σ h) (GlobalTheory.RowShape.rowN ch.G n) v :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ n hn σ h v =>
    primAt_rowJac ch.G ch.W.ψ ch.W.ψ_std n hn σ h v⟩⟩

end GlobalTheory.RowShape
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobiFlagChar_primitive_movedLattice_largeDepth : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ n (hn : n < D.R.m) σ (h : D.R.m - 1 - n = 2 * σ) v, GlobalTheory.FinPl.PrimAt ch.W.ψ (rowJac ch.G n hn σ h) (GlobalTheory.RowShape.rowN ch.G n) v := by
  atlas_forward_decl GlobalTheory.RowShape.big_primAt_rowJac
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.RowColsBF

open GlobalTheory.RowShape GlobalTheory.RowChain GlobalTheory.StairCols

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem tiltSc_odd {j : ℕ} (hj : Odd j) (p : Fin (D.R.m - 1 - j)) (hp : 2 * p.1 < D.R.m - 1 - j) :
    tiltSc D j p = (D.host.xi0 ^ p.1)⁻¹ := by
  rw [tiltSc, if_pos hj, if_pos hp]

theorem tiltSc_even {j : ℕ} (hj : ¬ Odd j) (p : Fin (D.R.m - 1 - j)) : tiltSc D j p = 1 := by
  rw [tiltSc, if_neg hj]

theorem besCol_eq (G : GridData L sc) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (i : Fin σ) (a : AE D) :
    GlobalTheory.FinPl.colMul (besDecAt G j σ hj).jX i a =
      fun k => (a * incA D (D.host.xi0 ^ i.1)) * incA D ((G.rowDec j (by omega)).a k (Fin.castLE (by omega) i)) := by
  funext k
  simp only [GlobalTheory.FinPl.colMul, HypDec.jX, besDecAt, diagDec, rowBes, besDec, HermitianOrthogonalExtensionData.iso, rat, Matrix.map_apply,
    Matrix.mul_diagonal, Matrix.submatrix_apply, lam, id_eq, map_mul]
  ring

theorem jacCol_eq (G : GridData L sc) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (i : Fin σ) (a : AE D) :
    GlobalTheory.FinPl.colMul (xZero (rowJac G (j + 1) (by omega) σ (by omega))) i a =
      fun k => a * incA D ((G.rowDec (j + 1) (by omega)).a k (Fin.castLE (by omega) i)) := rfl

theorem cols (G : GridData L sc) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (v : GlobalTheory.FinPl.Pl D) :
    GlobalTheory.FinPl.ColsAt (besDecAt G j σ hj) (xZero (rowJac G (j + 1) (by omega) σ (by omega)))
      (rowN G j) (rowN G (j + 1)) v := by
  intro i a ha
  have hjm : j < D.R.m := by omega
  have hjm' : j + 1 < D.R.m := by omega
  obtain ⟨k, hk⟩ := D.R.m_even
  have hev : ¬ Odd j := by
    rw [Nat.not_odd_iff_even]; exact ⟨k - σ - 1, by omega⟩
  have hod : Odd (j + 1) := ⟨k - σ - 1, by omega⟩
  rw [besCol_eq G j σ hj i a, jacCol_eq G j σ hj i a]
  have l1 : rowN G j = (G.rowDec j hjm).lat (G.Λ (.top j)) (rowId D j) := dif_pos hjm
  have l2 : rowN G (j + 1) = (G.rowDec (j + 1) hjm').lat (G.Λ (.top (j + 1))) (rowId D (j + 1)) := dif_pos hjm'
  have hpr : (Fin.castLE (by omega : σ ≤ D.R.m - 1 - j) i).rev ≠ Fin.castLE (by omega) i := fun e => by
    have := congrArg Fin.val e
    simp only [Fin.val_rev, Fin.val_castLE] at this
    omega
  have hqr : (Fin.castLE (by omega : σ ≤ D.R.m - 1 - (j + 1)) i).rev ≠ Fin.castLE (by omega) i := fun e => by
    have := congrArg Fin.val e
    simp only [Fin.val_rev, Fin.val_castLE] at this
    omega
  rw [GlobalTheory.FinPl.latV, l1, col_mem_iff (G.rowDec j hjm) _ hpr _ _ 1 {1}
    (fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact FractionalIdeal.one_mem_one _)
    (fun x hx => by
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      exact ⟨1, rfl, o, (one_mul _).symm⟩) v]
  rw [GlobalTheory.FinPl.latA, l2, col_mem_iff (G.rowDec (j + 1) hjm') _ hqr _ _ D.host.AA {a | a ∈ D.host.AA} (fun x hx => hx)
    (fun x hx => ⟨x, hx, 1, by simp⟩) v]
  have e3 : D.host.AA * rowId D (j + 1) (Fin.castLE (by omega) i) =
      FractionalIdeal.spanSingleton _ (D.host.xi0 ^ i.1)⁻¹ * (1 * rowId D j (Fin.castLE (by omega) i)) := by
    rw [rowId, rowId, tiltSc_even hev, tiltSc_odd hod _ (by simp only [Fin.val_castLE]; omega),
      FractionalIdeal.spanSingleton_one, one_mul, one_mul, stairId, stairId]
    simp only [Fin.val_castLE]
    have h1 : D.R.m - 1 - j - i.1 = (D.R.m - 1 - (j + 1) - i.1) + 1 := by omega
    rw [h1, pow_succ]
    ring
  rw [e3, GlobalTheory.StairLine.mem_idV_inv_mul (pow_ne_zero _ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)), mul_comm a]

theorem colsAt_bf : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v,
    GlobalTheory.FinPl.ColsAt (besDecAt ch.G j σ hj) (xZero (rowJac ch.G (j + 1) (by omega) σ (by omega)))
      (GlobalTheory.RowShape.rowN ch.G j) (GlobalTheory.RowShape.rowN ch.G (j + 1)) v :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => fun j σ hj v => cols ch.G j σ hj v⟩⟩

end GlobalTheory.RowColsBF
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselToJacobi_basePoint_carries_row_lattice_lines : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v, GlobalTheory.FinPl.ColsAt (besDecAt ch.G j σ hj) (xZero (rowJac ch.G (j + 1) (by omega) σ (by omega)))
    (GlobalTheory.RowShape.rowN ch.G j) (GlobalTheory.RowShape.rowN ch.G (j + 1)) v := by
  atlas_forward_decl GlobalTheory.RowColsBF.colsAt_bf
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowShape.ColsJB

variable {D : D7} {A B : HSp D} {c : ℕ}

theorem coreMat_iB' {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iB = midCol d h := by
  refine (Matrix.submatrix_mul_equiv _ _ _ _ _).trans ?_
  show Matrix.fromCols (frameMat B A d.ι) (midCol d h) *
      Matrix.fromRows (0 : Matrix (Fin A.rank) (Fin 1) D.host.E) (1 : Matrix (Fin 1) (Fin 1) D.host.E) = _
  rw [Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, zero_add]

theorem coreMat_vecB {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) (x : D.host.E) :
    coreMat d h *ᵥ vecB (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)) (fun _ => x) =
      fun k => x * d.a k ⟨σ, by omega⟩ := by
  show coreMat d h *ᵥ (_ *ᵥ _) = _
  rw [Matrix.mulVec_mulVec, coreMat_iB']
  funext k
  show ∑ j : Fin 1, midCol d h k j * x = _
  simp [midCol, mul_comm]

end GlobalTheory.RowShape.ColsJB

theorem GlobalTheory.RowShape.cols_jacBes_rowN : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ i σ (hi : i + 2 * (σ + 1) + 1 = D.R.m) v, GlobalTheory.FinPl.ColsAt (rowJac ch.G i (by omega) (σ + 1) (by omega))
    (xLast (besDecAt ch.G (i + 1) σ (by omega)) (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top (i + 1))) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ))
    (GlobalTheory.RowShape.rowN ch.G i) (GlobalTheory.RowShape.rowN ch.G (i + 1)) v := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ => ?_⟩⟩
  intro i σ hi v a s hs
  have hodd : Odd i := by
    obtain ⟨k, hk⟩ := D.R.m_even
    exact ⟨k - σ - 2, by omega⟩
  unfold GlobalTheory.RowShape.rowN
  rw [dif_pos (by omega), dif_pos (by omega)]
  have hrat : ∀ {m n : ℕ} (N : Matrix (Fin m) (Fin n) D.host.E) (z : Fin n → D.host.E),
      GlobalTheory.MixModel.rat N *ᵥ ratV z = ratV (N *ᵥ z) := by
    intro m n N z
    funext k
    simp [GlobalTheory.MixModel.rat, ratV, Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hL : colMul (rowJac ch.G i (by omega) (σ + 1) (by omega)).jX a s =
      fun k => s * incA D ((ch.G.rowDec i (by omega)).a k ⟨a.1, by omega⟩) := by
    funext k
    rfl
  have hR : colMul (xLast (besDecAt ch.G (i + 1) σ (by omega))
      (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top (i + 1))) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ)) a s =
      fun k => (s * incA D (D.host.xi0 ^ a.1)) * incA D ((ch.G.rowDec (i + 1) (by omega)).a k ⟨a.1, by omega⟩) := by
    funext k
    induction a using Fin.lastCases with
    | last =>
      have e1 := GlobalTheory.RowShape.ColsJB.coreMat_vecB (ch.G.rowDec (i + 1) (by omega)) (σ := σ) (by omega) (D.host.xi0 ^ σ)
      simp only [colMul, xLast, Matrix.of_apply, Fin.snoc_last, HypDec.j0, hrat, Fin.val_last]
      show s * ratV ((coreMat (ch.G.rowDec (i + 1) (by omega)) (σ := σ) (by omega)) *ᵥ _) k = _
      rw [e1]
      simp only [ratV, map_mul]
      ring
    | cast b =>
      simp only [colMul, xLast, Matrix.of_apply, Fin.snoc_castSucc, HypDec.jX, GlobalTheory.MixModel.rat, Matrix.map_apply]
      show s * incA D ((Matrix.submatrix (ch.G.rowDec (i + 1) (by omega)).a id (Fin.castLE (by omega)) *
        diagonal (lam (D := D) σ) : Matrix (Fin _) (Fin σ) D.host.E) k b) = _
      rw [Matrix.mul_diagonal, map_mul]
      simp only [lam, Matrix.submatrix_apply, id, Fin.coe_castSucc]
      rw [mul_comm (incA D _) (incA D _), ← mul_assoc]
      rfl
  rw [hL, hR, (GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v s).1,
    (GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v _).2]
  have hx : D.host.xi0 ^ a.1 ≠ 0 := pow_ne_zero _ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)
  have h1 : GlobalTheory.RowShape.rowId D i ⟨a.1, by omega⟩ = FractionalIdeal.spanSingleton _ ((D.host.xi0 ^ a.1)⁻¹) *
      stairId D.host.AA D.host.AAbar (D.R.m - 1 - i) ⟨a.1, by omega⟩ := by
    unfold GlobalTheory.RowShape.rowId GlobalTheory.RowShape.tiltSc
    rw [if_pos hodd, if_pos (by simp only; omega)]
  have h2 : D.host.AA * GlobalTheory.RowShape.rowId D (i + 1) ⟨a.1, by omega⟩ =
      stairId D.host.AA D.host.AAbar (D.R.m - 1 - i) ⟨a.1, by omega⟩ := by
    unfold GlobalTheory.RowShape.rowId GlobalTheory.RowShape.tiltSc
    rw [if_neg (by rw [Nat.not_odd_iff_even]; exact hodd.add_one), FractionalIdeal.spanSingleton_one, one_mul]
    unfold stairId
    rw [show D.R.m - 1 - i - a.1 = (D.R.m - 1 - (i + 1) - a.1) + 1 by omega, pow_succ]
    ring
  rw [h1, h2, idV_spanSingleton_mul_iff D v _ _ (inv_ne_zero hx) s, inv_inv, mul_comm, and_iff_left hs]
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobiToBessel_carries_flagLines_rowPeriod_succ : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ i σ (hi : i + 2 * (σ + 1) + 1 = D.R.m) v, GlobalTheory.FinPl.ColsAt (rowJac ch.G i (by omega) (σ + 1) (by omega))
    (xLast (besDecAt ch.G (i + 1) σ (by omega)) (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top (i + 1))) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ))
    (GlobalTheory.RowShape.rowN ch.G i) (GlobalTheory.RowShape.rowN ch.G (i + 1)) v := by
  atlas_forward_decl GlobalTheory.RowShape.cols_jacBes_rowN
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped TensorProduct nonZeroDivisors

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.RowShape.LastBF

open GlobalTheory.GoodPos GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem mem_completedHomLattice_iff_selfDual_source {S T : HSp D} {LS : Lat S} (LT : Lat T) (hS : IsSelfDualC S LS) (P : Pl D → Prop) (u : WO S T) :
    u ∈ latO S T (LS : Set _) (LT : Set _) P ↔
      MxAt P u ∧ ∀ y ∈ latV S LS P, Matrix.mulVec (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u) y ∈ latA T LT P := by
  refine ⟨fun hu => ⟨latO_mxAt hu, fun y hy => latO_maps hS hu hy⟩, fun ⟨hP, hmap⟩ => ?_⟩
  obtain ⟨m, s, s', hs, hs', hdual⟩ := exists_dualBasis S hS
  let yv : Fin m → Fin S.rank → AE D := fun i l => pairA D.host.F 0 (indP D.host.F P) ⊗ₜ[D.host.F] (1 * s i l)
  have hyv : ∀ i, yv i ∈ latV S LS P := fun i =>
    AddSubgroup.subset_closure ⟨indP D.host.F P, indicatorAdele_mem_integralAdeles' _ _, indicatorAdele_supported _ _, 1, rfl, s i, hs i, rfl⟩
  have hu : u = ∑ i, rowMul S T (s' i) (u *ᵥ yv i) := by
    ext k j
    simp only [Matrix.sum_apply, rowMul, Matrix.of_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, yv]
    simp only [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, ← TensorProduct.tmul_sum, hdual]
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]; exact (mul_indP (hP k j)).symm
    · intro l _ hl; rw [if_neg hl, TensorProduct.tmul_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hu]
  exact sum_mem fun i _ => rowMul_mem (hs' i) (hmap _ (hyv i))

theorem last_of_line {V₀ W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (z : Fin V₀.rank → D.host.E) {M : Lat V₀} (LW : Lat W)
    (hM : IsSelfDualC V₀ M) {x : Pl D} {m : (AE D)ˣ} (r : Fin ρ) (hr : r.1 + 1 = ρ)
    (hW : ∀ t ∈ idAt D (· = x), colMul d.jY r t ∈ latA W LW (· = x) ↔
      incA D D.host.xi0 * cA D (m : AE D) * t ∈ intAt D (· = x))
    (hz : ∀ a ∈ idAt D (· = x), a • ratV z ∈ latV V₀ M (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) :
    ∀ a ∈ idAt D (· = x),
      d.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (M : Set _) (LW : Set _) (· = x) ↔ a ∈ intAt D (· = x) := fun a ha => by
  have hsd := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V₀ M x hM
  have hmx : MxAt (· = x) (d.incAdj V₀ (a • yZero V₀ ρ z)) :=
    mxAt_mul _ (mxAt_smul _ (mxAt_mul' _ (mxAt_adj fun i j => Ideal.mul_mem_right _ _ ha)))
  rw [mem_completedHomLattice_iff_selfDual_source LW hM, and_iff_right hmx]
  have h1 := hz _ (Ideal.mul_mem_left _ (m : AE D) ha)
  rw [Units.inv_mul_cancel_left,
    hsd.2.2 (((m : AE D) * a) • ratV z) fun i => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)] at h1
  rw [← h1]
  refine forall₂_congr fun y hy => ?_
  rw [incAdj_yZero_mulVec d _ hr, hW _ (Ideal.mul_mem_left _ _ (GlobalTheory.IwaPlace.LocSD.hermAt_mem_idAt (hsd.1 y hy) _)),
    ← herm_conj V₀ y (((m : AE D) * a) • ratV z), int_conj, mul_smul]
  have e1 := herm_smul V₀ 1 m y (a • ratV z)
  rw [one_smul] at e1
  rw [e1]
  have e3 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := (xiU D).mul_inv
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (cA D m * GlobalTheory.IwaPlace.hermAt V₀ y (a • ratV z)) * e3

theorem const_mem_latPi {S : HSp D} (i₀ : Fin S.rank) (I : FI D) (v : Pl D) (s : AE D) :
    (fun _ => s) ∈ latV S (latPi S I) (· = v) ↔ s ∈ idV I v := by
  constructor
  · intro hy
    have key : ∀ y ∈ latV S (latPi S I) (· = v), y i₀ ∈ idV I v := fun y hy => by
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨α, hα, h0, a, rfl, z, hz, rfl⟩ := hy
        exact AddSubgroup.subset_closure ⟨α, hα, h0, z i₀, mem_latPi.1 hz i₀, by simp only [one_mul]⟩
      | zero => exact zero_mem _
      | add a b _ _ ha hb => exact add_mem ha hb
      | neg a _ ha => exact neg_mem ha
    exact key _ hy
  · intro hs
    induction hs using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, h0, z, hz, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨α, hα, h0, 1, rfl, fun _ => z, mem_latPi.2 fun _ => hz,
        funext fun i => by rw [one_mul]⟩
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | neg a _ ha => exact neg_mem ha

theorem AA_mul_rowId (j τ : ℕ) (hj : j + 2 * (τ + 1) + 2 = D.R.m) (p : Fin (D.R.m - 1 - (j + 1))) (hp : p.1 = τ + 1) :
    D.host.AA * rowId D (j + 1) p = FractionalIdeal.spanSingleton _ (star (D.host.xi0 ^ τ)) * lineId D j := by
  have hodd : Odd (j + 1) := by
    obtain ⟨k, hk⟩ := D.R.m_even
    exact ⟨k - τ - 2, by omega⟩
  unfold rowId tiltSc lineId stairId
  rw [if_pos hodd, if_neg (by omega), show D.R.m - 1 - (j + 1) - 1 - p.1 = τ by omega,
    show D.R.m - 1 - (j + 1) - p.1 = τ + 1 by omega, show (D.R.m - 2 - j) / 2 = τ + 1 by omega, hp,
    pow_succ D.host.AA (τ + 1)]
  ring

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem last_rowN (G : GridData L sc) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (v : Pl D) (hσ : 0 < σ) :
    ∀ a ∈ idAt D (· = v),
    (rowJac G (j + 1) (by omega) σ (by omega)).incAdj (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (a • yZero (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) σ
        (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ)) ∈
      latO (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) (G.V (.grid D.R.m (j + 1)))
        (coreL G j : Set _) (rowN G (j + 1) : Set _) (· = v) ↔ a ∈ intAt D (· = v) := by
  obtain ⟨τ, rfl⟩ : ∃ τ, σ = τ + 1 := ⟨σ - 1, by omega⟩
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hL : IsSelfDualC _ (lineL D j) :=
    isSelfDualC_latPi (GlobalTheory.RowShape.nLine_gram D) (lineId_ne_zero D j) (lineId_mul_conj D j)
  have hX : IsSelfDualC _ (G.Λ (.top j)) :=
    (G.isV (X := .top j) (show j ≤ D.R.m by omega) (fun _ h => by cases h)).sd
  have hM : IsSelfDualC _ (coreL G j) := GlobalTheory.Core.Rk.SumBox.selfDual_sumLatO D _ _ _ _ _ _ hX hL
  have ho : OrthAt (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (coreL G j) (G.Λ (.top j)) (lineL D j) v := GlobalTheory.Core.Rk.SumSplit.orthAt_sumLatO D _ _ _ _ _ _ v
  obtain ⟨g, hg, hgen⟩ := GlobalTheory.IdVGen.idV_gen D v (lineId D j) (lineId_ne_zero D j)
  have hx : D.host.xi0 ^ (τ + 1) ≠ 0 := pow_ne_zero _ hξ
  have hm0 : g * (D.host.xi0 ^ (τ + 1))⁻¹ ≠ 0 := mul_ne_zero hg (inv_ne_zero hx)
  have hline : ∀ a ∈ idAt D (· = v),
      a • ratV (fun _ : Fin (GlobalTheory.SeeSaw.Model.nLine D).rank => D.host.xi0 ^ (τ + 1)) ∈
        latV (GlobalTheory.SeeSaw.Model.nLine D) (lineL D j) (· = v) ↔
      (((inU _ hm0)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = v) := fun a ha => by
    refine (const_mem_latPi (S := GlobalTheory.SeeSaw.Model.nLine D) (0 : Fin 1) (lineId D j) v
      (a * incA D (D.host.xi0 ^ (τ + 1)))).trans ?_
    rw [hgen, and_iff_left (Ideal.mul_mem_right _ _ ha), inU_inv, mul_inv, inv_inv, RingHom.map_mul, mul_assoc, mul_comm a]
  have hU := line_norm (GlobalTheory.SeeSaw.Model.isLineVec_nLine hx) hL hline
  have hN : star (fun _ : Fin (GlobalTheory.SeeSaw.Model.nLine D).rank => D.host.xi0 ^ (τ + 1)) ⬝ᵥ
      (GlobalTheory.SeeSaw.Model.nLine D).gram *ᵥ (fun _ => D.host.xi0 ^ (τ + 1)) =
      -(star (D.host.xi0 ^ (τ + 1)) * D.host.xi0 ^ (τ + 1)) := by
    rw [GlobalTheory.RowShape.nLine_gram, neg_mulVec, one_mulVec, dotProduct_neg]
    exact congrArg Neg.neg (Fin.sum_univ_one (fun _ : Fin 1 => star (D.host.xi0 ^ (τ + 1)) * D.host.xi0 ^ (τ + 1)))
  rw [hN] at hU
  refine last_of_line _ _ _ hM (m := inU _ hm0) (Fin.last τ) rfl (fun t ht => ?_)
    (fun a ha => (orth_line _ ho _ a).symm.trans (hline a ha))
  have hc : colMul (rowJac G (j + 1) (by omega) (τ + 1) (by omega)).jY (Fin.last τ) t =
      fun k => t * incA D ((G.rowDec (j + 1) (by omega)).a k
        (Fin.castLE (by omega : τ + 1 ≤ D.R.m - 1 - (j + 1)) (Fin.last τ)).rev) := by
    funext k
    rfl
  have hs : star (D.host.xi0 ^ τ) ≠ 0 := star_ne_zero.2 (pow_ne_zero _ hξ)
  rw [hc, rowN, dif_pos (by omega), (GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v t).2,
    AA_mul_rowId j τ hj _ (by simp only [Fin.val_rev, Fin.val_castLE, Fin.val_last]; omega),
    idV_spanSingleton_mul_iff D v _ _ hs t, and_iff_left ht, hgen, and_iff_left (Ideal.mul_mem_left _ _ ht),
    hU _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ht)), inU_val]
  have e : g * (D.host.xi0 ^ (τ + 1))⁻¹ * -(star (D.host.xi0 ^ (τ + 1)) * D.host.xi0 ^ (τ + 1)) *
      (g⁻¹ * (star (D.host.xi0 ^ τ))⁻¹) = D.host.xi0 := by
    rw [pow_succ D.host.xi0 τ, star_mul, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg]
    have := pow_ne_zero τ hξ
    field_simp
  have e' := congrArg (incA D) e
  rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_mul (incA D) g⁻¹] at e'
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (cA D (incA D (g * (D.host.xi0 ^ (τ + 1))⁻¹)) * t) * e'

end GlobalTheory.RowShape.LastBF

theorem GlobalTheory.RowShape.big_last_rowN : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v, 0 < σ → ∀ a ∈ GlobalTheory.FinPl.idAt D (· = v),
    (rowJac ch.G (j + 1) (by omega) σ (by omega)).incAdj (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (a • yZero (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) σ
        (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ)) ∈
      latO (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) (ch.G.V (.grid D.R.m (j + 1)))
        (GlobalTheory.RowShape.coreL ch.G j : Set _) (GlobalTheory.RowShape.rowN ch.G (j + 1) : Set _) (· = v) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = v) :=
  ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ j σ hj v hσ =>
    GlobalTheory.RowShape.LastBF.last_rowN ch.G j σ hj v hσ⟩⟩

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselLastVector_mem_homLattice_iff_integral : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v, 0 < σ → ∀ a ∈ GlobalTheory.FinPl.idAt D (· = v),
    (rowJac ch.G (j + 1) (by omega) σ (by omega)).incAdj (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (a • yZero (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) σ
        (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ)) ∈
      latO (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) (ch.G.V (.grid D.R.m (j + 1)))
        (GlobalTheory.RowShape.coreL ch.G j : Set _) (GlobalTheory.RowShape.rowN ch.G (j + 1) : Set _) (· = v) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = v) := by
  atlas_forward_decl GlobalTheory.RowShape.big_last_rowN
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.LastLineLat

variable {D : D7}

theorem of_tmul_eq (p : AF D.host.F) {m n : ℕ} (y : Fin m → Fin n → D.host.E) :
    (Matrix.of fun i j => p ⊗ₜ[D.host.F] y i j : Mx D m n) = (p ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • rat (Matrix.of y) := by
  ext i j
  simp only [rat, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  change _ = _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] y i j)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem cA_tmul_one (p : AF D.host.F) : cA D (p ⊗ₜ[D.host.F] (1 : D.host.E)) = p ⊗ₜ[D.host.F] (1 : D.host.E) := by
  simp [cA, sigR]

theorem adj_rat {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) : adj (rat M : Mx D m n) = rat Mᴴ := by
  ext i j
  simp [adj, rat, Matrix.conjTranspose_apply, GlobalTheory.DualPairCheck.cA_incA]

theorem rat_smul' {m n : ℕ} (c : D.host.E) (M : Matrix (Fin m) (Fin n) D.host.E) :
    (rat (c • M) : Mx D m n) = incA D c • rat M := by
  ext i j
  simp [rat]

theorem kap_gen {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) {c0 : D.host.E} (hτ : ∀ i k, τ i k = c0)
    (V : HSp D) (p : AF D.host.F) (a : D.host.E) (s : Fin V.rank → D.host.E)
    (t : Fin L''.rank → D.host.E) :
    kap τ V (Matrix.of fun i j => p ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * V.gram k j)) =
      Matrix.of fun i j => p ⊗ₜ[D.host.F] (s i * star (D.host.xi0⁻¹ * c0 * ∑ l, a * t l) * ∑ k, L.gram k j) := by
  have hy : (Matrix.of fun i j => a * t i * ∑ k, star (s k) * V.gram k j) =
      Matrix.vecMulVec (fun i => a * t i) (star s) * V.gram := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Finset.mul_sum, mul_assoc]
  have h1 := of_tmul_eq (D := D) p (fun i j => a * t i * ∑ k, star (s k) * V.gram k j)
  rw [hy] at h1
  have h2 := of_tmul_eq (D := D) p (fun i j => s i * star (D.host.xi0⁻¹ * c0 * ∑ l, a * t l) * ∑ k, L.gram k j)
  beta_reduce at h1 h2
  rw [h1, h2]
  unfold GlobalTheory.FinPl.kap GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  have he := cA_tmul_one (D := D) p
  generalize (p ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) = e at he ⊢
  rw [Matrix.mul_smul, adj_smul, he]
  rw [rat_mul (Matrix.vecMulVec (fun i => a * t i) (star s)) V.gram, ← Matrix.mul_assoc (rat τ), ← rat_mul τ,
    show (rat V.gram : Mx D V.rank V.rank) = gA V from rfl, adj_mul, adj_gA, adj_rat, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc, giA_gA_cancel, show gA L = (rat L.gram : Mx D L.rank L.rank) from rfl, ← rat_mul, smul_comm,
    ← rat_smul']
  congr 2
  ext i j
  congr 1
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, hτ,
    Pi.star_apply, Matrix.of_apply, smul_eq_mul, star_sum, star_mul', star_star, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg,
    Finset.mul_sum, Finset.sum_mul, inv_neg]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.LastLineLat

namespace GlobalTheory.LastLineLat

variable {D : D7}

theorem kap_add' {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D) (w w' : WO S L'') :
    kap τ S (w + w') = kap τ S w + kap τ S w' := by
  have hadj : ∀ x y : Mx D L.rank S.rank, adj (x + y) = adj x + adj y := fun x y => by
    ext i j
    simp [adj]
  unfold GlobalTheory.FinPl.kap GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  rw [Matrix.mul_add (rat τ) w w', hadj, Matrix.add_mul, Matrix.mul_add, smul_add]

theorem line_mem {L V : HSp D} (J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (hJ : D.host.AA ≤ D.host.AAbar * J)
    (Λ : Set (Fin V.rank → D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (α : Af D.host.F)
    (hα : α ∈ intAf D.host.F) (hP : ∀ v, ¬ P v → evalV D.host.F v α = 0) (s : Fin V.rank → D.host.E) (hs : s ∈ Λ)
    (c : D.host.E) (hc : c ∈ D.host.AA) :
    (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (s i * star c * ∑ k, L.gram k j) : Mx D V.rank L.rank) ∈
      latO L V (GlobalTheory.RowShape.latPi L J : Set _) Λ P := by
  have hc' : c ∈ D.host.AAbar * J := hJ hc
  refine FractionalIdeal.mul_induction_on (C := fun c => (Matrix.of fun i j =>
      pairA D.host.F 0 α ⊗ₜ[D.host.F] (s i * star c * ∑ k, L.gram k j) : Mx D V.rank L.rank) ∈
      latO L V (GlobalTheory.RowShape.latPi L J : Set _) Λ P) hc' ?_ ?_
  · intro b hb e he
    refine AddSubgroup.subset_closure ⟨α, hα, hP, star b, ?_, fun _ => e, ?_, s, hs, ?_⟩
    · rw [bridge_star_holds D.R D.host b]; exact Formalism.L2.Pj.conj_mem_AA D hb
    · exact Submodule.mem_pi.2 fun _ _ => he
    · ext i j
      simp only [Matrix.of_apply, star_mul', Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun _ _ => by ring
  · intro x y hx hy
    have : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (s i * star (x + y) * ∑ k, L.gram k j) :
        Mx D V.rank L.rank) = (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (s i * star x * ∑ k, L.gram k j)) +
        (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (s i * star y * ∑ k, L.gram k j)) := by
      ext i j
      simp only [Matrix.of_apply, Matrix.add_apply, star_add, mul_add, add_mul, TensorProduct.tmul_add]
    rw [this]
    exact add_mem hx hy

theorem AA_le_lineId (D : D7) (j : ℕ) (hj : j + 2 = D.R.m) :
    D.host.AA ≤ D.host.AAbar * GlobalTheory.RowShape.lineId D j := by
  have hb : D.host.AAbar ≠ 0 := by
    intro h
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rw [h] at h1
    simp at h1
  unfold GlobalTheory.RowShape.lineId
  rw [show (D.R.m - 2 - j) / 2 + 1 = 1 by omega, pow_one, pow_one, mul_comm D.host.AA, ← mul_assoc,
    mul_inv_cancel₀ hb, one_mul]

theorem mul_mem_AA {a : D.host.E} (ha : a ∈ D.host.AA) {t : D.host.E}
    (ht : t ∈ ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) : a * t ∈ D.host.AA := by
  rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff] at ht
  obtain ⟨y, rfl⟩ := ht
  rw [mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ y ha

end GlobalTheory.LastLineLat

namespace GlobalTheory.LastLineLat

theorem kap_latO (D : D7) (V : HSp D) (Λ : Set (Fin V.rank → D.host.E)) (j : ℕ) (hj : j + 2 = D.R.m)
    (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∀ w ∈ latO V (pLine D) Λ (GlobalTheory.RowShape.topL D : Set _) (· = v),
      kap lastTau V w ∈ latO (Model.nLine D) V (GlobalTheory.RowShape.lineL D j : Set _) Λ (· = v) := by
  have hle : latO V (pLine D) Λ (GlobalTheory.RowShape.topL D : Set _) (· = v) ≤
      (latO (Model.nLine D) V (GlobalTheory.RowShape.lineL D j : Set _) Λ (· = v)).comap (AddMonoidHom.mk' (kap lastTau V) (kap_add' lastTau V)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, AddMonoidHom.mk'_apply]
    rw [kap_gen lastTau (c0 := -D.host.xi0) (fun _ _ => rfl)]
    refine line_mem _ (AA_le_lineId D j hj) Λ _ α hα hP s hs _ ?_
    have hx := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
    rw [show D.host.xi0⁻¹ * -D.host.xi0 = -1 by rw [mul_neg, inv_mul_cancel₀ hx], neg_one_mul]
    have ht' : t ∈ GlobalTheory.RowShape.latPi (pLine D) 1 := ht
    exact Submodule.neg_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) (Submodule.sum_mem _ fun l _ => mul_mem_AA ha (Submodule.mem_pi.1 ht' l (Set.mem_univ _)))
  exact fun w hw => hle hw

end GlobalTheory.LastLineLat

theorem GlobalTheory.LastLineLat.kap_lastTau_latO : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j, j + 2 = D.R.m → ∀ v, ∀ w ∈ latO (ch.G.V (.top (j + 1))) (pLine D) (ch.G.Λ (.top (j + 1)) : Set _) (GlobalTheory.RowShape.topL D : Set _) (· = v),
    GlobalTheory.FinPl.kap lastTau _ w ∈ latO (GlobalTheory.SeeSaw.Model.nLine D) (ch.G.V (.top (j + 1))) (GlobalTheory.RowShape.lineL D j : Set _) (ch.G.Λ (.top (j + 1)) : Set _) (· = v) := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R _ _ ch _ _ j hj v
  exact GlobalTheory.LastLineLat.kap_latO D _ _ j hj v
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastSeesawLineMap_keeps_lattices_largeDepth : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j, j + 2 = D.R.m → ∀ v, ∀ w ∈ latO (ch.G.V (.top (j + 1))) (pLine D) (ch.G.Λ (.top (j + 1)) : Set _) (GlobalTheory.RowShape.topL D : Set _) (· = v),
    GlobalTheory.FinPl.kap lastTau _ w ∈ latO (GlobalTheory.SeeSaw.Model.nLine D) (ch.G.V (.top (j + 1))) (GlobalTheory.RowShape.lineL D j : Set _) (ch.G.Λ (.top (j + 1)) : Set _) (· = v) := by
  atlas_forward_decl GlobalTheory.LastLineLat.kap_lastTau_latO
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastRowUnram

theorem chars_unram : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ (t : T) (v : GlobalTheory.FinPl.Pl D), (∀ w ∈ locPl ch.G t, w.under (𝓞 D.host.F) ≠ v) → ∀ i, i < D.R.m →
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (ch.G.chrS (.mu t D.R.m i)) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (ch.G.chrT (.mu t D.R.m i)) v := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ => ?_⟩⟩
  intro t v hv i hi
  classical
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hS0 := GlobalTheory.RowVacScalar.notMem_S0_of_no_place_above ch.G t hv
  have hQ : ∀ PP ∈ R.toLevCh.Q t, PP ∈ locPl ch.G t := fun PP h => by
    unfold locPl
    exact Finset.mem_union_right _ h
  have hmu : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (R.toLevCh.mu t (i + 1)) v := by
    refine GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_
    show GlobalTheory.LFun.UnrAt (R.toLevCh.mu0 (i + 1) * R.toLevCh.xi t) w
    refine GlobalTheory.LFun.UnrAt.mul ?_ ?_
    · refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.mu0 ⟨i, hi⟩) w).2 ((R.toLevCh.C.isMu0 ⟨i, hi⟩).unr w fun k hk => ?_)
      refine hS0 (ch.G.pl.mem_S0_of_sum_eq.2 (Or.inr ((GlobalTheory.ChiGrid.S1_mem_OmF D).2 ?_)))
      have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
        show algebraMap _ (𝓞 D.host.E) _ ∈ w.asIdeal
        rw [map_natCast]; exact hk
      rw [hw] at this
      fin_cases k
      · exact Or.inl this
      · exact Or.inr (Or.inl this)
    · refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) w).2 ?_
      by_contra hu
      rcases (hL.Q_ram t w).1 hu with h | ⟨P', hP', hc⟩
      · exact hv w (hQ w h) hw
      · exact hv P' (hQ P' hP') ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc).trans hw)
  have key := GlobalTheory.RowVacScalar.attChr_charUnramAt hmu (GlobalTheory.RowVacScalar.eta_charUnramAt hL v)
  exact ⟨key _, key _⟩

end GlobalTheory.LastRowUnram
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRowChars_unramified_off_tensorPlaces : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ (t : T) (v : GlobalTheory.FinPl.Pl D), (∀ w ∈ locPl ch.G t, w.under (𝓞 D.host.F) ≠ v) → ∀ i, i < D.R.m →
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (ch.G.chrS (.mu t D.R.m i)) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (ch.G.chrT (.mu t D.R.m i)) v := by
  atlas_forward_decl GlobalTheory.LastRowUnram.chars_unram
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowShape

set_option maxHeartbeats 800000 in

theorem shapeAt_big : Big fun ch => ShapeAt ch := by
  refine big_mono (fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch h => ?_)
    ((((((((((((((GlobalTheory.T.gridRow_zero_basePoint_carriesLattice).and GlobalTheory.T.vacuum_base_point_moves_row_lattices).and GlobalTheory.T.posNormLine_selfDual_and_topLattice_splits).and GlobalTheory.T.negLineLattice_and_besselCoreLattice_selfDual_split).and GlobalTheory.T.isSelfDual_gridRowMovedLattice_largeDepth).and GlobalTheory.T.gridRowMovedLattice_splits_bessel_largeDepth).and GlobalTheory.T.gridRowMovedLattice_splits_jacobi_largeDepth).and GlobalTheory.T.besselFlag_character_primitive_rowTest_movedLattice).and GlobalTheory.T.jacobiFlagChar_primitive_movedLattice_largeDepth).and
      GlobalTheory.T.besselToJacobi_basePoint_carries_row_lattice_lines).and GlobalTheory.T.jacobiToBessel_carries_flagLines_rowPeriod_succ).and GlobalTheory.T.besselLastVector_mem_homLattice_iff_integral).and GlobalTheory.T.lastSeesawLineMap_keeps_lattices_largeDepth).and GlobalTheory.T.lastRowChars_unramified_off_tensorPlaces)
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hmv0, hmvS⟩, htop⟩, hcore⟩, hsd⟩, hmB⟩, hmJ⟩, hpB⟩, hpJ⟩, hcBF⟩, hcFB⟩, hlast⟩, hkap⟩, hun⟩ := h
  have hmv : ∀ (t : T) (b : Pts ch.G), IsBase t ch.S.B b → ∀ j, j ≤ D.R.m → GlobalTheory.FinPl.Moves _ (b j) (ch.G.Λ (.grid D.R.m j)) (GlobalTheory.RowShape.rowN ch.G j) fun _ => True := fun t b hb j hj => by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact hmv0 t b hb
    · exact hmvS t b hb j hj0 hj
  have hX : ∀ k, k ≤ D.R.m → IsSelfDualC (ch.G.V (.top k)) (ch.G.Λ (.top k)) := fun k hk =>
    (ch.G.isV (X := .top k) (by show k ≤ D.R.m; omega) (fun _ e => Node.noConfusion e)).sd
  refine ⟨GlobalTheory.RowShape.rowN ch.G, GlobalTheory.RowShape.coreL ch.G, GlobalTheory.RowShape.lineL D, GlobalTheory.RowShape.topL D, hmv, htop.1, htop.2,
    fun t M hM j σ hj vN v => ?_⟩
  obtain ⟨hLL, hN0, hO⟩ := hcore j σ hj
  refine ⟨hLL, hO v, ?_, ?_, ?_, ?_⟩
  · exact
      { tame := GlobalTheory.FinPl.TamePlaces.tame D v
        sdV := hsd j (by omega)
        sdV₀ := hN0
        sdW := hsd (j + 1) (by omega)
        sdW₀ := hX (j + 1) (by omega)
        monoV := hmB j σ hj v
        monoW := hmJ (j + 1) (by omega) σ (by omega) v
        prim := hpB j σ hj v
        cols := hcBF j σ hj v
        last := fun hσ a ha => hlast j σ hj v hσ a ha }
  · intro i hi hi'
    subst hi
    exact
      { tame := GlobalTheory.FinPl.TamePlaces.tame D v
        sdV := hsd i (by omega)
        sdV₀ := hX i (by omega)
        sdW := hsd (i + 1) (by omega)
        sdW₀ := hN0
        monoV := hmJ i (by omega) (σ + 1) (by omega) v
        monoW := hmB (i + 1) σ (by omega) v
        prim := hpJ i (by omega) (σ + 1) (by omega) v
        cols := hcFB i σ hi' v }
  · intro hσ w hw
    subst hσ
    exact hkap j (by omega) v w hw
  · exact fun hoff i hi => hun t v hoff i hi
end GlobalTheory.RowShape

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRowLatticesGoodPosition_large_depth : Big fun ch => ShapeAt ch := by
  atlas_forward_decl GlobalTheory.RowShape.shapeAt_big
end
