import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPatOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BesselCompatibility
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondModelFinitePartFrameActionMatrixStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelSubgroupConjFiniteMovesFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicGroupNormalizesFlagUnipotent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartNonempty
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.NLevelHolds
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFormCentralTranslation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateSymmetricUnipotentPatternStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceReductionsConjOfNestedFrameStabilisers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReductionIffPatternStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LambdaZeroEqProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffSymmetricPositionEntryPattern
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReductionStatement
import BuildAid.ForwardExisting

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.StepData ValuativeRel

namespace GlobalTheory.LevelComb

variable {D : D7} {u : D.what₂.Word} {d : GlobalTheory.SeeSaw.Dat D u} {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E}
  {PP : Formalism.L2.DIV.Pl D.host.E}

theorem mem_of_rho_lt (G : GAt d τ PP) {z : 𝓞 D.host.E} (hz : valuation G.k (rho G z) < 1) : z ∈ PP.asIdeal := by
  by_cases h0 : z = 0
  · subst h0; exact PP.asIdeal.zero_mem
  have h0' : rho G z ≠ 0 := (map_ne_zero (G.q.pr.comp (incA D))).2 (RingOfIntegers.coe_ne_zero_iff.2 h0)
  refine (G.idem.2 z h0).2 ?_
  rw [← G.q.sec_pr, ← G.q.int_iff]
  change (G.q.pr.comp (incA D)) _ ∉ _
  rw [map_inv₀, Valuation.mem_integer_iff, map_inv₀, not_le]
  exact (one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0'))).2 hz

end GlobalTheory.LevelComb

theorem GlobalTheory.LevelComb.red_uniq : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP) (x x' : G.S.P.J) (g g' : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)), G.Red x g → G.Red x' g' → GlobalTheory.StepData.MaxM ((x' : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val) → g' = g := by
  intro D u d τ PP G x x' g g' hx hx' hm
  rw [GlobalTheory.LevelComb.red_iff] at hx hx'
  ext a' b'
  obtain ⟨a, rfl⟩ := (GlobalTheory.LevelComb.pos G).surjective a'
  obtain ⟨b, rfl⟩ := (GlobalTheory.LevelComb.pos G).surjective b'
  have h := (valuation G.k).map_sub_lt ((valuation G.k).map_add_lt (hx a b) (hm a b)) (hx' a b)
  have e : ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - GlobalTheory.LevelComb.lift G g.val) a b +
      (((x' : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val) a b) -
      ((x' : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - GlobalTheory.LevelComb.lift G g'.val) a b =
      GlobalTheory.LevelComb.rho G (GlobalTheory.LevelComb.out (g'.val (GlobalTheory.LevelComb.pos G a) (GlobalTheory.LevelComb.pos G b)) -
        GlobalTheory.LevelComb.out (g.val (GlobalTheory.LevelComb.pos G a) (GlobalTheory.LevelComb.pos G b))) := by
    simp only [Matrix.sub_apply, GlobalTheory.LevelComb.lift, map_sub]; ring
  rw [e] at h
  have hm' := GlobalTheory.LevelComb.mem_of_rho_lt G h
  rw [← GlobalTheory.LevelComb.mk_out (g'.val _ _), ← GlobalTheory.LevelComb.mk_out (g.val _ _)]
  exact (Ideal.Quotient.eq.2 hm')
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_unique_of_maximal : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP) (x x' : G.S.P.J) (g g' : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)), G.Red x g → G.Red x' g' → GlobalTheory.StepData.MaxM ((x' : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val) → g' = g := by
  atlas_forward_decl GlobalTheory.LevelComb.red_uniq
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel

namespace GlobalTheory.ReadAtBase

theorem mat_read {k : Type} [CommRing k] {N Y : Type} [Fintype N] [DecidableEq N] [Fintype Y] [DecidableEq Y] (σ : N ≃ Y)
    (β' βi' W Mi M0 : Matrix N N k) (Fb : Matrix N Y k) (Fg : Matrix Y N k) (bs bi X : Matrix Y Y k)
    {Yy G : Matrix _ _ k} (h1 : β' * W * βi' = Mi * Yy * M0) (hY : Yy = Fb * G * Fg) (hG : G = bs * X * bi) (h2 : βi' * β' = 1) (h3 : M0 * Mi = 1)
    (h4 : Fg * Fb = 1) (h5 : bi * bs = 1) (h6 : β' = (Mi * Fb * bs).submatrix id σ) :
    W = X.submatrix σ σ := by
  subst hY hG
  have hs : ∀ (M : Matrix N N k) (P : Matrix N Y k), M * P.submatrix id σ = (M * P).submatrix id σ := fun M P => by
    ext i j; simp [Matrix.mul_apply]
  have hA : β' * W = β' * X.submatrix σ σ := by
    have e1 : β' * W = β' * W * βi' * β' := by rw [Matrix.mul_assoc (β' * W), h2, Matrix.mul_one]
    rw [e1, h1, h6, hs, Matrix.submatrix_mul_equiv _ _ _ σ]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc M0 Mi, h3, Matrix.one_mul, ← Matrix.mul_assoc Fg Fb, h4, Matrix.one_mul,
      h5, Matrix.mul_one]
  calc W = βi' * β' * W := by rw [h2, Matrix.one_mul]
    _ = βi' * β' * X.submatrix σ σ := by rw [Matrix.mul_assoc, hA, ← Matrix.mul_assoc]
    _ = X.submatrix σ σ := by rw [h2, Matrix.one_mul]

end GlobalTheory.ReadAtBase

namespace GlobalTheory.ReadAtBase

theorem map_mt_conj {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.LocMod.Place D k) (V : HSp D) (t y : GA D V) :
    (Formalism.L2.Theta.mt V (t⁻¹ * y * t)).map p.π =
      (Formalism.L2.Theta.mt V t⁻¹).map p.π * (Formalism.L2.Theta.mt V y).map p.π * (Formalism.L2.Theta.mt V t).map p.π := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul, Matrix.map_mul]

theorem map_mt_inv {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.LocMod.Place D k) (V : HSp D) (t : GA D V) :
    (Formalism.L2.Theta.mt V t).map p.π * (Formalism.L2.Theta.mt V t⁻¹).map p.π = 1 := by
  rw [← Matrix.map_mul]
  simp [Formalism.L2.Theta.mt]

theorem map_inv_mul {R k : Type} [CommRing R] [CommRing k] {n : ℕ} (f : R →+* k) (β : GL (Fin n) R) :
    (β⁻¹).val.map f * β.val.map f = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem bc_apply {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B) (g : GL (Fin n) A) (i j : Fin n) :
    (Formalism.UG.bc f g).val i j = f (g.val i j) := rfl

theorem intGL_apply {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (w : GL (Fin n) (Formalism.L2.Herm.intAf F E)) (i j : Fin n) :
    (intGL F E n w).val i j = (w.val i j : E ⊗[F] Formalism.L2.Herm.Af F) := rfl
end GlobalTheory.ReadAtBase

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.ReadAtBase.red_of_isLoc : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP) (hr : D.R.r ≤ (d.st 0).V.rank) (hc : 0 + (G.s + 1) = G.s + 1) (x : G.S.P.J) (y : GA D (d.st 0).V), (GlobalTheory.LocMod.ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) hc) y ((GlobalTheory.StepData.typeFrame G.S.ϖ (GlobalTheory.StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) hc)).conj (GlobalTheory.StepData.reGL (GlobalTheory.StepData.ixZero (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t)) (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k))) → Formalism.IndefR.Lev.finE (d.st 0).V ((d.t 0)⁻¹ * y * d.t 0) ∈ Formalism.L2.DIV.St (d.st 0).β → G.Red x (Formalism.L2.DIV.upperLeftBlock hr (Formalism.L2.DIV.redFn (d.st 0).β PP (Formalism.IndefR.Lev.finE (d.st 0).V ((d.t 0)⁻¹ * y * d.t 0)))) := by
  intro D u d τ PP G hr hc x y hL hSt
  obtain ⟨π', hπ, hred, -, -⟩ := GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D G.k G.q PP G.idem
  have hπ' : ∀ a, π' (toEAf D a) = (GlobalTheory.LocMod.ofSplit G.q).π a := hπ
  obtain ⟨w, hw⟩ := hSt
  rw [← hw, Formalism.L2.DIV.redFn_frGL]
  obtain ⟨e, he, hmv⟩ := G.frame 0 (G.s + 1) hc
  have hβ := GlobalTheory.LocMod.StepVec.map_eq_of_movedTo (GlobalTheory.LocMod.ofSplit G.q) (G.FY 0 (G.s + 1) hc) hπ' _ _ hmv
  have hn : (d.st 0).V.rank ≤ D.R.r := by
    have h1 := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, zero_mul, add_zero] at h1
    have h2 := G.hs
    unfold Formalism.BasicNotions.Ranks.r
    omega
  intro a b a' b' ha hb z hz
  have hrb : ((upperLeftBlock hr ((Formalism.UG.bc (resS D.host.F PP)) w)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) =
      (((Formalism.UG.bc (resS D.host.F PP)) w) : Matrix _ _ (kP PP)).submatrix (Fin.castLE hr) (Fin.castLE hr) := by
    refine upper_block_val_submatrix hr ?_
    intro i j hij
    exfalso
    have hi : blk2 D.R.r i = 0 := by simp [blk2, show i.val < D.R.r from lt_of_lt_of_le i.2 hn]
    rw [hi] at hij
    exact Nat.not_lt_zero _ hij
  rw [hrb] at hz
  have hpos : ∀ (c : Fin D.R.k ⊕ Fin (G.s + 1)) (c' : Fin D.R.r), c'.val = IndefiniteRowSideFullHecke.FramePositiveSum.framePos D.R.k (G.s + 1) c →
      Fin.castLE hr c' = e (StepData.ixZero _ _ c) := by
    intro c c' hc'
    ext
    rw [Fin.val_castLE, he, hc']
    rcases c with c | c <;> rfl
  rw [Matrix.submatrix_apply, hpos a a' ha, hpos b b' hb] at hz
  have e1 : frGL (d.st 0).β w = (d.st 0).β * Formalism.L2.DIV.intGL _ _ _ w * ((d.st 0).β)⁻¹ := rfl
  have e2 := congrArg Units.val (e1.symm.trans hw)
  rw [Units.val_mul, Units.val_mul] at e2
  have h1 := congrArg (Matrix.map · π') e2
  simp only [Matrix.map_mul] at h1
  have e4 : (finE (d.st 0).V ((d.t 0)⁻¹ * y * d.t 0)).val.map π' =
      (Formalism.L2.Theta.mt (d.st 0).V ((d.t 0)⁻¹ * y * d.t 0)).map (GlobalTheory.LocMod.ofSplit G.q).π := by
    ext i j
    exact hπ' _
  have h1' := (h1.trans e4).trans (GlobalTheory.ReadAtBase.map_mt_conj (GlobalTheory.LocMod.ofSplit G.q) _ (d.t 0) y)
  have hG : ((StepData.typeFrame G.S.ϖ (StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) hc)).conj
      ((StepData.reGL (StepData.ixZero (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t))) x)).val =
      ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) hc).val *
        (StepData.reGL (StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) hc)
          (StepData.reGL (StepData.ixZero (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t)) (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k))).val *
        (((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) hc)⁻¹).val := rfl
  have hW := GlobalTheory.ReadAtBase.mat_read ((e.symm).trans (StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) hc)) _ _ _ _ _ _ _ _ _ _ h1' hL.2
    hG (GlobalTheory.ReadAtBase.map_inv_mul _ _)
    (GlobalTheory.ReadAtBase.map_mt_inv _ _ _) (G.FY 0 (G.s + 1) hc).γβ (Units.inv_mul _) hβ
  have h := congrFun (congrFun hW (e (StepData.ixZero _ _ a))) (e (StepData.ixZero _ _ b))
  simp only [Matrix.map_apply, Matrix.submatrix_apply, Equiv.trans_apply, Equiv.symm_apply_apply, StepData.reGL_val] at h
  simp only [GlobalTheory.ReadAtBase.intGL_apply] at h
  simp only [GlobalTheory.ReadAtBase.bc_apply] at hz
  have hz0 : resS D.host.F PP (w.val (e (StepData.ixZero _ _ a)) (e (StepData.ixZero _ _ b)) - oToS D.host.F D.host.E z) = 0 := by
    rw [map_sub, resS_oToS, hz]
    exact sub_self _
  have hv := (hred.ker _).1 hz0
  simp only [RingHom.comp_apply, Subring.coe_subtype, AddSubgroupClass.coe_sub, map_sub, h] at hv
  have e8 : π' ((oToS _ _ z : Formalism.L2.Herm.intAf D.host.F D.host.E) : Datum.EAf D) =
      (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) := hπ' (incA D (z : D.host.E))
  rw [e8] at hv
  exact hv
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_zero_type_frame_locality : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP) (hr : D.R.r ≤ (d.st 0).V.rank) (hc : 0 + (G.s + 1) = G.s + 1) (x : G.S.P.J) (y : GA D (d.st 0).V), (GlobalTheory.LocMod.ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) hc) y ((GlobalTheory.StepData.typeFrame G.S.ϖ (GlobalTheory.StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) hc)).conj (GlobalTheory.StepData.reGL (GlobalTheory.StepData.ixZero (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t)) (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k))) → Formalism.IndefR.Lev.finE (d.st 0).V ((d.t 0)⁻¹ * y * d.t 0) ∈ Formalism.L2.DIV.St (d.st 0).β → G.Red x (Formalism.L2.DIV.upperLeftBlock hr (Formalism.L2.DIV.redFn (d.st 0).β PP (Formalism.IndefR.Lev.finE (d.st 0).V ((d.t 0)⁻¹ * y * d.t 0)))) := by
  atlas_forward_decl GlobalTheory.ReadAtBase.red_of_isLoc
end

section
section
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.SymDec
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem intM_adjugate {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n k} (h : IntM A) : IntM A.adjugate := by
  let B : Matrix n n 𝒪[k] := fun i j => ⟨A i j, h i j⟩
  have hB : A = (algebraMap 𝒪[k] k).mapMatrix B := by ext i j; rfl
  intro i j
  rw [hB, ← RingHom.map_adjugate]
  exact (B.adjugate i j).2

theorem mem_KO_of_intM_det {n : Type} [Fintype n] [DecidableEq n] {g : GL n k} (h : IntM g.val) (hd : g.val.det = 1) :
    g ∈ KO k n := by
  refine mem_KO.2 ⟨h, ?_⟩
  have : (g⁻¹).val = g.val.adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, hd]; simp
  rw [this]; exact intM_adjugate h
end

section Frame
variable {k : Type} [Field k] {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def dg (ϖ : kˣ) : n ⊕ Fin c → k := Sum.elim (fun _ => 1) (fun i => (ϖ : k) ^ (i.val + 1))

theorem dg_ne_zero (ϖ : kˣ) (r : n ⊕ Fin c) : dg ϖ r ≠ 0 := by
  rcases r with r | r <;> simp [dg]

theorem typeFrame_bas_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    (typeFrame ϖ ord).bas.val = diagonal (dg ϖ) := by
  ext (i | i) (j | j) <;> simp [typeFrame, embA, SplitFlip.diagGL, dg, diagonal, fromBlocks, Matrix.one_apply]

theorem typeFrame_bas_inv_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    ((typeFrame ϖ ord).bas⁻¹).val = diagonal fun r => (dg ϖ r)⁻¹ := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [typeFrame_bas_val, diagonal_mul_diagonal]
  rw [← diagonal_one]; congr 1; funext r; exact mul_inv_cancel₀ (dg_ne_zero ϖ r)

theorem conj_entry [Fintype ι] [DecidableEq ι] (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) (g : GL ι k) (r s : n ⊕ Fin c) :
    ((typeFrame ϖ ord).conj g).val r s = dg ϖ r * g.val (ord.symm r) (ord.symm s) * (dg ϖ s)⁻¹ := by
  rw [LatFrame.conj_apply, Units.val_mul, Units.val_mul, typeFrame_bas_inv_val, typeFrame_bas_val,
    mul_diagonal, diagonal_mul, reGL_val]
  rfl
end Frame

section Zero
variable {k : Type} [Field k] {κ c : ℕ} (t : Type) [Fintype t] [DecidableEq t]

def ordZ (hc : 0 + c = c) : Fin κ ⊕ Fin c ≃ XIx (Fin κ) t 0 ⊕ Fin c :=
  (ixZero (Fin κ ⊕ Fin c) t).trans (stdOrd (Fin κ) t 0 c hc)

theorem ordZ_inl (hc : 0 + c = c) (i : Fin κ) : ordZ t hc (Sum.inl i) = Sum.inl (Sum.inl (Sum.inl i)) := rfl

theorem ordZ_inr (hc : 0 + c = c) (i : Fin c) : ordZ (κ := κ) t hc (Sum.inr i) = Sum.inr i := by
  have h := standardOrderExtendedBasis_apply_low_block (Fin κ) t 0 c hc i
  simp only [Fin.eta] at h
  exact h

def epsZ : Fin κ ≃ XIx (Fin κ) t 0 :=
  (Equiv.sumEmpty (Fin κ) (Fin 0)).symm.trans (Equiv.sumEmpty (Fin κ ⊕ Fin 0) (Fin 0 × t)).symm

theorem lev_ordZ_symm (hc : 0 + c = c) (p : ℕ) (z : XIx (Fin κ) t 0 ⊕ Fin c) :
    lev p ((ordZ t hc).symm z) = lev p z := by
  obtain ⟨w, rfl⟩ := (ordZ t hc).surjective z
  rw [Equiv.symm_apply_apply]
  rcases w with i | i
  · rw [ordZ_inl]; rfl
  · rw [ordZ_inr]; rfl

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem conj_reGL_val (ϖ : kˣ) (hc : 0 + c = c) (g : GL (Fin κ ⊕ Fin c) k) (r s : XIx (Fin κ) t 0 ⊕ Fin c) :
    ((typeFrame ϖ (stdOrd (Fin κ) t 0 c hc)).conj (reGL (ixZero (Fin κ ⊕ Fin c) t) g)).val r s =
      dg ϖ r * g.val ((ordZ t hc).symm r) ((ordZ t hc).symm s) * (dg ϖ s)⁻¹ := by
  rw [conj_entry, reGL_val]; rfl

theorem conj_inN (ϖ : kˣ) (hc : 0 + c = c) (p : ℕ) {g : GL (Fin κ ⊕ Fin c) k} (hg : InN p g) :
    InN p ((typeFrame ϖ (stdOrd (Fin κ) t 0 c hc)).conj (reGL (ixZero (Fin κ ⊕ Fin c) t) g)) := by
  intro r s hrs
  rw [conj_reGL_val, hg _ _ (by rw [lev_ordZ_symm, lev_ordZ_symm]; exact hrs)]
  by_cases h : r = s
  · subst h; simp [Matrix.one_apply, mul_inv_cancel₀ (dg_ne_zero ϖ r)]
  · have h' : (ordZ t hc).symm r ≠ (ordZ t hc).symm s := fun e => h ((ordZ t hc).symm.injective e)
    simp [Matrix.one_apply, h, h']

theorem conj_embX (ϖ : kˣ) (hc : 0 + c = c) (γ : GL (Fin κ) k) :
    (typeFrame ϖ (stdOrd (Fin κ) t 0 c hc)).conj (reGL (ixZero (Fin κ ⊕ Fin c) t) (embX c γ)) =
      embX c (reGL (epsZ t) γ) := by
  have hs1 : ∀ i : Fin κ, (ordZ t hc).symm (Sum.inl (Sum.inl (Sum.inl i))) = Sum.inl i := fun i =>
    (ordZ t hc).symm_apply_eq.2 (ordZ_inl t hc i).symm
  have hs2 : ∀ i : Fin c, (ordZ t hc).symm (Sum.inr i) = Sum.inr i := fun i =>
    (ordZ t hc).symm_apply_eq.2 (ordZ_inr (κ := κ) t hc i).symm
  ext r s
  rw [conj_reGL_val, Radical.embX_val, Radical.embX_val, reGL_val]
  rcases r with ((i | i) | ⟨i, _⟩) | i
  · rcases s with ((j | j) | ⟨j, _⟩) | j
    · rw [hs1, hs1]; simp [dg]; rfl
    · exact j.elim0
    · exact j.elim0
    · rw [hs1, hs2]; simp [dg]
  · exact i.elim0
  · exact i.elim0
  · rcases s with ((j | j) | ⟨j, _⟩) | j
    · rw [hs2, hs1]; simp [dg]
    · exact j.elim0
    · exact j.elim0
    · rw [hs2, hs2]
      by_cases h : i = j
      · subst h; simp [dg, Matrix.one_apply]
      · simp [dg, Matrix.one_apply, h]
end Zero

end GlobalTheory.SymDec

open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem GlobalTheory.SymChain.SymData.exists_N_mul_embX_congr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
    (hc : 0 + (s + 1) = s + 1) (x : S.P.J), ∃ (a b : S.P.J) (γ : GL (GlobalTheory.StepData.XIx (Fin κ) t 0) k),
    (GlobalTheory.StepData.typeFrame S.ϖ (GlobalTheory.StepData.stdOrd (Fin κ) t 0 (s + 1) hc)).conj
      (GlobalTheory.StepData.reGL (GlobalTheory.StepData.ixZero (Fin κ ⊕ Fin (s + 1)) t) (a : GL (Fin κ ⊕ Fin (s + 1)) k)) ∈
        GlobalTheory.RootEx.N k (GlobalTheory.StepData.XIx (Fin κ) t 0) (s + 1) (S.ρ + 1) ∧
    (GlobalTheory.StepData.typeFrame S.ϖ (GlobalTheory.StepData.stdOrd (Fin κ) t 0 (s + 1) hc)).conj
      (GlobalTheory.StepData.reGL (GlobalTheory.StepData.ixZero (Fin κ ⊕ Fin (s + 1)) t) (b : GL (Fin κ ⊕ Fin (s + 1)) k)) =
        GlobalTheory.RootEx.embX (s + 1) γ ∧
    GlobalTheory.StepData.MaxM (((a * b : S.P.J) : GL (Fin κ ⊕ Fin (s + 1)) k).val - (x : GL (Fin κ ⊕ Fin (s + 1)) k).val) := by
  classical
  intro k _ _ _ _ s κ S t _ _ hc x
  have hx := (SymData.mem_J_iff_pattern k s κ S x).1 x.2
  let M : Matrix (Fin κ ⊕ Fin (s + 1)) (Fin κ ⊕ Fin (s + 1)) k := fun a b =>
    if FreeTop S.ρ a b then (x : GL _ k).val a b else (1 : Matrix _ _ k) a b
  have hM : MaxM (M - (x : GL _ k).val) := by
    intro a b
    rw [Matrix.sub_apply]
    simp only [M]
    split_ifs with h
    · simp
    · rw [← neg_sub, Valuation.map_neg]; exact hx.2 a b h
  obtain ⟨x', hx'J, hx'M⟩ := S.P.exists_of_congr x.2 hM
  obtain ⟨u, hu, γ₀, hγ₀, e⟩ := GlobalTheory.SymPattern.exists_of_pat S.ρ x' (fun a b hab => by
    rw [hx'M]; simp [M, hab])
  have hγv : ∀ i j, γ₀.val i j = x'.val (Sum.inl i) (Sum.inl j) := by
    intro i j
    rw [e, Units.val_mul, Radical.embX_val, GlobalTheory.SymPattern.mul_fromBlocks_inl]
    have e1 : ∀ t, u.val (Sum.inl i) (Sum.inl t) = (1 : Matrix (Fin κ) (Fin κ) k) i t := by
      intro t; rw [hu _ _ (by simp [lev])]; simp [Matrix.one_apply]
    simp only [e1]; rw [← Matrix.mul_apply, Matrix.one_mul]
  have hxInt := intM_of_mem_KO hx.1
  have hγInt : IntM γ₀.val := by
    intro i j; rw [hγv, hx'M]; simp only [M]; split_ifs
    · exact hxInt _ _
    · exact intM_one _ _
  have hdet : γ₀.val.det = 1 := Radical.Uni.det (b := Fin.val) hγ₀
  have hbKO : embX (s + 1) γ₀ ∈ KO k (Fin κ ⊕ Fin (s + 1)) := by
    refine GlobalTheory.SymDec.mem_KO_of_intM_det ?_ ?_
    · rw [Radical.embX_val]
      exact intM_fromBlocks.2 ⟨hγInt, intM_zero, intM_zero, intM_one⟩
    · rw [Radical.embX_val, det_fromBlocks_zero₂₁, det_one, mul_one, hdet]
  have hbJ : embX (s + 1) γ₀ ∈ S.P.J := by
    refine (SymData.mem_J_iff_pattern k s κ S _).2 ⟨hbKO, fun a b hab => ?_⟩
    have h1 : InN (S.ρ + 1) (1 : GL (Fin κ ⊕ Fin (s + 1)) k) := fun r s _ => rfl
    have := GlobalTheory.SymPattern.pat_of_mul S.ρ 1 h1 γ₀ hγ₀ a b hab
    rw [one_mul] at this
    rw [this, sub_self, map_zero]; exact zero_lt_one
  have hue : u = x' * (embX (s + 1) γ₀)⁻¹ := by rw [e]; group
  have huJ : u ∈ S.P.J := by rw [hue]; exact S.P.J.mul_mem hx'J (S.P.J.inv_mem hbJ)
  refine ⟨⟨u, huJ⟩, ⟨embX (s + 1) γ₀, hbJ⟩, reGL (GlobalTheory.SymDec.epsZ t) γ₀, ?_, ?_, ?_⟩
  · exact (Radical.mem_N_iff _).2 (GlobalTheory.SymDec.conj_inN t S.ϖ hc (S.ρ + 1) hu)
  · exact GlobalTheory.SymDec.conj_embX t S.ϖ hc γ₀
  · change MaxM ((u * embX (s + 1) γ₀).val - (x : GL _ k).val)
    rw [← e, hx'M]; exact hM
end
end

open ValuativeRel Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_frame_conjugation_decomposition : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (hc : 0 + (s + 1) = s + 1) (x : S.P.J), ∃ (a b : S.P.J) (γ : GL (GlobalTheory.StepData.XIx (Fin κ) t 0) k), (GlobalTheory.StepData.typeFrame S.ϖ (GlobalTheory.StepData.stdOrd (Fin κ) t 0 (s + 1) hc)).conj (GlobalTheory.StepData.reGL (GlobalTheory.StepData.ixZero (Fin κ ⊕ Fin (s + 1)) t) (a : GL (Fin κ ⊕ Fin (s + 1)) k)) ∈ GlobalTheory.RootEx.N k (GlobalTheory.StepData.XIx (Fin κ) t 0) (s + 1) (S.ρ + 1) ∧ (GlobalTheory.StepData.typeFrame S.ϖ (GlobalTheory.StepData.stdOrd (Fin κ) t 0 (s + 1) hc)).conj (GlobalTheory.StepData.reGL (GlobalTheory.StepData.ixZero (Fin κ ⊕ Fin (s + 1)) t) (b : GL (Fin κ ⊕ Fin (s + 1)) k)) = GlobalTheory.RootEx.embX (s + 1) γ ∧ GlobalTheory.StepData.MaxM (((a * b : S.P.J) : GL (Fin κ ⊕ Fin (s + 1)) k).val - (x : GL (Fin κ ⊕ Fin (s + 1)) k).val) := by
  atlas_forward_decl GlobalTheory.SymChain.SymData.exists_N_mul_embX_congr
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.MemMatch

open GlobalTheory.LocMod GlobalTheory.LocGrp in

theorem isLoc_embA {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {n : Type} [Fintype n] [DecidableEq n] {c ρ : ℕ} (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n)
    (F : Frame k B.V.rank (n ⊕ Fin c)) (hF : p.IsBesFrame B s FA F) {h : GA D B.A} {g₀ : GL n k} (hh : p.IsLoc FA h g₀) :
    p.IsLoc F (embA B.d B.o h) (GlobalTheory.RootEx.embX c g₀) := by
  obtain ⟨rfl, h0, hX, hz, hY⟩ := hF
  have eA : Formalism.L2.Theta.mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jA) = B.d.j0 ⬝ B.o.jA ⬝ Formalism.L2.Theta.mt B.A h := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jA, Matrix.mul_assoc]
  have eB : Formalism.L2.Theta.mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jB) = B.d.j0 ⬝ B.o.jB := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jB, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have rA : B.d.j0 ⬝ B.o.jA = rat (B.d.i₀ * B.o.iA) := (rat_mul _ _).symm
  have rB : B.d.j0 ⬝ B.o.jB = rat (B.d.i₀ * B.o.iB) := (rat_mul _ _).symm
  rw [rA] at eA
  rw [rB] at eB
  refine ⟨suppAt_wittLeviEmbedding B.d (suppAt_emb B.o hh.1),
    eq_embX F _ g₀ ((rat (B.d.i₀ * B.o.iA)).map p.π * FA.β) h0 (intertwine p eA hh) fun j => ?_⟩
  rcases lt_trichotomy j.val ρ with hj | hj | hj
  · exact fix_col (map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclX _)) _ ⟨j.val, hj⟩ (hX _ j rfl)
  · refine fix_vec (map_fix p eB) s (Witness.prH p ∘ B.ζ) fun r => (hz j hj r).trans (congrArg (s * ·) ?_)
    rw [vecB, Matrix.mulVec_mulVec]
    exact RingHom.map_mulVec (Witness.prH p) _ _ r
  · exact fix_col (map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclY _)) _ ⟨2 * ρ - j.val, by omega⟩ (hY _ j (by simp only; omega))

theorem st_of_levS {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {κ : GA D V}
    (h : κ ∈ levS V β L) : κ ∈ GfC V ∧ finE V κ ∈ St β := by
  obtain ⟨hf, hl⟩ := h
  change finE V κ ∈ lev _ _ _ _ at hl
  rw [mem_lev, mem_parLev] at hl
  exact ⟨hf, hl.1.2.1⟩

open GlobalTheory.LocMod in

theorem local_gen {D : D7} {u : D.what₂.Word} (d : GlobalTheory.SeeSaw.Dat D u)
    (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (cG) (G : ∀ PP : d.c.Pg, GAt d τ PP.1)
    (hB : d.Base) (hG : PinGBy G cG) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hr : D.R.r ≤ (d.st 0).V.rank) (PP : d.c.Pg)
    (g : GL (Fin D.R.r) (kP PP.1)) (hg : ∃ x, (G PP).Red x g) :
    ∃ n ∈ flagN (d.bes 0 D.R.rS h0).d, ∃ h ∈ GfC (D.sp.X 0), (d.t 0)⁻¹ * n * d.t 0 ∈ d.lev 0 ∧
      (d.t 0)⁻¹ * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o h * d.t 0 ∈ d.lev 0 ∧
      upperLeftBlock hr (redFn (d.st 0).β PP.1 (finE (d.st 0).V
        ((d.t 0)⁻¹ * (n * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o h) * d.t 0))) = g := by
  obtain ⟨x, hx⟩ := hg
  have hc : 0 + ((G PP).s + 1) = (G PP).s + 1 := zero_add _
  have hF := (G PP).bes 0 D.R.rS h0 _ hc
  have hρ : (G PP).S.ρ = D.R.rS := by
    have h1 := hF.1
    have h2 := (G PP).S.odd
    omega
  obtain ⟨a, b, γ, ha, hb, hab⟩ := GlobalTheory.T.type_frame_conjugation_decomposition (G PP).k (G PP).s D.R.k (G PP).S (Fin D.R.t) hc x
  rw [hρ] at ha
  obtain ⟨n, hn⟩ := Witness.exists_isLoc (ofSplit (G PP).q) ((G PP).FY 0 _ hc)
    ((GlobalTheory.StepData.typeFrame (G PP).S.ϖ (GlobalTheory.StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 ((G PP).s + 1) hc)).conj
      (GlobalTheory.StepData.reGL (GlobalTheory.StepData.ixZero (Fin D.R.k ⊕ Fin ((G PP).s + 1)) (Fin D.R.t)) a.1))
  obtain ⟨h, hh⟩ := Witness.exists_isLoc (ofSplit (G PP).q) ((G PP).FX 0 (by omega)) γ
  have he := isLoc_embA (ofSplit (G PP).q) (d.B 0 D.R.rS h0) _ _ _ hF hh
  rw [← hb] at he
  have hJ : ∀ y : (G PP).S.P.J,
      (GlobalTheory.StepData.typeFrame (G PP).S.ϖ (GlobalTheory.StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 ((G PP).s + 1) hc)).conj
        (GlobalTheory.StepData.reGL (GlobalTheory.StepData.ixZero (Fin D.R.k ⊕ Fin ((G PP).s + 1)) (Fin D.R.t)) y.1) ∈
        (((G PP).S.T (Fin D.R.t)).lev 0 _ hc).J := by
    intro y
    refine GlobalTheory.StepData.Level.mem_map.2 ?_
    rw [MulEquiv.symm_apply_apply]
    change (GlobalTheory.StepData.reGL (GlobalTheory.StepData.ixZero _ _)).symm _ ∈ (G PP).S.P.J
    rw [MulEquiv.symm_apply_apply]
    exact y.2
  have hLev := GlobalTheory.T.pinned_local_groups_have_level D u d τ cG G hB hG PP
  have l1 := hLev 0 _ hc _ _ hn (hJ a)
  have l2 := hLev 0 _ hc _ _ he (hJ b)
  have hm := GlobalTheory.LocGrp.isLoc_mul (ofSplit (G PP).q) hn he
  rw [← map_mul, ← map_mul] at hm
  have l3 := hLev 0 _ hc _ _ hm (hJ (a * b))
  refine ⟨n, GlobalTheory.LocGrp.mem_flagN_of_mem_N (ofSplit (G PP).q) (d.B 0 D.R.rS h0) _ _ _ hF n _ ha hn, h,
    GlobalTheory.WeilProduct.mem_GfC_of_suppAt (G PP).q.split hh.1, l1, l2, ?_⟩
  exact GlobalTheory.T.reduction_unique_of_maximal D u d τ PP.1 (G PP) x (a * b) g _ hx
    (GlobalTheory.T.level_zero_type_frame_locality D u d τ PP.1 (G PP) hr hc (a * b) _ hm (st_of_levS l3).2) hab

theorem eq_of_lev_eq {D : D7} {ρ : ℕ} {V A V₀ V₀' L L' : HSp D} {d : HypDec V V₀ ρ} {d' : HypDec V V₀' ρ} {o : OrthDec V₀ A L}
    {o' : OrthDec V₀' A L'} {ζ ζ' l l' c c' vA vA' vN vN'}
    (h : (⟨V, V₀, A, L, d, o, ζ, l, c, vA, vN⟩ : BesLev D ρ) = ⟨V, V₀', A, L', d', o', ζ', l', c', vA', vN'⟩) :
    flagN d = flagN d' ∧ embA d o = embA d' o' := by
  cases h
  exact ⟨rfl, rfl⟩

theorem kset_iff_st {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    {β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)} (hβ : IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0))
    (κ : GA D (D.sp.Y 0)) : (iotaX X h κ).2 ∈ X.B.I.Kset ↔ finE (D.sp.Y 0) κ ∈ St β := by
  have key : ∀ (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D),
      (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D κ)).2 ∈ I.Kset ↔ finE (D.sp.Y 0) κ ∈ St β := by
    intro I hI
    subst hI
    have hL : (Formalism.L2.SG.InstExistsPf.instOf D).L = Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0 :=
      Formalism.L2.SG.InstExistsPf.Lv_eq_map D
    have e := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
    have e2 : Lev.finE (D.sp.Y 0) κ = ((Formalism.IndefR.RationalEmbedding.iota D κ).2.1 : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) :=
      (congrArg (Lev.finE (D.sp.Y 0)) ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ)).symm.trans e
    have hx := GlobalTheory.FlagBasis.kset_iff (Formalism.L2.SG.InstExistsPf.instOf D) (β := β) (hL ▸ hβ) (Formalism.IndefR.RationalEmbedding.iota D κ).2
    generalize Lev.finE (D.sp.Y 0) κ = y at e2 ⊢
    subst e2
    exact hx
  exact key X.B.I h

theorem iotaX_conj {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (x : X.B.I.Gf)
    (y : GA D (D.sp.Y 0)) :
    (iotaX X h (((iotaX X h).symm (1, x))⁻¹ * y * (iotaX X h).symm (1, x))).2 = x⁻¹ * (iotaX X h y).2 * x := by
  rw [map_mul, map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply]
  rfl

theorem flag_mem_K_two {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A) {n : GA D (D.sp.Y 0)} (hn : n ∈ flagN B.d)
    (hK : (X.xu u)⁻¹ * (iotaX X h n).2 * X.xu u ∈ X.B.I.Kset) : (X.xu u)⁻¹ * (iotaX X h n).2 * X.xu u ∈ X.K2 := by
  refine MassDataMassesW.NLev.nLevel_holds X u _ ((B.tieN n).1 hn).2 ?_
  have := MassDataMassesW.NLev.Kset_mul (MassDataMassesW.NLev.Kset_mul (X.xu_K u) hK) (MassDataMassesW.NLev.Kset_inv (X.xu_K u))
  rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_assoc, mul_inv_cancel, mul_one] at this

theorem column_mem_K_two {D : D7} {u : D.what₂.Word} {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u} (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u)
    (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hE : IdE S.X) (hX : LevX (F₀ u) d h0) (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0))
    (hA : B.Adapted (S.tr u).wt) {a₀ : GA D (D.sp.X 0)} (ha₀ : IsTransportAdelicCorrection (S.tr u) a₀) {h : GA D (D.sp.X 0)}
    (hf : h ∈ GfC (D.sp.X 0))
    (hl : (d.t 0)⁻¹ * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o h * d.t 0 ∈ d.lev 0) :
    (S.X.xu u)⁻¹ * (iotaX S.X S.inst (embA B.d B.o (a₀ * h * a₀⁻¹))).2 * S.X.xu u ∈ S.X.K2 := by
  let φ : GA D (D.sp.X 0) → Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := fun a =>
    ⟨GlobalTheory.AdForm.Model.finGL (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a,
      GlobalTheory.AdForm.Model.finGL_mem (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⟩
  have hmul : ∀ a b, φ (a * b) = φ a * φ b := fun a b => Subtype.ext (Units.ext (unitaryAdelicPointFiniteMatrix_base_space_mul a b))
  have e0 : φ a₀ = (S.tr u).h0 := Subtype.ext (Units.ext ha₀.2)
  have e1 : (S.tr u).h0⁻¹ * φ (a₀ * h * a₀⁻¹) * (S.tr u).h0 = φ h := by
    rw [← e0, mul_assoc, ← hmul, inv_mul_cancel_right, hmul, inv_mul_cancel_left]
  have hU := (hX h hf (φ h) rfl).1.2 hl
  have hR := GlobalTheory.T.secondModel_finitePart_frameActionMatrix D S.X S.inst u d.c.ψ B (F₀ u) (S.tr u) hE hA (a₀ * h * a₀⁻¹)
  have := ((S.lev u).2 (B.toH (a₀ * h * a₀⁻¹)).2 (φ (a₀ * h * a₀⁻¹)) hR).1.2 (by rw [e1]; exact hU)
  exact this

theorem conj_mem_iff_isPat {K : Type} [CommRing K] [Finite K] {r n ρ κ : ℕ} (hr : r ≤ n) (hn : n ≤ r) (e : r = κ + (2 * ρ + 1))
    (m : GL (Fin n) K) (h : ∀ g : GL (Fin r) K, GlobalTheory.SymRes.IsPat ρ κ g → ∃ y, upperLeftBlock hr y = g ∧ m * y * m⁻¹ ∈ unipSym K n ρ κ)
    (y : GL (Fin n) K) : m * y * m⁻¹ ∈ unipSym K n ρ κ ↔ GlobalTheory.SymRes.IsPat ρ κ (upperLeftBlock hr y) := by
  obtain rfl : r = n := le_antisymm hr hn
  have h' : ∀ g : GL (Fin r) K, GlobalTheory.SymRes.IsPat ρ κ g → m * g * m⁻¹ ∈ unipSym K r ρ κ := fun g hg => by
    obtain ⟨y, hy, hy'⟩ := h g hg
    rw [GlobalTheory.SeeConjRead.restrictedBlock_self_apply] at hy
    exact hy ▸ hy'
  rw [GlobalTheory.SeeConjRead.restrictedBlock_self_apply]
  exact ⟨GlobalTheory.T.conjugate_symmetric_unipotent_pattern K r ρ κ e m h' y, h' y⟩

theorem block_frame_conjugation_identity {G : Type} [Group G] (x e t n : G) : x⁻¹ * e * t * (t⁻¹ * n * t) * (x⁻¹ * e * t)⁻¹ = x⁻¹ * (e * n * e⁻¹) * x := by
  group

theorem conj_central_mul_cancel {G : Type} [Group G] (b a h : G) (ha : a ∈ Subgroup.center G) : b * a * h * (b * a)⁻¹ = b * h * b⁻¹ := by
  rw [mul_assoc b a, ← Subgroup.mem_center_iff.1 ha h]; group

theorem mul_aux {G : Type} [Group G] (t x y : G) : t⁻¹ * (x * y) * t = (t⁻¹ * x * t) * (t⁻¹ * y * t) := by group

theorem conj_mul_distrib {G : Type} [Group G] (t x y : G) : t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group

theorem generator_mem_K_two {D : D7} {u : D.what₂.Word} {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u} (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u)
    (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (cG) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d τ PP.1)
    (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hE : IdE S.X) (hB : d.Base)
    (hG : GlobalTheory.LocMod.PinGBy G cG) (hX : LevX (F₀ u) d h0) (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0))
    (hBl : B.lev = d.B 0 D.R.rS h0) (hA : B.Adapted (S.tr u).wt) (a₀ : GA D (D.sp.X 0)) (ha₀ : IsTransportAdelicCorrection (S.tr u) a₀)
    (a : GA D (D.sp.X 0)) (haz : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t₀ : GA D (D.sp.Y 0)) (ht₀ : t₀ = d.t 0) (t : GA D (D.sp.Y 0)) (ht' : t = ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * t₀)
    (hmove : ∀ y ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) y ∈ St d.bot.β → (iotaX S.X S.inst (t * y * t⁻¹)).2 ∈ S.X.B.I.Kset)
    (hr : D.R.r ≤ (D.sp.Y 0).rank) (PP : d.c.Pg) (g : GL (Fin D.R.r) (kP PP.1)) (hg : ∃ x, (G PP).Red x g) :
    ∃ y ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) y ∈ St d.bot.β ∧ upperLeftBlock hr (redFn d.bot.β PP.1 (finE (D.sp.Y 0) y)) = g ∧
      (iotaX S.X S.inst (t * y * t⁻¹)).2 ∈ S.X.K2 := by
  obtain ⟨eN, eA⟩ := eq_of_lev_eq hBl
  have H : ∃ n : GA D (D.sp.Y 0), n ∈ flagN B.d ∧ ∃ h ∈ GfC (D.sp.X 0), t₀⁻¹ * n * t₀ ∈ levS (D.sp.Y 0) d.bot.β d.bot.L ∧
      t₀⁻¹ * embA B.d B.o h * t₀ ∈ levS (D.sp.Y 0) d.bot.β d.bot.L ∧
      upperLeftBlock hr (redFn d.bot.β PP.1 (finE (D.sp.Y 0) (t₀⁻¹ * (n * embA B.d B.o h) * t₀))) = g := by
    rw [eN, eA]
    subst ht₀
    exact local_gen d τ cG G hB hG h0 hr PP g hg
  obtain ⟨n, hnB, h, hh, l1, l2, hg'⟩ := H
  have k2 := column_mem_K_two S d h0 hE hX B hA ha₀ hh (by rw [eA] at l2; subst ht₀; exact l2)
  have s1 := st_of_levS l1
  have s2 := st_of_levS l2
  have c1 : t * (t₀⁻¹ * n * t₀) * t⁻¹ = ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ *
      (embA B.d B.o (a₀ * a) * n * (embA B.d B.o (a₀ * a))⁻¹) * (iotaX S.X S.inst).symm (1, S.X.xu u) := by
    rw [ht']; exact block_frame_conjugation_identity _ _ _ _
  have c2 : t * (t₀⁻¹ * embA B.d B.o h * t₀) * t⁻¹ = ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ *
      embA B.d B.o (a₀ * h * a₀⁻¹) * (iotaX S.X S.inst).symm (1, S.X.xu u) := by
    rw [← conj_central_mul_cancel a₀ a h haz, map_mul (embA B.d B.o) _ (a₀ * a)⁻¹, map_mul (embA B.d B.o) (a₀ * a) h, map_inv, ht']
    exact block_frame_conjugation_identity _ _ _ _
  have k1 : (iotaX S.X S.inst (t * (t₀⁻¹ * n * t₀) * t⁻¹)).2 ∈ S.X.K2 := by
    have := hmove _ s1.1 s1.2
    rw [c1, iotaX_conj] at this ⊢
    exact flag_mem_K_two B (GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D _ _ _ B.d n hnB (B.o.emb (a₀ * a, 1))) this
  have k2' : (iotaX S.X S.inst (t * (t₀⁻¹ * embA B.d B.o h * t₀) * t⁻¹)).2 ∈ S.X.K2 := by
    rw [c2, iotaX_conj]; exact k2
  have e3 : t₀⁻¹ * (n * embA B.d B.o h) * t₀ = (t₀⁻¹ * n * t₀) * (t₀⁻¹ * embA B.d B.o h * t₀) := mul_aux _ _ _
  refine ⟨_, ?_, ?_, hg', ?_⟩
  · rw [e3]; exact mul_mem s1.1 s2.1
  · rw [e3, map_mul]; exact mul_mem s1.2 s2.2
  · rw [e3, conj_mul_distrib, map_mul]
    exact S.Y.hK.2.1 _ k1 _ k2'

theorem mem_iff {D : D7} {u : D.what₂.Word} {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u} (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u)
    (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (cG) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d τ PP.1)
    (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hE : IdE S.X) (hB : d.Base) (hT : GlobalTheory.Core.Mi.IsTypePlaces d.c.Pg)
    (hG : GlobalTheory.LocMod.PinGBy G cG) (hX : LevX (F₀ u) d h0) (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0))
    (hBl : B.lev = d.B 0 D.R.rS h0) (hA : B.Adapted (S.tr u).wt) (a₀ : GA D (D.sp.X 0)) (ha₀ : IsTransportAdelicCorrection (S.tr u) a₀)
    (a : GA D (D.sp.X 0)) (haf : a ∈ GfC (D.sp.X 0)) (haz : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t : GA D (D.sp.Y 0)) (ht : t = ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0))
    (hSt : ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) t * d.bot.β) →
      (iotaX S.X S.inst κ).2 ∈ S.X.B.I.Kset)
    (hr : D.R.r ≤ (D.sp.Y 0).rank) (κ : GA D (D.sp.Y 0)) (hκ : κ ∈ GfC (D.sp.Y 0))
    (hκS : finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) t * d.bot.β)) :
    (iotaX S.X S.inst κ).2 ∈ S.X.K2 ↔
      (fun PP : d.c.Pg => upperLeftBlock hr (redFn (finE (D.sp.Y 0) t * d.bot.β) PP.1 (finE (D.sp.Y 0) κ))) ∈ d.c.P.H := by
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hrk : (D.sp.Y 0).rank = D.R.rankY 0 := (hB.st 0 hm).rank
  have hn : (D.sp.Y 0).rank ≤ D.R.r := by rw [hrk]; simp [Formalism.BasicNotions.Ranks.rankY]
  have hre : D.R.r = D.R.k + (2 * D.R.rS + 1) := by unfold Ranks.r; omega
  obtain ⟨N, hN, -⟩ := (hB.st 0 hm).base
  obtain ⟨-, ψ0, hψ, -⟩ := GlobalTheory.Core.Mi.PinModel.exists_isSymLev (D := D) d.c.Pg
  obtain ⟨β₀, hβ₀, hK⟩ := GlobalTheory.SeeConjRead.read_fin S.X S.inst d.c.Pg hT (GlobalTheory.T.genusTypePlaceSet_not_conjugatePlaces _ hT hB.com.split) ψ0 hψ
  have hx : (iotaX S.X S.inst).symm (1, S.X.xu u) ∈ GfC (D.sp.Y 0) := by
    rw [← GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff S.X S.inst, ContinuousMulEquiv.apply_symm_apply]
  have htf : t ∈ GfC (D.sp.Y 0) := ht ▸
    mul_mem (mul_mem (inv_mem hx) (GlobalTheory.Core.Mi.CenAct.embA_mem_GfC B.d B.o (mul_mem ha₀.1 haf))) (hB.t 0)
  have hfin : ∀ y, finE (D.sp.Y 0) (t * y * t⁻¹) = finE (D.sp.Y 0) t * finE (D.sp.Y 0) y * (finE (D.sp.Y 0) t)⁻¹ := fun y => by
    rw [map_mul, map_mul, map_inv]
  have hmove : ∀ y ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) y ∈ St d.bot.β → (iotaX S.X S.inst (t * y * t⁻¹)).2 ∈ S.X.B.I.Kset :=
    fun y hy hs => hSt _ (mul_mem (mul_mem htf hy) (inv_mem htf))
      (by rw [hfin]; exact (GlobalTheory.FrameConj.conj_mem_St_iff _ _ _).2 hs)
  have hc : ∀ T β y : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D), y ∈ St (T⁻¹ * β) ↔ T * y * T⁻¹ ∈ St β := fun T β y => by
    rw [← GlobalTheory.FrameConj.conj_mem_St_iff T, mul_inv_cancel_left]
  have hc' : ∀ (T β y : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (PP), redFn (T⁻¹ * β) PP y = redFn β PP (T * y * T⁻¹) :=
    fun T β y PP => by rw [← GlobalTheory.FrameConj.redFn_conj T, mul_inv_cancel_left]
  have hto : ∀ y ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) y ∈ St d.bot.β →
      finE (D.sp.Y 0) y ∈ St ((finE (D.sp.Y 0) t)⁻¹ * β₀) := fun y hy hs => by
    rw [hc, ← hfin]
    exact (kset_iff_st S.X S.inst hβ₀ _).1 (hmove y hy hs)
  have hloc : ∀ PP : d.c.Pg, ∀ y ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) y ∈ St d.bot.β →
      (redFn β₀ PP.1 (finE (D.sp.Y 0) (t * y * t⁻¹)) ∈ unipSym (kP PP.1) (D.sp.Y 0).rank D.R.rS D.R.k ↔
        ∃ x, (G PP).Red x (upperLeftBlock hr (redFn d.bot.β PP.1 (finE (D.sp.Y 0) y)))) := by
    intro PP
    haveI : Finite (kP PP.1) := Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
    obtain ⟨m, hmm⟩ := GlobalTheory.T.splitPlaceReductions_conj_of_nestedFrameStabilisers D (D.sp.Y 0) d.bot.β ((finE (D.sp.Y 0) t)⁻¹ * β₀) _ N hN _ PP.1 (G PP).idem hto
    have hred : ∀ y ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) y ∈ St d.bot.β → redFn β₀ PP.1 (finE (D.sp.Y 0) (t * y * t⁻¹)) =
        m * redFn d.bot.β PP.1 (finE (D.sp.Y 0) y) * m⁻¹ := fun y hy hs => by
      rw [hfin, ← hc', hmm _ hs (hto y hy hs)]
    intro y hy hs
    rw [hred y hy hs, GlobalTheory.T.exists_reduction_iff_pattern D u d τ PP.1 (G PP)]
    refine conj_mem_iff_isPat hr hn hre m (fun g hg => ?_) _
    obtain ⟨w, hw, hws, hwg, hwK⟩ := generator_mem_K_two S d τ cG G h0 hE hB hG hX B hBl hA a₀ ha₀ a haz _ rfl t ht hmove hr PP g
      ((GlobalTheory.T.exists_reduction_iff_pattern D u d τ PP.1 (G PP) g).2 hg)
    refine ⟨_, hwg, ?_⟩
    rw [← hred w hw hws]
    exact ((hK _).1.1 hwK).2 PP.1 PP.2
  obtain ⟨y, rfl⟩ : ∃ y, κ = t * y * t⁻¹ := ⟨t⁻¹ * κ * t, by group⟩
  have hy : y ∈ GfC (D.sp.Y 0) := (GlobalTheory.FrameConj.conj_mem_iff _ htf y).1 hκ
  have hs : finE (D.sp.Y 0) y ∈ St d.bot.β := by
    rw [hfin] at hκS
    exact (GlobalTheory.FrameConj.conj_mem_St_iff _ _ _).1 hκS
  rw [(hK _).1, hG.grp]
  have e5 : ∀ PP, redFn (finE (D.sp.Y 0) t * d.bot.β) PP (finE (D.sp.Y 0) (t * y * t⁻¹)) =
      redFn d.bot.β PP (finE (D.sp.Y 0) y) := fun PP => by rw [hfin, GlobalTheory.FrameConj.redFn_conj]
  simp only [e5]
  exact ⟨fun h PP => (hloc PP y hy hs).1 (h.2 PP.1 PP.2), fun h => ⟨(kset_iff_st S.X S.inst hβ₀ _).1 (hmove y hy hs),
    fun PP hPP => (hloc ⟨PP, hPP⟩ y hy hs).2 (h ⟨PP, hPP⟩)⟩⟩

end GlobalTheory.Core.Mi.MemMatch

namespace GlobalTheory.Core.Mi

theorem memMatch_noLat : ∀ (D : D7) (u : D.what₂.Word) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : GlobalTheory.FinPl.OffDat d k ι) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d o.τ PP.1) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.Core.Mi.IdE S.X → d.Base → IsTypePlaces d.c.Pg → GlobalTheory.FinPl.PinOff o → GlobalTheory.LocMod.PinGBy G o.cG → LevX (F₀ u) d h0 → ∀ (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0)), B.lev = d.B 0 D.R.rS h0 → B.Adapted (S.tr u).wt → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → (∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β)) ↔ ((iotaX S.X S.inst κ).1 = 1 ∧ (iotaX S.X S.inst κ).2 ∈ S.X.B.I.Kset)) → ∀ (hr : D.R.r ≤ (D.sp.Y 0).rank) (κ : GA D (D.sp.Y 0)), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β) → ((iotaX S.X S.inst κ).2 ∈ S.X.K2 ↔ (fun PP : d.c.Pg => upperLeftBlock hr (redFn (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β) PP.1 (finE (D.sp.Y 0) κ))) ∈ d.c.P.H) := by
  intro D u F₀ S d k _ _ _ _ ι o G h0 hE hB hT _ hG hX B hBl hA a₀ ha₀ a haf haz hSt hr κ hκ hκS
  exact MemMatch.mem_iff S d o.τ o.cG G h0 hE hB hT hG hX B hBl hA a₀ ha₀ a haf haz _ rfl
    (fun y hy hs => ((hSt y).1 ⟨hy, hs⟩).2) hr κ hκ hκS

theorem memMatch : ∀ (D : D7) (u : D.what₂.Word) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : GlobalTheory.FinPl.OffDat d k ι) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d o.τ PP.1) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.Core.Mi.IdE S.X → d.Base → IsTypePlaces d.c.Pg → GlobalTheory.FinPl.PinOff o → GlobalTheory.LocMod.PinGBy G o.cG → (∀ z, z ∈ (d.x 0).L ↔ z ∈ (F₀ u).cls0.lev.Lb.map ((LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)))).toLinearMap.restrictScalars (𝓞 D.host.E))) → LevX (F₀ u) d h0 → ∀ (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0)), B.lev = d.B 0 D.R.rS h0 → B.Adapted (S.tr u).wt → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → (∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β)) ↔ ((iotaX S.X S.inst κ).1 = 1 ∧ (iotaX S.X S.inst κ).2 ∈ S.X.B.I.Kset)) → ∀ (hr : D.R.r ≤ (D.sp.Y 0).rank) (κ : GA D (D.sp.Y 0)), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β) → ((iotaX S.X S.inst κ).2 ∈ S.X.K2 ↔ (fun PP : d.c.Pg => upperLeftBlock hr (redFn (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β) PP.1 (finE (D.sp.Y 0) κ))) ∈ d.c.P.H) := by
  intro D u F₀ S d k _ _ _ _ ι o G h0 hE hB hT hO hG _
  exact memMatch_noLat D u F₀ S d k ι o G h0 hE hB hT hO hG

end GlobalTheory.Core.Mi

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.off_type_pinned_local_groups : ∀ (D : D7) (u : D.what₂.Word) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : GlobalTheory.FinPl.OffDat d k ι) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d o.τ PP.1) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.Core.Mi.IdE S.X → d.Base → IsTypePlaces d.c.Pg → GlobalTheory.FinPl.PinOff o → GlobalTheory.LocMod.PinGBy G o.cG → (∀ z, z ∈ (d.x 0).L ↔ z ∈ (F₀ u).cls0.lev.Lb.map ((LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)))).toLinearMap.restrictScalars (𝓞 D.host.E))) → LevX (F₀ u) d h0 → ∀ (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0)), B.lev = d.B 0 D.R.rS h0 → B.Adapted (S.tr u).wt → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → (∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β)) ↔ ((iotaX S.X S.inst κ).1 = 1 ∧ (iotaX S.X S.inst κ).2 ∈ S.X.B.I.Kset)) → ∀ (hr : D.R.r ≤ (D.sp.Y 0).rank) (κ : GA D (D.sp.Y 0)), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β) → ((iotaX S.X S.inst κ).2 ∈ S.X.K2 ↔ (fun PP : d.c.Pg => upperLeftBlock hr (redFn (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β) PP.1 (finE (D.sp.Y 0) κ))) ∈ d.c.P.H) := by
  atlas_forward_decl GlobalTheory.Core.Mi.memMatch
end
