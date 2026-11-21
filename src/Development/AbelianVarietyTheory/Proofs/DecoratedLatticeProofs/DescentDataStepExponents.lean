import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RdAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionAtLevelPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalGroupsMatrixReadingStatement

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

theorem GlobalTheory.IntPlaces.mem_of_idem_sum {R : Type} [CommRing R] {n : ℕ} (S : Set R) (hS0 : (0 : R) ∈ S)
    (E : Fin n → R) (hEE : ∀ i, E i * E i = E i) (hE : ∀ i j, i ≠ j → E i * E j = 0) (G : Fin n → R → Prop)
    (hint : ∀ i z, z ∈ S ↔ (1 - E i) * z ∈ S ∧ G i z) (hG : ∀ i j z, i ≠ j → G i z → G i ((1 - E j) * z)) :
    ∀ z, (∑ i, E i) * z = z → (∀ i, G i z) → z ∈ S := by
  have key : ∀ s : Finset (Fin n), ∀ z, (∑ i ∈ s, E i) * z = z → (∀ i ∈ s, G i z) → z ∈ S := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro z hz _
      rw [Finset.sum_empty, zero_mul] at hz
      rw [← hz]
      exact hS0
    | insert a s ha ih =>
      intro z hz hzi
      rw [Finset.sum_insert ha] at hz
      refine (hint a z).2 ⟨?_, hzi a (Finset.mem_insert_self a s)⟩
      have hET : E a * ∑ i ∈ s, E i = 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_zero fun i hi => hE a i fun h => ha (h ▸ hi)
      have hw : (1 - E a) * z = (∑ i ∈ s, E i) * z := by
        calc (1 - E a) * z = (1 - E a) * ((E a + ∑ i ∈ s, E i) * z) := by rw [hz]
          _ = (∑ i ∈ s, E i) * z := by linear_combination (-z) * hEE a + (-z) * hET
      refine ih _ ?_ fun i hi => ?_
      · linear_combination (-1 : R) * hw + (-z) * hET
      · exact hG i a z (fun h => ha (h ▸ hi)) (hzi i (Finset.mem_insert_of_mem hi))
  exact fun z hz hzi => key Finset.univ z hz fun i _ => hzi i

open GlobalTheory.IdemSupport in

theorem GlobalTheory.IntPlaces.mem_intAf_of_split : ∀ (D : D7) (n : ℕ) (k : Fin n → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (P : Fin n → Formalism.L2.DIV.Pl D.host.E), (∀ i, Formalism.L2.NTheta.IsIdemAt (q i).e (P i)) → Function.Injective P → ∀ (π' : ∀ i, Formalism.IndefR.Datum.EAf D →+* k i), (∀ i a, π' i (Formalism.IndefR.Datum.toEAf D a) = (q i).pr a) → (∀ i (z : Formalism.IndefR.Datum.EAf D), z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ (1 - Formalism.IndefR.Datum.toEAf D (q i).e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ π' i z ∈ 𝒪[k i]) → ∀ z : Formalism.IndefR.Datum.EAf D, Formalism.IndefR.Datum.toEAf D (∑ i, (q i).e) * z = z → (∀ i, π' i z ∈ 𝒪[k i]) → z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D n k _ _ _ _ q P hI hP π' hπ hint z0 hz0 hzi0
  have hΦ := GlobalTheory.StdFrames.comp_toAd D
  have hd : ∀ i, IsDelta ((GlobalTheory.StdFrames.toAd D).comp (Formalism.IndefR.Datum.toEAf D)) (P i) (q i).e :=
    fun i => delta_of_isIdemAt hΦ (hI i)
  have horth : ∀ i j, i ≠ j → (q i).e * (q j).e = 0 := by
    intro i j hij
    refine hΦ.ext' (by rw [RingHom.map_mul, (hd i).1, zero_mul, RingHom.map_zero]) fun Q => ?_
    rw [ev_mul, ev_zero]
    by_cases hQ : Q = P i
    · rw [(hd j).2.2 Q (fun h => hij (hP (hQ.symm.trans h))), mul_zero]
    · rw [(hd i).2.2 Q hQ, zero_mul]
  have hidem : ∀ i, (q i).e * (q i).e = (q i).e := by
    intro i
    refine hΦ.ext' (by rw [RingHom.map_mul, (hd i).1, zero_mul]) fun Q => ?_
    rw [ev_mul]
    by_cases hQ : Q = P i
    · rw [hQ, (hd i).2.1, mul_one]
    · rw [(hd i).2.2 Q hQ, zero_mul]
  have hpr : ∀ i j, i ≠ j → π' i (Formalism.IndefR.Datum.toEAf D (q j).e) = 0 := by
    intro i j hij
    rw [hπ, ← (q i).pr_sec ((q i).pr (q j).e), (q i).sec_pr, horth i j hij, map_zero]
  refine GlobalTheory.IntPlaces.mem_of_idem_sum (Formalism.L2.Herm.intAf D.host.F D.host.E : Set _) (zero_mem _)
    (fun i => Formalism.IndefR.Datum.toEAf D (q i).e) (fun i => by rw [← RingHom.map_mul, hidem])
    (fun i j hij => by rw [← RingHom.map_mul, horth i j hij, RingHom.map_zero]) (fun i z => π' i z ∈ 𝒪[k i])
    hint (fun i j z hij hz => ?_) z0 (by rw [show (∑ i, Formalism.IndefR.Datum.toEAf D (q i).e) = Formalism.IndefR.Datum.toEAf D (∑ i, (q i).e) from
      (map_sum (Formalism.IndefR.Datum.toEAf D).toAddMonoidHom (fun i => (q i).e) Finset.univ).symm]; exact hz0) hzi0
  rw [RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hpr i j hij, sub_zero, one_mul]
  exact hz
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_finiteAdele_of_split_place_components : ∀ (D : D7) (n : ℕ) (k : Fin n → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (P : Fin n → Formalism.L2.DIV.Pl D.host.E), (∀ i, Formalism.L2.NTheta.IsIdemAt (q i).e (P i)) → Function.Injective P → ∀ (π' : ∀ i, Formalism.IndefR.Datum.EAf D →+* k i), (∀ i a, π' i (Formalism.IndefR.Datum.toEAf D a) = (q i).pr a) → (∀ i (z : Formalism.IndefR.Datum.EAf D), z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ (1 - Formalism.IndefR.Datum.toEAf D (q i).e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ π' i z ∈ 𝒪[k i]) → ∀ z : Formalism.IndefR.Datum.EAf D, Formalism.IndefR.Datum.toEAf D (∑ i, (q i).e) * z = z → (∀ i, π' i z ∈ 𝒪[k i]) → z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  atlas_forward_decl GlobalTheory.IntPlaces.mem_intAf_of_split
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

namespace GlobalTheory.MovedDat

open GlobalTheory.LocMod.StepVec

theorem rank_first_loc {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) : D.R.k + (G.s + 1) = D.R.r := by
  have := G.hs
  unfold Ranks.r
  omega

theorem rdAt_iff {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) {w : Formalism.L2.DIV.Pl D.host.E} {π' : Formalism.IndefR.Datum.EAf D →+* G.k}
    (hπ : ∀ a, π' (Formalism.IndefR.Datum.toEAf D a) = G.q.pr a)
    (hred : GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F w) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) (x : G.S.P.J)
    (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP w))
    (M : Matrix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.k ⊕ Fin (G.s + 1)) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hM : g.val.submatrix (firstOrd (rank_first_loc G)) (firstOrd (rank_first_loc G)) = M.map (Formalism.L2.DIV.resS D.host.F w)) :
    RdAt G w x g ↔ MaxM ((x : GL _ G.k).val - M.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) := by
  have key : ∀ a b (z : 𝓞 D.host.E),
      Ideal.Quotient.mk w.asIdeal z = g.val (firstOrd (rank_first_loc G) a) (firstOrd (rank_first_loc G) b) →
      valuation G.k ((π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (M a b) - (ofSplit G.q).pr (z : D.host.E)) < 1 :=
    fun a b z hz => by
      have h1 : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z) =
          (ofSplit G.q).pr (z : D.host.E) := hπ (incA D (z : D.host.E))
      rw [← h1, ← RingHom.map_sub, ← hred.ker, RingHom.map_sub, Formalism.L2.DIV.resS_oToS, sub_eq_zero]
      exact (hz.trans (congrFun (congrFun hM a) b)).symm
  constructor
  · intro h a b
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (g.val (firstOrd (rank_first_loc G) a) (firstOrd (rank_first_loc G) b))
    have := Valuation.map_sub_lt _ (h a b _ _ (firstOrd_val _ a) (firstOrd_val _ b) z hz) (key a b z hz)
    rwa [sub_sub_sub_cancel_right] at this
  · intro h a b a' b' ha hb z hz
    obtain rfl : a' = firstOrd (rank_first_loc G) a := Fin.ext (ha.trans (firstOrd_val _ a).symm)
    obtain rfl : b' = firstOrd (rank_first_loc G) b := Fin.ext (hb.trans (firstOrd_val _ b).symm)
    have := Valuation.map_add_lt _ (h a b) (key a b z hz)
    rwa [Matrix.sub_apply, Matrix.map_apply, sub_add_sub_cancel] at this

theorem card_of_ix {κ l r t j a : ℕ} (h : κ + l = r) (e : Ix (Fin κ ⊕ Fin l) (Fin t) j ≃ Fin a) : a = r + j * t := by
  have e' : (Fin κ ⊕ Fin l) ⊕ (Fin j × Fin t) ≃ Fin a := e
  have := Fintype.card_congr e'
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at this
  rw [← this, h]

theorem locF_eq_iterPhi : ∀ (D : D7) (c : Comm D) (v : VCom c) (G0 : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (π' : Formalism.IndefR.Datum.EAf D →+* G0.k), (∀ a, π' (Formalism.IndefR.Datum.toEAf D a) = G0.q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ (χ : ℕ → ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (j : ℕ), (∀ c, c ≤ j → GlobalTheory.FunObj.Comparison₂.Compat (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (χ (c + 1) PP) (G0.S.μ (c + 1))) → ∀ (a b : ℕ) (hr : D.R.r ≤ a) (ea : Ix (Fin D.R.k ⊕ Fin (G0.s + 1)) (Fin D.R.t) j ≃ Fin a) (eb : Ix (Fin D.R.k ⊕ Fin (G0.s + 1)) (Fin D.R.t) (j + 1) ≃ Fin b), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos ea → GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos eb → ∀ N : Matrix (Fin b) (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E), GlobalTheory.LocMod.StepVec.locF D.R.t j hr (GlobalTheory.MovedDat.RdAt G0 PP) (fun x => G0.S.P.lam x) (fun c => χ c PP) (N.map (Formalism.L2.DIV.resS D.host.F PP)) = G0.S.P.iterPhi (Fin D.R.t) G0.S.μ G0.S.tame j ((N.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)).submatrix eb ea) := by
  intro D c v G0 PP π' hπ hred χ j hχ a b hr ea eb ha hb N
  exact locF_eq (GlobalTheory.FunObj.TieLev.iterPhi_read _ _ _ _ _ hred _ _ _ _ _ _ (firstOrd (rank_first_loc G0)) ea eb
    (isIx_of_isOrd _ (card_of_ix (rank_first_loc G0) ea) ha) (isIx_of_isOrd _ (card_of_ix (rank_first_loc G0) eb) hb) hr _ _ _
    (fun i => χ i PP) hχ _ (rdAt_iff G0 hπ hred) N)

end GlobalTheory.MovedDat
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_local_factor_eq_iterated_chain_datum : ∀ (D : D7) (c : Comm D) (v : VCom c) (G0 : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (π' : Formalism.IndefR.Datum.EAf D →+* G0.k), (∀ a, π' (Formalism.IndefR.Datum.toEAf D a) = G0.q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ (χ : ℕ → ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (j : ℕ), (∀ c, c ≤ j → GlobalTheory.FunObj.Comparison₂.Compat (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (χ (c + 1) PP) (G0.S.μ (c + 1))) → ∀ (a b : ℕ) (hr : D.R.r ≤ a) (ea : Ix (Fin D.R.k ⊕ Fin (G0.s + 1)) (Fin D.R.t) j ≃ Fin a) (eb : Ix (Fin D.R.k ⊕ Fin (G0.s + 1)) (Fin D.R.t) (j + 1) ≃ Fin b), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos ea → GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos eb → ∀ N : Matrix (Fin b) (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E), GlobalTheory.LocMod.StepVec.locF D.R.t j hr (GlobalTheory.MovedDat.RdAt G0 PP) (fun x => G0.S.P.lam x) (fun c => χ c PP) (N.map (Formalism.L2.DIV.resS D.host.F PP)) = G0.S.P.iterPhi (Fin D.R.t) G0.S.μ G0.S.tame j ((N.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)).submatrix eb ea) := by
  atlas_forward_decl GlobalTheory.MovedDat.locF_eq_iterPhi
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.MovedDat

open GlobalTheory.LocMod.StepVec

theorem mt_mul {D : D7} (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one {D : D7} (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

theorem mt_inv_mul {D : D7} (V : HSp D) (a : GA D V) : mt V a⁻¹ * mt V a = 1 := by
  rw [← mt_mul, inv_mul_cancel, mt_one]

theorem isHalf_mul {D : D7} {S T : HSp D} (e : AE D) (A : Matrix (Fin T.rank) (Fin T.rank) (AE D))
    (B : Matrix (Fin S.rank) (Fin S.rank) (AE D)) (y : WO S T) (hy : IsHalf e y) :
    IsHalf e (HMul.hMul (HMul.hMul A (y : Matrix (Fin T.rank) (Fin S.rank) (AE D))) B : WO S T) := by
  intro i j
  have hy' : e • (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) :=
    Matrix.ext fun i j => hy i j
  have := congrFun (congrFun (congrArg (fun M : Matrix (Fin T.rank) (Fin S.rank) (AE D) => HMul.hMul (HMul.hMul A M) B) hy') i) j
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul] at this
  exact this

theorem isHalf_actO_iff {D : D7} (S T : HSp D) (g : GA D S) (h : GA D T) (e : AE D) (x : WO S T) :
    IsHalf e (actO S T g h x) ↔ IsHalf e x := by
  constructor
  · intro hx
    have e1 : x = actO S T g⁻¹ h⁻¹ (actO S T g h x) := by
      unfold actO
      rw [inv_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul, Matrix.mul_assoc,
        mt_inv_mul, Matrix.mul_one]
    rw [e1]
    exact isHalf_mul e _ _ _ hx
  · intro hx
    exact isHalf_mul e _ _ _ hx

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

theorem down_moved_actO (p : Place D k) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (g : GA D S) (h : GA D T) (x : WO S T) :
    p.down (moved p FS g⁻¹) (moved p FT h⁻¹) (actO S T g⁻¹ h⁻¹ x) = p.down FS FT x := by
  have hm : ∀ (V : HSp D) (a : GA D V), (mt V a⁻¹⁻¹).map p.π * (mt V a⁻¹).map p.π = 1 := fun V a => by
    rw [← Matrix.map_mul, mt_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  unfold Place.down moved actO
  simp only [Matrix.map_mul]
  have e1 : FT.γ * (mt T h⁻¹⁻¹).map p.π * ((mt T h⁻¹).map p.π * (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π *
      (mt S g⁻¹⁻¹).map p.π) * ((mt S g⁻¹).map p.π * FS.β) =
      FT.γ * ((mt T h⁻¹⁻¹).map p.π * (mt T h⁻¹).map p.π) * (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π *
        ((mt S g⁻¹⁻¹).map p.π * (mt S g⁻¹).map p.π) * FS.β := by
    simp only [Matrix.mul_assoc]
  rw [e1, hm, hm, Matrix.mul_one, Matrix.mul_one]

end GlobalTheory.MovedDat

namespace GlobalTheory.MovedDat

open GlobalTheory.LocMod.StepVec

theorem phi_down_eq (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) {u : D.what₂.Word} (f : FamCh W u) (v : VCom f.c) (G0 : GLoc v)
    (π' : Formalism.IndefR.Datum.EAf D →+* G0.k) (hπ : ∀ a, π' (Formalism.IndefR.Datum.toEAf D a) = G0.q.pr a) (j a : ℕ) (ha : j + a = G0.s)
    (ea : Ix (Fin D.R.k ⊕ Fin (G0.s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank)
    (eb : Ix (Fin D.R.k ⊕ Fin (G0.s + 1)) (Fin D.R.t) (j + 1) ≃ Fin (Yc D (j + 1)).rank)
    (mS : MovedTo (ofSplit G0.q) (Yc D j) (f.g.b j) ((pk W).βY j)
      (((G0.FY j (a + 1) (by omega)).β * ((G0.S.T (Fin D.R.t)).bas j (a + 1) (by omega)).val).submatrix id
        fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j (a + 1) (by omega) (ea.symm i)))
    (mT : MovedTo (ofSplit G0.q) (Yc D (j + 1)) (f.g.b (j + 1)) ((pk W).βY (j + 1))
      (((G0.FY (j + 1) a (by omega)).β * ((G0.S.T (Fin D.R.t)).bas (j + 1) a (by omega)).val).submatrix id
        fun i => stdOrd (Fin D.R.k) (Fin D.R.t) (j + 1) a (by omega) (eb.symm i)))
    (x : WO (Yc D j) (Yc D (j + 1))) :
    ((G0.S.T (Fin D.R.t)).Phi j a ha ((ofSplit G0.q).down (G0.FY j (a + 1) (by omega)) (G0.FY (j + 1) a (by omega)) x)) =
      G0.S.P.iterPhi (Fin D.R.t) G0.S.μ G0.S.tame j
        (((frMapO (Yc D j) (Yc D (j + 1)) ((pk W).βY j) ((pk W).βY (j + 1))
          (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x)).map π').submatrix eb ea) := by
  have hS := map_eq_of_movedTo (ofSplit G0.q) (G0.FY j (a + 1) (by omega)) hπ _ _ mS
  have hT := map_eq_of_movedTo (ofSplit G0.q) (G0.FY (j + 1) a (by omega)) hπ _ _ mT
  have key := coords_down (ofSplit G0.q) _ _ hπ (typeFrame G0.S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) j (a + 1) (by omega)))
    (typeFrame G0.S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) (j + 1) a (by omega))) ea eb hS hT
    (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x)
  rw [down_moved_actO] at key
  rw [← key]
  rfl

end GlobalTheory.MovedDat

namespace GlobalTheory.MovedDat

theorem moved_datum_eq_prod : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ v : VCom f.c, v.Is → VTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg), GPin G → GRead f G pl → ∀ j, j + 1 < D.R.m → ∀ (a : Fin n → ℕ) (ha : ∀ i, j + a i = (G i).s), ∃ κ : ℂ, κ ≠ 0 ∧ ∀ x : WO (Yc D j) (Yc D (j + 1)), (if IsHalf (∑ i, (G i).q.e) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x) ∧ IsIntM (frMapO (Yc D j) (Yc D (j + 1)) ((pk W).βY j) ((pk W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x)) then omegaG (datY _ D.R.r D.R.t j (r_le_Y j) (pk W).Pg ∅ (lvP W) (pk W).chi (fun _ => 1) Frm.B) ((pk W).chi (j + 1)) (fun PP => redM PP (frMapO (Yc D j) (Yc D (j + 1)) ((pk W).βY j) ((pk W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x))) * omegaQ ∅ (datY _ D.R.r D.R.t j (r_le_Y j) (pk W).Pg ∅ (lvP W) (pk W).chi (fun _ => 1) Frm.B).r (fun _ => 1) 1 (fun PP => redM PP (frMapO (Yc D j) (Yc D (j + 1)) ((pk W).βY j) ((pk W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x))) else 0) = κ * (if IsHalf (∑ i, (G i).q.e) x then ∏ i, ((G i).S.T (Fin D.R.t)).Phi j (a i) (ha i) ((ofSplit (G i).q).down ((G i).FY j (a i + 1) (by have := ha i; omega)) ((G i).FY (j + 1) (a i) (by have := ha i; omega)) x) else 0) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hRow v hv hVT n G pl hGP hGR j hj a ha
  refine ⟨1, one_ne_zero, fun x => ?_⟩
  rw [one_mul, isHalf_actO_iff]
  choose π' hπ hred hint hres using fun i => GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D (G i).k (G i).q (pl i).1 (hGR.idem i).1
  choose ea hea mS using fun i => hGR.frame i j (a i + 1) (by have := ha i; omega)
  choose eb heb mT using fun i => hGR.frame i (j + 1) (a i) (by have := ha i; omega)
  have hC := fun i => phi_down_eq D L hT Gi Gl Kc Yd cX ex W f v (G i) (π' i) (hπ i) j (a i) (ha i) (ea i) (eb i) (mS i) (mT i) x
  by_cases hx : IsHalf (∑ i, (G i).q.e) x
  · rw [if_pos hx]
    have hx' := (isHalf_actO_iff _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ _ x).2 hx
    have hQ : ∀ y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin (Yc D (j + 1)).rank) (Fin (Yc D j).rank) (Formalism.L2.DIV.kP PP),
        omegaQ (∅ : Finset (Formalism.L2.DIV.Pl D.host.E)) (datY _ D.R.r D.R.t j (r_le_Y j) (pk W).Pg ∅ (lvP W) (pk W).chi
          (fun _ => 1) Frm.B).r (fun _ => 1) 1 y = 1 := fun y => by
      rw [omegaQ, dif_pos (by simp)]; simp
    by_cases hI : IsIntM (frMapO (Yc D j) (Yc D (j + 1)) ((pk W).βY j) ((pk W).βY (j + 1))
      (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x))
    · rw [if_pos ⟨hx, hI⟩, hQ, mul_one, GlobalTheory.T.local_groups_matrix_reading D L hT Gi Gl Kc Yd cX ex W u f v n G pl hGR j]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hC i, GlobalTheory.LocMod.StepVec.redM_eq_map (pl i).1 hI, GlobalTheory.T.seeSaw_local_factor_eq_iterated_chain_datum D f.c v (G i) (pl i).1 (π' i) (hπ i) (hred i) (pk W).chi j
        (fun c hc => GlobalTheory.T.reduction_at_level_place D L hT Gi Gl Kc Yd cX ex W hP (G i).k (G i).q (pl i).1 (pl i).2 (hGR.idem i).1 (π' i) (hπ i) (hred i)
          (c + 1) (by omega) (by omega) _ ((G i).S.tame _) (hGR.mu i (c + 1) (by omega) (by omega)))
        _ _ (r_le_Y j) (ea i) (eb i) (hea i) (heb i)]
      rfl
    · rw [if_neg (fun h => hI h.2)]
      symm
      by_contra hne
      apply hI
      have hnz := fun i h => hne (Finset.prod_eq_zero (Finset.mem_univ i) h)
      intro r s
      refine GlobalTheory.T.integral_finiteAdele_of_split_place_components D n (fun i => (G i).k) (fun i => (G i).q) (fun i => (pl i).1) (fun i => (hGR.idem i).1)
        (fun i l h => pl.injective (Subtype.ext h)) π' hπ hint _ ?_ fun i => ?_
      · rw [← GlobalTheory.LocMod.StepVec.frMapO_smul]
        congr 1
        exact Matrix.ext fun r' s' => hx' r' s'
      · have h1 := hnz i
        rw [hC i] at h1
        have h2 := GlobalTheory.StepData.TypeDatum.intM_of_Phi_ne_zero _ _ h1 ((ixSucc _ _ j).symm ((eb i).symm r)) ((ea i).symm s)
        simpa using h2
  · rw [if_neg (fun h => hx h.1), if_neg hx]

end GlobalTheory.MovedDat

end
end
