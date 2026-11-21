import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRightOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqFinClSumAvg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Formalism.LocalToGlobal.IndefiniteReal.TopMult
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFinCombOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenSubgroupFixesVacuumDefiniteBottom
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixingSeesawVacuumDefiniteBottom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixTranslates

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option synthInstance.maxHeartbeats 100000

noncomputable section

namespace GlobalTheory.BottomFinComb

open StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

variable {D : D7}

local notation "OO" => Formalism.L2.Herm.intAf D.host.F D.host.E

theorem eToEAf_mem (α : 𝓞 D.host.E) : eToEAf D (α : D.host.E) ∈ OO := (oToS D.host.F D.host.E α).2

theorem exists_nat_den (a : D.host.E) : ∃ q : ℕ, 0 < q ∧ (q : EAf D) * eToEAf D a ∈ OO := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := D.host.E) {a}
  have hi : IsIntegral ℤ (y • a) := hy a (by simp)
  have h1 : eToEAf D (y • a) ∈ OO := eToEAf_mem ⟨y • a, hi⟩
  refine ⟨y.natAbs * y.natAbs, Nat.mul_pos (Int.natAbs_pos.2 hy0) (Int.natAbs_pos.2 hy0), ?_⟩
  have h0 : ((y.natAbs * y.natAbs : ℕ) : EAf D) = ((y * y : ℤ) : EAf D) := by
    rw [← Int.natAbs_mul_self' y, ← Nat.cast_mul, Int.cast_natCast]
  have h2 : ((y.natAbs * y.natAbs : ℕ) : EAf D) * eToEAf D a = (y : EAf D) * eToEAf D (y • a) := by
    rw [h0, zsmul_eq_mul, map_mul, map_intCast, Int.cast_mul, mul_assoc]
  rw [h2]
  exact mul_mem (intCast_mem _ _) h1

theorem frMapAdj_add' (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x y : WO S T) :
    frMapAdj S T βS βT (x + y) = frMapAdj S T βS βT x + frMapAdj S T βS βT y := by
  unfold frMapAdj
  rw [Matrix.map_add (cA D) (fun a b => (cA D).map_add a b), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul,
    Matrix.map_add (toEAf D) (fun a b => (toEAf D).map_add a b), Matrix.mul_add, Matrix.add_mul]

theorem frMapAdj_zero' (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) :
    frMapAdj S T βS βT 0 = 0 := by
  have h := frMapAdj_add' S T βS βT 0 0
  rw [add_zero] at h
  exact (add_eq_left.1 h.symm)

theorem frMapAdj_nsmul' (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (k : ℕ)
    (x : WO S T) : frMapAdj S T βS βT (k • x) = k • frMapAdj S T βS βT x := by
  induction k with
  | zero => rw [zero_smul, zero_smul, frMapAdj_zero']
  | succ n ih => rw [succ_nsmul, succ_nsmul, frMapAdj_add', ih]

theorem dualCoord_add_nsmul (A' WW : HSp D) (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D))
    (t u : WO A' WW) (k : ℕ) :
    dualCoord A' WW βA' βW (t + k • u) = dualCoord A' WW βA' βW t + k • dualCoord A' WW βA' βW u := by
  unfold dualCoord
  rw [frMapAdj_add', frMapAdj_nsmul', smul_add, smul_comm]

theorem isIntM_rightBlock {k d : ℕ} (a : ℕ) {Y : Matrix (Fin k) (Fin d) (EAf D)} (h : IsIntM Y) :
    IsIntM (rightBlock a Y) := fun i j => by
  unfold rightBlock
  split_ifs
  · exact h _ _
  · exact zero_mem _

theorem rightBlock_shift {k d : ℕ} (a : ℕ) {Y Y' Z : Matrix (Fin k) (Fin d) (EAf D)} {c : EAf D}
    (h : ∀ i j, Y' i j = Y i j + c * Z i j) (i j : Fin k) :
    rightBlock a Y' i j = rightBlock a Y i j + c * rightBlock a Z i j := by
  unfold rightBlock
  split_ifs
  · exact h _ _
  · rw [mul_zero, add_zero]

set_option maxHeartbeats 1000000 in

theorem stdSnd_shift {ν : (AE D)ˣ →* Circle} {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S)
    {I : Ideal (𝓞 D.host.E)} {n₀ n c : ℕ} (hn₀ : ((n₀ : ℕ) : 𝓞 D.host.E) ∈ I)
    (hl : ∀ x, Formalism.L2.Pj.FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = n • y) → ν x = 1)
    (hc : ∀ P ∈ S, ((c : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (a : ℕ) (A' WW : HSp D) (βA' : GL (Fin A'.rank) (EAf D))
    (βW : GL (Fin WW.rank) (EAf D)) {t t' : WO A' WW} (hh : IsHalf (cA D e) t' ↔ IsHalf (cA D e) t)
    {Z : Matrix (Fin A'.rank) (Fin WW.rank) (EAf D)} (hZ : IsIntM Z)
    (h : ∀ i j, dualCoord A' WW βA' βW t' i j =
      dualCoord A' WW βA' βW t i j + ((n₀ * (n * c) : ℕ) : EAf D) * Z i j) :
    stdSnd ν e I a A' WW βA' βW t' = stdSnd ν e I a A' WW βA' βW t := by
  have hW1 : ∀ i j, ((n * c : ℕ) : EAf D) * Z i j ∈ OO := fun i j => mul_mem (natCast_mem _ _) (hZ i j)
  have hW2 : ∀ i j, (n₀ : EAf D) * (((n * c : ℕ) : EAf D) * Z i j) ∈ OO := fun i j =>
    mul_mem (natCast_mem _ _) (hW1 i j)
  have ha : ∀ i j, dualCoord A' WW βA' βW t' i j =
      dualCoord A' WW βA' βW t i j + (n₀ : EAf D) * (((n * c : ℕ) : EAf D) * Z i j) := fun i j => by
    rw [h, Nat.cast_mul n₀, mul_assoc]
  have hb : ∀ i j, dualCoord A' WW βA' βW t i j =
      dualCoord A' WW βA' βW t' i j + (n₀ : EAf D) * (-(((n * c : ℕ) : EAf D) * Z i j)) := fun i j => by
    rw [ha, mul_neg, add_neg_cancel_right]
  have hint : IsIntM (dualCoord A' WW βA' βW t') ↔ IsIntM (dualCoord A' WW βA' βW t) :=
    forall_congr' fun i => forall_congr' fun j => by
      rw [ha]
      exact add_mem_cancel_right (hW2 i j)
  have hid : (∀ i j, j.1 < a → InId I (dualCoord A' WW βA' βW t' i j)) ↔
      ∀ i j, j.1 < a → InId I (dualCoord A' WW βA' βW t i j) :=
    ⟨fun H i j hi => inId_shift hn₀ (neg_mem (hW1 i j)) (hb i j) (H i j hi),
      fun H i j hi => inId_shift hn₀ (hW1 i j) (ha i j) (H i j hi)⟩
  unfold stdSnd
  by_cases hcnd : IsHalf (cA D e) t ∧ IsIntM (dualCoord A' WW βA' βW t) ∧
      ∀ i j, j.1 < a → InId I (dualCoord A' WW βA' βW t i j)
  · rw [if_pos hcnd, if_pos ⟨hh.2 hcnd.1, hint.2 hcnd.2.1, hid.2 hcnd.2.2⟩]
    refine (unitChar_congr he hl hc (isIntM_rightBlock a hcnd.2.1)
      (Z := rightBlock a fun i j => (n₀ : EAf D) * Z i j)
      (isIntM_rightBlock a fun i j => mul_mem (natCast_mem _ _) (hZ i j))
      (rightBlock_shift a (c := ((n * c : ℕ) : EAf D)) fun i j => ?_)).symm
    rw [h, Nat.cast_mul n₀]
    ring
  · rw [if_neg hcnd, if_neg fun h' => hcnd ⟨hh.1 h'.1, hint.1 h'.2.1, hid.1 h'.2.2⟩]

set_option maxHeartbeats 1000000 in

theorem stdSnd_isSB {ν : (AE D)ˣ →* Circle} (hν : Continuous ν) {e : AE D} {S : Finset (Pl D.host.E)}
    (he : IsIdemSum e S) {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) (a : ℕ) (A' WW : HSp D)
    (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (Λ : AddSubgroup (WO A' WW))
    (hB : ∃ M : ℕ, 0 < M ∧ ∀ u ∈ Λ, ∀ i j, (M : EAf D) * dualCoord A' WW βA' βW u i j ∈ OO)
    (hC : ∃ K : ℕ, 0 < K ∧ ∀ t : WO A' WW, IsHalf (cA D e) t → IsIntM (dualCoord A' WW βA' βW t) → K • t ∈ Λ) :
    IsSBHalf (cA D e) Λ (stdSnd ν e I a A' WW βA' βW) := by
  obtain ⟨M, hM, hB⟩ := hB
  obtain ⟨K, hK, hC⟩ := hC
  obtain ⟨n, hn, hl, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν
  obtain ⟨n₀, hn₀, hnI⟩ : ∃ n₀ : ℕ, 0 < n₀ ∧ ((n₀ : ℕ) : 𝓞 D.host.E) ∈ I :=
    ⟨_, Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h), Ideal.absNorm_mem I⟩
  obtain ⟨c, hc, hcS⟩ : ∃ c : ℕ, 0 < c ∧ ∀ P ∈ S, ((c : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    refine ⟨∏ P ∈ S, Ideal.absNorm P.asIdeal, Finset.prod_pos fun P _ =>
      Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h), fun P hP => ?_⟩
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun P : Pl D.host.E => Ideal.absNorm P.asIdeal) hP
    rw [hm, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem P.asIdeal)
  refine ⟨fun t ht => ?_, K * ((n₀ * (n * c)) * M),
    Nat.mul_pos hK (Nat.mul_pos (Nat.mul_pos hn₀ (Nat.mul_pos hn hc)) hM), fun u hu hh t => ?_, fun t ht => ?_⟩
  · unfold stdSnd at ht
    by_contra h
    exact ht (if_neg fun h' => h h'.1)
  · refine stdSnd_shift he hnI hl hcS a A' WW βA' βW
      (Z := fun i j => (K : EAf D) * ((M : EAf D) * dualCoord A' WW βA' βW u i j))
      ?_ (fun i j => mul_mem (natCast_mem _ _) (hB u hu i j)) fun i j => ?_
    · rw [GlobalTheory.PlaceModel.isHalf_iff A' WW, GlobalTheory.PlaceModel.isHalf_iff A' WW]
      exact AddSubgroup.add_mem_cancel_right _ (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff A' WW).1 hh) _)
    · rw [dualCoord_add_nsmul, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]
      push_cast
      ring
  · have h : IsHalf (cA D e) t ∧ IsIntM (dualCoord A' WW βA' βW t) := by
      unfold stdSnd at ht
      by_contra h
      exact ht (if_neg fun h' => h ⟨h'.1, h'.2.1⟩)
    rw [mul_nsmul]
    exact nsmul_mem (hC t h.1 h.2) _

end GlobalTheory.BottomFinComb

namespace GlobalTheory.BottomFinComb

open StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

set_option maxHeartbeats 1000000 in

theorem finVec_isFinComb : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ (n : ℕ) (c : Fin n → ℂ) (x : Fin n → WO A' WW), (∀ k, (x k).map (infPart D) = 0) ∧
      X.f' t = ∑ k, c k • heisO W.ψ A' WW (x k) X.vac' := by
  intro D T L sc G W i j A A' WW X hX t
  have he := hX.is.idem t
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hce : cA D (X.e t) * cA D (X.e t) = cA D (X.e t) := by rw [← RingHom.map_mul, hee]
  have hcinf : infPart D (cA D (X.e t)) = 0 := GlobalTheory.PlaceDatum.infPart_cA hinf
  have hν := (hX.is.weil' t).hecT.1
  have hI : X.ideal (locPl G) t ≠ ⊥ := by
    unfold Tri.ideal
    rw [← Ideal.zero_eq_bot]
    exact Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)
  have hξ := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  obtain ⟨d, hd, hL1⟩ : ∃ d : ℕ, 0 < d ∧ ∀ u ∈ (latO A' WW X.rA'.Λ X.rW.Λ fun _ => True),
      IsIntM (frMapAdj A' WW X.rA'.β X.rW.β (d • u)) := by
    obtain ⟨k, hk, h⟩ := GlobalTheory.PlaceVec.frMapAdj_up A' WW X.rA'.β X.rW.β
    obtain ⟨M, hM, h'⟩ := GlobalTheory.PlaceDatum.exists_den_latO hX.is.rigA'.1.1.fg hX.is.rigW.1.1.fg
    refine ⟨M * k, Nat.mul_pos hM hk, fun u hu => ?_⟩
    rw [mul_nsmul, frMapAdj_nsmul']
    refine h _ fun a b => ?_
    change toEAf D (M • u a b) ∈ _
    rw [nsmul_eq_mul, RingHom.map_mul, map_natCast]
    exact h' u hu a b
  obtain ⟨q, hq, hqξ⟩ := exists_nat_den (D := D) D.host.xi0
  obtain ⟨q', hq', hq'ξ⟩ := exists_nat_den (D := D) D.host.xi0⁻¹
  obtain ⟨m, hm, hmem⟩ : ∃ m : ℕ, 0 < m ∧ ∀ s : WO A' WW, IsHalf (cA D (X.e t)) s →
      IsIntM (frMapAdj A' WW X.rA'.β X.rW.β s) → m • s ∈ (latO A' WW X.rA'.Λ X.rW.Λ fun _ => True) := by
    obtain ⟨N, hN, h'⟩ := GlobalTheory.PlaceVec.frMapAdj_down A' WW X.rA'.β X.rW.β
    obtain ⟨K, hK, h⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO hX.is.rigA'.1.1 hX.is.rigW.1.1
    refine ⟨N * K, Nat.mul_pos hN hK, fun s hs hi => ?_⟩
    have ht := GlobalTheory.PlaceDatum.infPart_of_half hcinf hs
    rw [mul_nsmul]
    refine h _ (Matrix.ext fun a b => ?_) fun a b => ?_
    · change infPart D (N • s a b) = 0
      rw [nsmul_eq_mul, RingHom.map_mul, show infPart D (s a b) = 0 from congrFun (congrFun ht a) b, mul_zero]
    · change toEAf D (N • s a b) ∈ _
      rw [hom_nsmul]
      exact h' s hi a b
  have hB : ∃ M : ℕ, 0 < M ∧ ∀ u ∈ (latO A' WW X.rA'.Λ X.rW.Λ fun _ => True), ∀ a b,
      (M : EAf D) * dualCoord A' WW X.rA'.β X.rW.β u a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    refine ⟨q * d, Nat.mul_pos hq hd, fun u hu a b => ?_⟩
    have h1 := hL1 u hu a b
    rw [frMapAdj_nsmul', Matrix.smul_apply, nsmul_eq_mul] at h1
    have e1 : ((q * d : ℕ) : EAf D) * dualCoord A' WW X.rA'.β X.rW.β u a b =
        ((q : EAf D) * eToEAf D D.host.xi0) * ((d : EAf D) * frMapAdj A' WW X.rA'.β X.rW.β u a b) := by
      unfold dualCoord
      rw [Matrix.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [e1]
    exact mul_mem hqξ h1
  have hC : ∃ K : ℕ, 0 < K ∧ ∀ s : WO A' WW, IsHalf (cA D (X.e t)) s →
      IsIntM (dualCoord A' WW X.rA'.β X.rW.β s) → K • s ∈ (latO A' WW X.rA'.Λ X.rW.Λ fun _ => True) := by
    refine ⟨q' * m, Nat.mul_pos hq' hm, fun s hs hint => ?_⟩
    have h1 : IsIntM (frMapAdj A' WW X.rA'.β X.rW.β (q' • s)) := fun a b => by
      have e1 : frMapAdj A' WW X.rA'.β X.rW.β (q' • s) a b =
          ((q' : EAf D) * eToEAf D D.host.xi0⁻¹) * dualCoord A' WW X.rA'.β X.rW.β s a b := by
        rw [frMapAdj_nsmul', Matrix.smul_apply, nsmul_eq_mul]
        unfold dualCoord
        rw [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← mul_assoc (eToEAf D _), ← map_mul, inv_mul_cancel₀ hξ,
          map_one, one_mul]
      rw [e1]
      exact mul_mem hq'ξ (hint a b)
    have h2 : IsHalf (cA D (X.e t)) (q' • s) :=
      (GlobalTheory.PlaceModel.isHalf_iff A' WW).2 (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff A' WW).1 hs) _)
    rw [mul_nsmul]
    exact hmem _ h2 h1
  have hSB := stdSnd_isSB hν he hI A.rank A' WW X.rA'.β X.rW.β _ hB hC
  exact GlobalTheory.AdForm.isFinComb_of_isThetaAt W.ψ A' WW X.rA'.Λ X.rW.Λ (cA D (X.e t)) X.vac' _ (X.f' t) hX.is.isVac'.1
    hX.is.rigA'.1 hX.is.rigW.1 hce hcinf hSB (hX.is.snd t)

end GlobalTheory.BottomFinComb
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottom_finiteVector_eq_finite_heisenbergComb : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ (n : ℕ) (c : Fin n → ℂ) (x : Fin n → WO A' WW), (∀ k, (x k).map (infPart D) = 0) ∧
      X.f' t = ∑ k, c k • heisO W.ψ A' WW (x k) X.vac' := by
  atlas_forward_decl GlobalTheory.BottomFinComb.finVec_isFinComb
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_subgroup_fixes_vacuum_definiteBottom : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D A'), IsOpen (U : Set (GA D A')) ∧ ∀ κ ∈ U, κ ∈ GfC A' → X.ω' t (κ, 1) X.vac' = X.vac' := by
  first | exact @GlobalTheory.VacFixSource.exists_open_fix_vac_source | exact GlobalTheory.VacFixSource.exists_open_fix_vac_source | (intros; apply GlobalTheory.VacFixSource.exists_open_fix_vac_source <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

open scoped Topology
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.VacTranslateLeft

theorem exists_open_fix_translate_source : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f₀ : WO S T → ℂ,
    IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f₀ →
    ∀ u : WO S T, u.map (infPart D) = 0 →
    ∃ U : Subgroup (GA D S), IsOpen (U : Set (GA D S)) ∧ ∀ κ ∈ U, κ ∈ GfC S →
      heisO ψ S T (actO S T κ 1 u) f₀ = heisO ψ S T u f₀ := by
  intro D ψ θ S T sS sT ΛS ΛT hS hT f₀ hvac u hu
  obtain ⟨M, hM, hMu⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' hS.1 hT.1 u hu
  have hN : 0 < 2 * (2 * 2) * M * M := by positivity
  have hev := GlobalTheory.LatNhds.eventually_move S T ΛS ΛT hS hT u hu (2 * (2 * 2) * M * M) hN
  have hc : Filter.Tendsto (fun κ : GA D S => (κ, (1 : GA D T))) (𝓝 1) (𝓝 1) := by
    have := (continuous_id.prodMk (continuous_const (y := (1 : GA D T)))).tendsto (1 : GA D S)
    simpa only [Prod.mk_one_one, id] using this
  have hev' := hc.eventually hev
  have key : ∃ n : ℕ, ∀ κ ∈ GfC S, GlobalTheory.Member.FinCong S n.factorial κ →
      ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        actO S T κ 1 u = u + (2 * (2 * 2) * M * M) • l := by
    by_contra hne
    push_neg at hne
    choose k hk hkc hkne using hne
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := k) hk hkc
    obtain ⟨n, hn⟩ := (ht.eventually hev').exists
    obtain ⟨l, hl, e⟩ := hn
    exact hkne n l hl e
  obtain ⟨n, hn⟩ := key
  refine ⟨GlobalTheory.VacFixTarget.congGroup S n.factorial, GlobalTheory.VacFixTarget.isOpen_congGroup S n.factorial_pos,
    fun κ hκc hκ => ?_⟩
  obtain ⟨l, hl, e⟩ := hn κ hκ hκc
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hvac
  have e2 : (2 * (2 * 2) * M * M) • l = 2 • ((2 * 2) • (M • (M • l))) := by
    simp only [smul_smul]
    congr 1
    ring
  have hu' : (2 * 2) • (M • (M • l)) ∈
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :=
    AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_mem _ hl M) M) _
  have hs : ψ (symplOH S T u (2 • ((2 * 2) • (M • (M • l))))) = 1 := by
    rw [two_nsmul, GlobalTheory.SplitScalar.symplOH_add_right, GlobalTheory.SplitScalar.symplOH_add_self, ← GlobalTheory.Mem.CoefInv.symplO_nsmul,
      ← GlobalTheory.Mem.CoefInv.symplO_nsmul, smul_comm M (2 * 2) u]
    exact GlobalTheory.VacTranslate.psi_four_eq_one hvac.2.lat.1 hw₀ hMu (AddSubgroup.nsmul_mem _ hl M)
  have h := GlobalTheory.SplitScalar.heisO_heisO ψ S T u (2 • ((2 * 2) • (M • (M • l)))) f₀
  rw [hvac.2.lat.1 _ hu', hs, one_smul] at h
  rw [e, e2, h]

end GlobalTheory.VacTranslateLeft

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_fixing_vacuum_translate_source : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f₀ : WO S T → ℂ,
    IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f₀ →
    ∀ u : WO S T, u.map (infPart D) = 0 →
    ∃ U : Subgroup (GA D S), IsOpen (U : Set (GA D S)) ∧ ∀ κ ∈ U, κ ∈ GfC S →
      heisO ψ S T (actO S T κ 1 u) f₀ = heisO ψ S T u f₀ := by
  atlas_forward_decl GlobalTheory.VacTranslateLeft.exists_open_fix_translate_source
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.BotKerLevel

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}

theorem fixTranslate (hX : IsBottomTri W i j X) (t : T) (u : WO A' WW) (hu : u.map (infPart D) = 0) :
    ∃ U : Subgroup (GA D A'), IsOpen (U : Set (GA D A')) ∧ ∀ κ ∈ U, κ ∈ GfC A' →
      X.ω' t (κ, 1) (heisO W.ψ A' WW u X.vac') = heisO W.ψ A' WW u X.vac' := by
  obtain ⟨U₁, hU₁, h₁⟩ := GlobalTheory.T.exists_open_subgroup_fixes_vacuum_definiteBottom hX t
  obtain ⟨U₂, hU₂, h₂⟩ := GlobalTheory.T.exists_open_fixing_vacuum_translate_source D W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.Λ X.rW.Λ hX.is.rigA'.1 hX.is.rigW.1 X.vac'
    hX.is.isVac' u hu
  have hW : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hX.is.weil' t
  refine ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun κ hκ hf => ?_⟩
  rw [hW.om_heis κ 1 u X.vac' hX.is.isVac'.2.theta, h₁ κ hκ.1 hf, h₂ κ hκ.2 hf]

theorem exists_open_fix (hX : IsBottomTri W i j X) (t : T) :
    ∃ U : Subgroup (GA D A'), IsOpen (U : Set (GA D A')) ∧ ∀ κ ∈ U, κ ∈ GfC A' → X.ω' t (κ, 1) (X.f' t) = X.f' t := by
  obtain ⟨n, c, x, hx, e⟩ := GlobalTheory.T.definiteBottom_finiteVector_eq_finite_heisenbergComb hX t
  choose U hU hfix using fun k => fixTranslate hX t (x k) (hx k)
  refine ⟨⨅ k, U k, ?_, fun κ hκ hf => ?_⟩
  · have e2 : (((⨅ k, U k) : Subgroup (GA D A')) : Set (GA D A')) = ⋂ k, (U k : Set (GA D A')) := by
      ext y; simp [Subgroup.mem_iInf]
    rw [e2]
    exact isOpen_iInter_of_finite hU
  · rw [e, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hfix k κ (Subgroup.mem_iInf.1 hκ k) hf]

theorem continuous_finPart (V : HSp D) : Continuous (GlobalTheory.DefiniteClassAvg.finPart V) := by
  have e : GlobalTheory.DefiniteClassAvg.finPart V = fun y => (GlobalTheory.DefiniteClassAvg.realPart V y)⁻¹ * y := by
    funext y
    exact eq_inv_mul_of_mul_eq (GlobalTheory.DefiniteClassAvg.realPart_mul_finPart V y)
  rw [e]
  exact ((GlobalTheory.DefiniteClassAvg.continuous_realPart V).inv).mul continuous_id

theorem finPart_one (V : HSp D) : GlobalTheory.DefiniteClassAvg.finPart V 1 = 1 := by
  have h1 := GlobalTheory.DefiniteClassAvg.finPart_mul_realPart V 1
  have h2 : GlobalTheory.DefiniteClassAvg.finPart V 1 ∈ GinfC V ⊓ GfC V := by
    refine ⟨?_, GlobalTheory.DefiniteClassAvg.finPart_mem V 1⟩
    have : GlobalTheory.DefiniteClassAvg.finPart V 1 = (GlobalTheory.DefiniteClassAvg.realPart V 1)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact (GinfC V).inv_mem (GlobalTheory.DefiniteClassAvg.realPart_mem V 1)
  rw [Formalism.IndefR.TopMult.inf_GinfC_GfC', Subgroup.mem_bot] at h2
  exact h2

theorem eq_of_finE_eq (V : HSp D) {a b : GA D V} (ha : a ∈ GfC V) (hb : b ∈ GfC V) (h : Lev.finE V a = Lev.finE V b) :
    a = b := by
  have h1 : finHom V a = finHom V b := by
    have inj : Function.Injective (Formalism.UG.bc (n := Fin V.rank) (Lev.swapAE D)) := by
      intro x y hxy
      apply Units.ext
      ext p q
      have := congrArg (fun z : GL (Fin V.rank) (Lev.EAf D) => z.1 p q) hxy
      simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at this
      exact (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective this
    exact inj h
  have h2 : a⁻¹ * b ∈ GinfC V ⊓ GfC V := by
    refine ⟨?_, (GfC V).mul_mem ((GfC V).inv_mem ha) hb⟩
    show finHom V (a⁻¹ * b) = 1
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  rw [Formalism.IndefR.TopMult.inf_GinfC_GfC', Subgroup.mem_bot] at h2
  exact (inv_mul_eq_one.1 h2)

theorem exists_level : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ K : Subgroup (GL (Fin A'.rank) (Lev.EAf D)), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel A' K ∧
      ∀ (P : PolF D WW.rank A'.rank) (h : GA D WW), ∀ k ∈ Lev.levA A' K, ∀ g,
        X.ker' W.ψ W.θ t P h (g * k) = X.ker' W.ψ W.θ t P h g := by
  intro D T L sc G W i j A A' WW X hX t
  obtain ⟨U, hUo, hfix⟩ := exists_open_fix hX t
  have hW : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hX.is.weil' t
  have hθ : IsInfFam W.θ := hX.is.isVac'.2.inf
  have hf' : IsThetaFunO W.ψ A' WW (X.f' t) := (GlobalTheory.ConstRatio.theta_f hX.is t).2
  let K : Subgroup (GL (Fin A'.rank) (Lev.EAf D)) := St X.rA'.β ⊓ (U ⊓ GfC A').map (Lev.finE A')
  have hKo : IsOpen ((K.comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    have hU1 : GlobalTheory.DefiniteClassAvg.finPart A' ⁻¹' (U : Set (GA D A')) ∈ nhds (1 : GA D A') :=
      (continuous_finPart A').continuousAt.preimage_mem_nhds (by rw [finPart_one]; exact hUo.mem_nhds U.one_mem)
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ A' X.rA'.β ∅, hU1] with κ h1 h2
    exact ⟨h1.2.1, ⟨GlobalTheory.DefiniteClassAvg.finPart A' κ, ⟨h2, GlobalTheory.DefiniteClassAvg.finPart_mem A' κ⟩,
      GlobalTheory.DefiniteClassAvg.finE_finPart A' κ⟩⟩
  have hKc : IsCompact ((Lev.levA A' K : Subgroup (GA D A')) : Set (GA D A')) := by
    obtain ⟨C, hC, hCm⟩ := GlobalTheory.ParahoricCompact.exists_compact A' X.rA'.β
    refine hC.of_isClosed_subset ((GlobalTheory.Ker.CongTop.isClosed_GfC A').inter
      (Subgroup.isClosed_of_isOpen _ hKo)) fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Lev.mem_levA.1 hk
    exact hCm k hk1 hk2.1
  refine ⟨K, ⟨hKo, hKc⟩, fun P h k hk g => ?_⟩
  obtain ⟨hk1, hk2⟩ := Lev.mem_levA.1 hk
  obtain ⟨u, ⟨huU, huf⟩, hue⟩ := hk2.2
  have hku : k = u := (eq_of_finE_eq A' huf hk1 hue).symm
  have hk3 : X.ω' t (k, 1) (X.f' t) = X.f' t := hku ▸ hfix u huU huf
  show X.ω' t (g * k, h) _ 0 = X.ω' t (g, h) _ 0
  have e : ((g * k, h) : GA D A' × GA D WW) = (g, h) * (k, 1) := by simp
  rw [e, map_mul, Module.End.mul_apply, GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ A' WW _ _ _ hW W.θ hθ k hk1 1 (GfC WW).one_mem
    _ _ _ _ _ P hf', hk3]

end GlobalTheory.BotKerLevel
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openCompactLevel_thetaKernel_bottomTriple : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ K : Subgroup (GL (Fin A'.rank) (Lev.EAf D)), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel A' K ∧
      ∀ (P : PolF D WW.rank A'.rank) (h : GA D WW), ∀ k ∈ Lev.levA A' K, ∀ g,
        X.ker' W.ψ W.θ t P h (g * k) = X.ker' W.ψ W.θ t P h g := by
  atlas_forward_decl GlobalTheory.BotKerLevel.exists_level
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

open scoped ComplexOrder

open GlobalTheory.ClassRegroup GlobalTheory.DefiniteClassAvg GlobalTheory.DefiniteClassReal

namespace GlobalTheory.RowTest.BottomClassSum

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}

theorem weil' (hX : IsBottomTri W i j X) (t : T) :
    IsWeilDatumO W.ψ A' WW (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2))
      ((L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.ω' t) :=
  hX.is.weil' t

theorem theta' (hX : IsBottomTri W i j X) (t : T) (P : PolF D WW.rank A'.rank) :
    IsThetaFunO W.ψ A' WW (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t) P) :=
  GlobalTheory.Chain.InnerSteps.theta_pureTensorO hX.is.isVac'.1 hX.is.isVac'.2.inf X.rA'.s X.rA'.B X.rW.s X.rW.B
    (GlobalTheory.ConstRatio.theta_f hX.is t).2 P

theorem ker'_left (hX : IsBottomTri W i j X) (t : T) (P : PolF D WW.rank A'.rank) (h : GA D WW) :
    ∀ γ ∈ GQ A', ∀ g, X.ker' W.ψ W.θ t P h (γ * g) = X.ker' W.ψ W.θ t P h g := by
  intro γ hγ g
  have hW := weil' hX t
  have hF := theta' hX t P
  show X.ω' t (γ * g, h) _ 0 = X.ω' t (g, h) _ 0
  have e : ((γ * g, h) : GA D A' × GA D WW) = (γ, 1) * (g, h) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hW.om_aut γ hγ 1 (one_mem _) _ (hW.om_pres _ _ hF)

theorem ker'_cont (hX : IsBottomTri W i j X) (t : T) (P : PolF D WW.rank A'.rank) (h : GA D WW) (x : GA D A') :
    Continuous fun k : GinfC A' => X.ker' W.ψ W.θ t P h (x * k) := by
  have hW := weil' hX t
  have hF := theta' hX t P
  exact (hW.om_cont _ hF 0).comp ((continuous_const.mul continuous_subtype_val).prodMk continuous_const)

theorem level_all [Finite T] (t₀ : T) (hX : IsBottomTri W i j X) :
    ∃ K : Subgroup (GL (Fin A'.rank) (Lev.EAf D)), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel A' K ∧
      ∀ (t : T) (P : PolF D WW.rank A'.rank) (h : GA D WW), ∀ k ∈ Lev.levA A' K, ∀ g,
        X.ker' W.ψ W.θ t P h (g * k) = X.ker' W.ψ W.θ t P h g := by
  choose K hK hinv using GlobalTheory.T.exists_openCompactLevel_thetaKernel_bottomTriple hX
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A'
  have hG := hT.2.2.2.2.1
  refine ⟨⨅ t, K t, ⟨?_, ?_⟩, fun t P h k hk g => hinv t P h k ?_ g⟩
  · have e : (((⨅ t, K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) =
        ⋂ t, (((K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) := by
      ext x; simp [Subgroup.mem_iInf]
    rw [e]
    exact isOpen_iInter_of_finite fun t => (hK t).1
  · have hcl : IsClosed ((((⨅ t, K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A'))) := by
      have e : (((⨅ t, K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) =
          ⋂ t, (((K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) := by
        ext x; simp [Subgroup.mem_iInf]
      rw [e]
      exact isClosed_iInter fun t => Subgroup.isClosed_of_isOpen _ (hK t).1
    have e2 : ((Lev.levA A' (⨅ t, K t) : Subgroup (GA D A')) : Set (GA D A')) =
        (Lev.levA A' (K t₀) : Set (GA D A')) ∩ (((⨅ t, K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) := by
      ext x
      simp only [SetLike.mem_coe, Set.mem_inter_iff, Lev.mem_levA, Subgroup.mem_comap]
      exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h1, (Subgroup.mem_iInf.1 h2) t₀⟩, h2⟩, fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩⟩
    rw [e2]
    exact (hK t₀).2.inter_right hcl
  · obtain ⟨hk1, hk2⟩ := Lev.mem_levA.1 hk
    exact Lev.mem_levA.2 ⟨hk1, (Subgroup.mem_iInf.1 hk2) t⟩

theorem integral_eq_classSum_bottom : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (v : ℝ) (N : ℕ) (z : Fin N → GA D A') (w : Fin N → ℕ) (κ : Measure (GinfC A')), 0 < v ∧ (∀ l, z l ∈ GfC A') ∧
      (∀ l, 0 < w l) ∧ κ.IsMulLeftInvariant ∧ IsProbabilityMeasure κ ∧
      ∀ (t : T) (P : PolF D WW.rank A'.rank), ∀ h ∈ GfC WW,
        X.I' W.ψ W.θ t P h = (v : ℂ) * ∑ l, ((w l : ℂ))⁻¹ * ∫ g, X.ker' W.ψ W.θ t P h (z l * (g : GA D A')) ∂κ := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ hL hX

  have hV : ∀ φ : D.host.E →+* ℂ, (A'.gram.map φ).PosDef := fun φ => by
    rw [hX.std'.1, Matrix.map_one φ (map_zero φ) (map_one φ)]
    exact Matrix.PosDef.one
  let V' : HSp D := { A' with sig := fun _ => (A'.rank, 0) }
  have hS' : V'.SigOK := fun τ => GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef (hV τ)
  have hD' : V'.IsDefinite := fun τ => Or.inl rfl
  have hGc : IsCompact (GinfC A' : Set (GA D A')) := Formalism.IndefR.Eqv.isCompact_GinfC (V := V') hS' hD'
  haveI : CompactSpace (GinfC A') := isCompact_iff_compactSpace.1 hGc
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A'
  have hLC := hT.1
  have hSC := hT.2.1
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  have hC := hT.2.2.2.2.2.2

  obtain ⟨K'', hK'', hr⟩ := level_all μ₀ hX
  have hfin0 : Finite (FinCl A' K'') := (finite_finCl_and_gamOrd A' K'' hV hK'').1

  let μ := X.m'
  haveI : μ.IsHaarMeasure := hX.is.meas'.1
  have hfd : IsFundamentalDomain (GQ A') X.fd' μ := hX.is.meas'.2
  let J : Subgroup (GA D A') := K''.comap (Lev.finE A')
  have hJo : IsOpen (J : Set (GA D A')) := hK''.1
  have hJc : IsCompact (J : Set (GA D A')) := by
    refine (hK''.2.mul hGc).of_isClosed_subset (Subgroup.isClosed_of_isOpen J hK''.1) ?_
    intro k hk
    exact ⟨finPart A' k, finPart_mem_levA A' hk, realPart A' k, realPart_mem A' k, finPart_mul_realPart A' k⟩
  have hJtop : μ J ≠ ⊤ := hJc.measure_lt_top.ne
  have hJ0 : μ J ≠ 0 := (hJo.measure_pos μ ⟨1, J.one_mem⟩).ne'
  have hinfJ : GinfC A' ≤ J := by
    show GinfC A' ≤ K''.comap (Lev.finE A')
    rw [GlobalTheory.Mass.Levels.comap_finE]
    exact le_sup_right

  let κ : Measure (GinfC A') := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (GinfC A'))
  haveI hκH : κ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hκ1 : κ Set.univ = 1 := by
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (GinfC A')))
    simpa using this
  haveI : IsProbabilityMeasure κ := ⟨hκ1⟩

  let e := finEquiv A'
  have he : ∀ γ, e (((finPt A').comp (GQ A').subtype) γ) = Bridge.ratF A' γ := fun γ => e.apply_symm_apply _
  have hJe : ∀ a, e a ∈ GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin A' K'' ↔ a ∈ K''.comap (finG A') := fun a => Iff.rfl
  have hy := isReps_transfer _ _ e he _ _ hJe _ (isReps_out A' K'')
  let N := Nat.card (FinCl A' K'')
  let eq : FinCl A' K'' ≃ Fin N := Finite.equivFin _
  let y : FinCl A' K'' → Bridge.Gf A' := fun c => e (Quotient.out c)
  let zc : FinCl A' K'' → GA D A' := fun c => ((Quotient.out c : GfC A') : GA D A')
  have hz : ∀ c, (finHom A').rangeRestrict (zc c) = y c := fun c => rfl
  have hu0 : ∀ x : GA D A', ∃! c, ∃ γ ∈ GQ A', ∃ k ∈ J, x = γ * zc c * k :=
    existsUnique_doubleCoset (finHom A').rangeRestrict (GQ A') (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin A' K'') y hy zc hz
  let z : Fin N → GA D A' := fun l => zc (eq.symm l)
  have hu : ∀ x : GA D A', ∃! l, ∃ γ ∈ GQ A', ∃ k ∈ J, x = γ * z l * k := fun x =>
    (eq.existsUnique_congr_left (p := fun c => ∃ γ ∈ GQ A', ∃ k ∈ J, x = γ * zc c * k)).1 (hu0 x)
  have hfinΓ : ∀ l, {γ : GQ A' | (z l)⁻¹ * (γ : GA D A') * z l ∈ J}.Finite := fun l =>
    GlobalTheory.InnerClassSum.finite_stab_of_measure μ (GQ A') J hfd hJ0 hJtop (z l)
  have him : ∀ l, {γ : GA D A' | γ ∈ GQ A' ∧ (z l)⁻¹ * γ * z l ∈ J} =
      Subtype.val '' {γ : GQ A' | (z l)⁻¹ * (γ : GA D A') * z l ∈ J} := by
    intro l
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩
  have hfin : ∀ l, {γ : GA D A' | γ ∈ GQ A' ∧ (z l)⁻¹ * γ * z l ∈ J}.Finite := fun l =>
    him l ▸ (hfinΓ l).image _
  have hdec : ∀ k ∈ J, ∃ k' ∈ Lev.levA A' K'', ∃ w : GinfC A', k = k' * (GinfC A').subtype w := fun k hk =>
    ⟨finPart A' k, finPart_mem_levA A' hk, ⟨realPart A' k, realPart_mem A' k⟩, (finPart_mul_realPart A' k).symm⟩
  have hcomm : ∀ k ∈ Lev.levA A' K'', ∀ w : GinfC A', k * (GinfC A').subtype w = (GinfC A').subtype w * k :=
    fun k hk w => (Formalism.IndefR.Eqv.Act.comm_inf_fin w.2 (Subgroup.mem_inf.1 hk).1).symm
  have hrt : ∀ w : GinfC A', MeasurePreserving (· * (GinfC A').subtype w) μ μ := fun w =>
    measurePreserving_mul_right_of_mem μ J hJo hJ0 hJtop (hinfJ w.2)
  refine ⟨(μ J).toReal, N, z, fun l => {γ : GA D A' | γ ∈ GQ A' ∧ (z l)⁻¹ * γ * z l ∈ J}.ncard, κ,
    ENNReal.toReal_pos hJ0 hJtop, fun l => (Quotient.out (eq.symm l)).2, fun l => ?_, inferInstance, inferInstance,
    fun t P h _ => ?_⟩
  · exact (Set.ncard_pos (hfin l)).2 ⟨1, (GQ A').one_mem, by simp [J.one_mem]⟩
  · have hcont : Continuous (X.ker' W.ψ W.θ t P h) :=
      continuous_of_level A' K'' hK''.1 _ (fun k hk g => hr t P h k hk g) (ker'_cont hX t P h)
    obtain ⟨-, heq⟩ := integral_eq_sum_avg (GA D A') μ (GQ A') J (Lev.levA A' K'') X.fd' hfd hJo hJtop (GinfC A') κ
      (GinfC A').subtype continuous_subtype_val hrt hdec hcomm (Fin N) z hu hfin (X.ker' W.ψ W.θ t P h) hcont
      (ker'_left hX t P h) (fun k hk g => hr t P h k hk g)
    exact heq
end GlobalTheory.RowTest.BottomClassSum
end
end
