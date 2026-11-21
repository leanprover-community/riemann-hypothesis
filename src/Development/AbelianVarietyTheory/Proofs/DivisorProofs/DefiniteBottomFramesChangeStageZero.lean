import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixAdjointJointAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFrameConjIntegralSmulOfIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomWeilActionFockPureTensorSubstituti
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawsRescaleWithS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocKIntMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixAdjointSupportedOfConjHalf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicUnitarySplitPlaceComponent
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SquareCharUnit

theorem exists_root_of_locIn {D : D7} {K : Type} [Field K] (σ : K →+* ℂ) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E)
    (h : ChrEq c χ) (hL : LocIn σ χ) (x : (AE D)ˣ) (hx : Formalism.L2.Pj.FinUnit x) :
    ∃ ζ : K, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧ σ ζ = ((c x : Circle) : ℂ) := by
  have hmem : ((c x : Circle) : ℂ) ∈ σ.fieldRange := by
    obtain ⟨j, j1, j2, j3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
    obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D j j1 j2 (GlobalTheory.PlaceIdem.exists_isPlIdem D j j1 j2 j3) c χ h
    obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
      (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom x)
    rw [hprod x hx.1 S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS']
    exact prod_mem fun P _ => hL P _
  obtain ⟨ζ, hζ⟩ := hmem
  obtain ⟨-, -, -, m, hm, hpow⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c h.1.1
  refine ⟨ζ, ⟨m, hm, σ.injective ?_⟩, hζ⟩
  rw [map_pow, map_one, hζ, ← Circle.coe_pow, hpow x hx, Circle.coe_one]

theorem nu_finUnit_root : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (μ₀ : T), Lc.Is μ₀ →
    CharsIn G D.what₂.embLL → ∀ (i j : Fin D.R.m) (t : T) (x : (AE D)ˣ), Formalism.L2.Pj.FinUnit x →
    ∃ ζ : D.what₂.LL, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧
      D.what₂.embLL ζ = (((Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) /
        (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) x : Circle) : ℂ) := by
  intro D T Lc sc G μ₀ hL hC i j t x hx
  have hi := i.2
  obtain ⟨a, ⟨n₁, h₁, e₁⟩, ha⟩ := exists_root_of_locIn D.what₂.embLL _ _ (hL.mu0 j) (hC.mu0 j) x hx
  obtain ⟨b, ⟨n₂, h₂, e₂⟩, hb⟩ := exists_root_of_locIn D.what₂.embLL _ _ (hL.xi t) (hC.xi t) x hx
  obtain ⟨c, ⟨n₃, h₃, e₃⟩, hc⟩ := exists_root_of_locIn D.what₂.embLL _ _
    (G.ch.chi_eq (D.R.m - i) (by omega) (by omega)) (hC.chi (D.R.m - i) (by omega) (by omega)) x hx
  refine ⟨a * b / c, ⟨n₁ * n₂ * n₃, by positivity, ?_⟩, ?_⟩
  · rw [div_pow, mul_pow]
    have f₁ : a ^ (n₁ * n₂ * n₃) = 1 := by rw [mul_assoc, pow_mul, e₁, one_pow]
    have f₂ : b ^ (n₁ * n₂ * n₃) = 1 := by rw [mul_right_comm, mul_comm, pow_mul, e₂, one_pow]
    have f₃ : c ^ (n₁ * n₂ * n₃) = 1 := by rw [mul_comm, pow_mul, e₃, one_pow]
    rw [f₁, f₂, f₃, one_mul, div_one]
  · rw [mul_div_mul_right_eq_div, map_div₀, map_mul, ha, hb, hc, MonoidHom.div_apply, Circle.coe_div]
    congr 1

end GlobalTheory.SquareCharUnit
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridSquareCharQuotient_finiteUnitIdele_rootOfUnity : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (μ₀ : T), Lc.Is μ₀ →
    CharsIn G D.what₂.embLL → ∀ (i j : Fin D.R.m) (t : T) (x : (AE D)ˣ), Formalism.L2.Pj.FinUnit x →
    ∃ ζ : D.what₂.LL, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧
      D.what₂.embLL ζ = (((Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) /
        (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) x : Circle) : ℂ) := by
  atlas_forward_decl GlobalTheory.SquareCharUnit.nu_finUnit_root
end

section
namespace GlobalTheory.StdSndSB

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta

variable {D : D7}

local notation "OO" => Formalism.L2.Herm.intAf D.host.F D.host.E

private theorem isIntM_rightBlock {k d a : ℕ} {Y : Matrix (Fin k) (Fin d) (EAf D)} (h : IsIntM Y) :
    IsIntM (rightBlock a Y) := fun i j => by
  unfold rightBlock
  split_ifs
  · exact h _ _
  · exact zero_mem _

private theorem rightBlock_shift {k d a : ℕ} {Y Y' W : Matrix (Fin k) (Fin d) (EAf D)} {c : EAf D}
    (h : ∀ i j, Y' i j = Y i j + c * W i j) (i j : Fin k) :
    rightBlock a Y' i j = rightBlock a Y i j + c * rightBlock a W i j := by
  unfold rightBlock
  split_ifs
  · exact h _ _
  · rw [mul_zero, add_zero]

set_option maxHeartbeats 1000000 in
private theorem stdSnd_shift {ν : (AE D)ˣ →* Circle} {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S)
    {I : Ideal (𝓞 D.host.E)} {n₀ n c : ℕ} (hn₀ : ((n₀ : ℕ) : 𝓞 D.host.E) ∈ I)
    (hl : ∀ x, Formalism.L2.Pj.FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = n • y) → ν x = 1)
    (hc : ∀ P ∈ S, ((c : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (a : ℕ) (A WW : HSp D) (βA : GL (Fin A.rank) (EAf D))
    (βW : GL (Fin WW.rank) (EAf D)) {t t' : WO A WW} (hh : IsHalf (cA D e) t' ↔ IsHalf (cA D e) t)
    {W : Matrix (Fin A.rank) (Fin WW.rank) (EAf D)} (hW : IsIntM W)
    (h : ∀ i j, dualCoord A WW βA βW t' i j = dualCoord A WW βA βW t i j + ((n₀ * (n * c) : ℕ) : EAf D) * W i j) :
    stdSnd ν e I a A WW βA βW t' = stdSnd ν e I a A WW βA βW t := by
  have hW1 : ∀ i j, ((n * c : ℕ) : EAf D) * W i j ∈ OO := fun i j => mul_mem (natCast_mem _ _) (hW i j)
  have hW2 : ∀ i j, (n₀ : EAf D) * (((n * c : ℕ) : EAf D) * W i j) ∈ OO := fun i j => mul_mem (natCast_mem _ _) (hW1 i j)
  have ha : ∀ i j, dualCoord A WW βA βW t' i j =
      dualCoord A WW βA βW t i j + (n₀ : EAf D) * (((n * c : ℕ) : EAf D) * W i j) := fun i j => by
    rw [h, Nat.cast_mul n₀, mul_assoc]
  have hb : ∀ i j, dualCoord A WW βA βW t i j =
      dualCoord A WW βA βW t' i j + (n₀ : EAf D) * (-(((n * c : ℕ) : EAf D) * W i j)) := fun i j => by
    rw [ha, mul_neg, add_neg_cancel_right]
  have hint : IsIntM (dualCoord A WW βA βW t') ↔ IsIntM (dualCoord A WW βA βW t) :=
    forall_congr' fun i => forall_congr' fun j => by
      rw [ha]
      exact add_mem_cancel_right (hW2 i j)
  have hid : (∀ i j, j.1 < a → InId I (dualCoord A WW βA βW t' i j)) ↔
      ∀ i j, j.1 < a → InId I (dualCoord A WW βA βW t i j) :=
    ⟨fun H i j hi => inId_shift hn₀ (neg_mem (hW1 i j)) (hb i j) (H i j hi),
      fun H i j hi => inId_shift hn₀ (hW1 i j) (ha i j) (H i j hi)⟩
  unfold stdSnd
  by_cases hcnd : IsHalf (cA D e) t ∧ IsIntM (dualCoord A WW βA βW t) ∧
      ∀ i j, j.1 < a → InId I (dualCoord A WW βA βW t i j)
  · rw [if_pos hcnd, if_pos ⟨hh.2 hcnd.1, hint.2 hcnd.2.1, hid.2 hcnd.2.2⟩]
    refine (unitChar_congr he hl hc (isIntM_rightBlock hcnd.2.1)
      (Z := rightBlock a fun i j => (n₀ : EAf D) * W i j)
      (isIntM_rightBlock fun i j => mul_mem (natCast_mem _ _) (hW i j))
      (rightBlock_shift (c := ((n * c : ℕ) : EAf D)) fun i j => ?_)).symm
    rw [h, Nat.cast_mul n₀]
    ring
  · rw [if_neg hcnd, if_neg fun h' => hcnd ⟨hh.1 h'.1, hint.1 h'.2.1, hid.1 h'.2.2⟩]

private theorem dualCoord_add (A WW : HSp D) (βA : GL (Fin A.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D))
    (x y : WO A WW) : dualCoord A WW βA βW (x + y) = dualCoord A WW βA βW x + dualCoord A WW βA βW y := by
  unfold dualCoord
  rw [GlobalTheory.PlaceVec.frMapAdj_add, smul_add]

private theorem mul_nsmul_mul_eq_nsmul_mul_nsmul {R : Type} [CommRing R] (k l : ℕ) (x y : R) : (k * l) • (x * y) = (k • x) * (l • y) := by
  simp only [nsmul_eq_mul]
  push_cast
  ring

private theorem inv_aux {R : Type} [CommRing R] (k : ℕ) {x x' : R} (h : x' * x = 1) (y : R) :
    k • y = (k • x') * (x * y) := by
  simp only [nsmul_eq_mul]
  linear_combination (-(k : R) * y) * h

set_option maxHeartbeats 1000000 in
private theorem dualCoord_up (A WW : HSp D) (βA : GL (Fin A.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) :
    ∃ k : ℕ, 0 < k ∧ ∀ x : WO A WW, IsIntM (x.map (toEAf D)) → IsIntM (k • dualCoord A WW βA βW x) := by
  obtain ⟨k, hk, h⟩ := GlobalTheory.PlaceVec.frMapAdj_up A WW βA βW
  obtain ⟨d, hd, hx⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_int (eToEAf D D.host.xi0)
  refine ⟨d * k, mul_pos hd hk, fun x hi i j => ?_⟩
  change (d * k) • (eToEAf D D.host.xi0 * frMapAdj A WW βA βW x i j) ∈ OO
  rw [mul_nsmul_mul_eq_nsmul_mul_nsmul]
  exact mul_mem hx (h x hi i j)

set_option maxHeartbeats 1000000 in
private theorem dualCoord_down (A WW : HSp D) (βA : GL (Fin A.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) :
    ∃ k : ℕ, 0 < k ∧ ∀ x : WO A WW, IsIntM (dualCoord A WW βA βW x) → IsIntM ((k • x).map (toEAf D)) := by
  obtain ⟨k, hk, h⟩ := GlobalTheory.PlaceVec.frMapAdj_down A WW βA βW
  obtain ⟨d, hd, hx⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_int (eToEAf D D.host.xi0⁻¹)
  have h1 : eToEAf D D.host.xi0⁻¹ * eToEAf D D.host.xi0 = 1 := by
    rw [← RingHom.map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), RingHom.map_one]
  refine ⟨k * d, mul_pos hk hd, fun x hi => ?_⟩
  have hn : frMapAdj A WW βA βW (d • x) = d • frMapAdj A WW βA βW x :=
    (AddMonoidHom.mk' _ (GlobalTheory.PlaceVec.frMapAdj_add A WW βA βW)).map_nsmul d x
  rw [mul_smul, GlobalTheory.PlaceVec.map_toEAf_nsmul]
  refine h (d • x) fun i j => ?_
  rw [hn]
  change d • frMapAdj A WW βA βW x i j ∈ OO
  rw [inv_aux d h1]
  exact mul_mem hx (hi i j)

set_option maxHeartbeats 1000000 in

private theorem stdSnd_isSB {ν : (AE D)ˣ →* Circle} (hν : Continuous ν) {e : AE D} {S : Finset (Pl D.host.E)}
    (he : IsIdemSum e S) {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) (a : ℕ) (A WW : HSp D) (βA : GL (Fin A.rank) (EAf D))
    (βW : GL (Fin WW.rank) (EAf D)) (Λ : AddSubgroup (WO A WW))
    (hB : ∃ M : ℕ, 0 < M ∧ ∀ u ∈ Λ, IsIntM (dualCoord A WW βA βW (M • u)))
    (hC : ∃ K : ℕ, 0 < K ∧ ∀ t : WO A WW, IsHalf (cA D e) t → IsIntM (dualCoord A WW βA βW t) → K • t ∈ Λ) :
    IsSBHalf (cA D e) Λ (stdSnd ν e I a A WW βA βW) := by
  obtain ⟨M, hM, hB⟩ := hB
  obtain ⟨K, hK, hC⟩ := hC
  obtain ⟨n, hn, hl, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν
  obtain ⟨n₀, hn₀, hnI⟩ : ∃ n₀ : ℕ, 0 < n₀ ∧ ((n₀ : ℕ) : 𝓞 D.host.E) ∈ I :=
    ⟨_, Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h), Ideal.absNorm_mem I⟩
  obtain ⟨c, hc, hcS⟩ := GlobalTheory.PlaceVec.exists_nat_mem_places S
  have hGn : ∀ (k : ℕ) x, dualCoord A WW βA βW (k • x) = k • dualCoord A WW βA βW x := fun k x =>
    (AddMonoidHom.mk' _ (dualCoord_add A WW βA βW)).map_nsmul k x
  refine ⟨fun t ht => ?_, (n₀ * (n * c)) * (K * M), Nat.mul_pos (Nat.mul_pos hn₀ (Nat.mul_pos hn hc)) (Nat.mul_pos hK hM),
    fun u hu hh t => ?_, fun t ht => ?_⟩
  · unfold stdSnd at ht
    by_contra h
    exact ht (if_neg fun h' => h h'.1)
  · refine stdSnd_shift he hnI hl hcS a A WW βA βW (W := K • dualCoord A WW βA βW (M • u))
      ?_ (GlobalTheory.PlaceVec.isIntM_nsmul (hB u hu) K) fun i j => ?_
    · rw [GlobalTheory.PlaceModel.isHalf_iff A WW, GlobalTheory.PlaceModel.isHalf_iff A WW]
      exact AddSubgroup.add_mem_cancel_right _ (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff A WW).1 hh) _)
    · rw [dualCoord_add, mul_smul, mul_smul K, hGn, hGn K, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]
  · have h : IsHalf (cA D e) t ∧ IsIntM (dualCoord A WW βA βW t) := by
      unfold stdSnd at ht
      by_contra h
      exact ht (if_neg fun h' => h ⟨h'.1, h'.2.1⟩)
    rw [show (n₀ * (n * c)) * (K * M) = ((n₀ * (n * c)) * M) * K by ring, mul_smul]
    exact nsmul_mem (hC t h.1 h.2) _

set_option maxHeartbeats 1000000 in
private theorem main (ν : (AE D)ˣ →* Circle) (hν : Continuous ν) (e : AE D) (S : Finset (Pl D.host.E))
    (he : IsIdemSum e S) (I : Ideal (𝓞 D.host.E)) (hI : I ≠ ⊥) (a : ℕ) (A WW : HSp D)
    (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E))
    (hA : IsSelfDualC A ΛA) (hW : IsSelfDualC WW ΛW) (βA : GL (Fin A.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) :
    IsSBHalf (cA D e) (latO A WW (ΛA : Set (Fin A.rank → D.host.E)) (ΛW : Set (Fin WW.rank → D.host.E)) fun _ => True)
      (stdSnd ν e I a A WW βA βW) := by
  have hinf := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  obtain ⟨k₁, hk₁, h₁⟩ := dualCoord_up A WW βA βW
  obtain ⟨k₂, hk₂, h₂⟩ := dualCoord_down A WW βA βW
  obtain ⟨k₃, hk₃, h₃⟩ := GlobalTheory.PlaceVec.exists_nsmul_latO_int (S := A) (T := WW) hA.1.fg hW.1.fg
  obtain ⟨k₄, hk₄, h₄⟩ := GlobalTheory.PlaceVec.exists_nsmul_int_mem_latO hA.1 hW.1
  refine stdSnd_isSB hν he hI a A WW βA βW _ ⟨k₁ * k₃, mul_pos hk₁ hk₃, fun u hu => ?_⟩
    ⟨k₄ * k₂, mul_pos hk₄ hk₂, fun t ht hi => ?_⟩
  · have hn : dualCoord A WW βA βW (k₁ • k₃ • u) = k₁ • dualCoord A WW βA βW (k₃ • u) :=
      (AddMonoidHom.mk' _ (dualCoord_add A WW βA βW)).map_nsmul k₁ _
    rw [mul_smul, hn]
    exact h₁ _ (by rw [GlobalTheory.PlaceVec.map_toEAf_nsmul]; exact h₃ u hu)
  · rw [mul_smul]
    exact h₄ (k₂ • t) (GlobalTheory.PlaceVec.half_infPart hinf (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff A WW).1 ht) _)) (h₂ t hi)

end

end GlobalTheory.StdSndSB

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.standardThetaPair_second_isSchwartzBruhat_conjHalf : ∀ {D : D7} (ν : (AE D)ˣ →* Circle), Continuous ν → ∀ (e : AE D) (S : Finset (Formalism.L2.DIV.Pl D.host.E)),
    IsIdemSum e S → ∀ (I : Ideal (𝓞 D.host.E)), I ≠ ⊥ → ∀ (a : ℕ) (A' WW : HSp D)
    (ΛA : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A' ΛA → IsSelfDualC WW ΛW → ∀ (βA : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)),
    IsSBHalf (cA D e) (latO A' WW (ΛA : Set (Fin A'.rank → D.host.E)) (ΛW : Set (Fin WW.rank → D.host.E)) fun _ => True)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a A' WW βA βW) :=
  fun ν hν e S he I hI a A WW ΛA ΛW hA hW βA βW => GlobalTheory.StdSndSB.main ν hν e S he I hI a A WW ΛA ΛW hA hW βA βW
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.frameChangeUnitDeterminant

open Formalism.IndefR.Datum

variable {D : D7}

local notation "OO" => Formalism.L2.Herm.intAf D.host.F D.host.E

private theorem isIntM_mul {b a c : ℕ} {N : Matrix (Fin b) (Fin a) (EAf D)} {κ : Matrix (Fin a) (Fin c) (EAf D)}
    (hN : IsIntM N) (hκ : IsIntM κ) : IsIntM (N * κ) := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => mul_mem (hN i l) (hκ l j)

private theorem frame_ratio_int {n : ℕ} {β β' : GL (Fin n) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (h : Formalism.L2.DIV.IsFrame β Λ) (h' : Formalism.L2.DIV.IsFrame β' Λ) : IsIntM ((β'⁻¹).val * β.val) := fun i j => by
  have hv : (fun k => β.val k j) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    refine (h _).2 fun i' => ?_
    have e1 : (β⁻¹).val.mulVec (fun k => β.val k j) i' =
        ((β⁻¹).val * β.val) i' j := by
      simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [e1, Units.inv_mul, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have := (h' _).1 hv i
  simpa only [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this

private theorem inId_mul {b a c : ℕ} {I : Ideal (𝓞 D.host.E)} {N : Matrix (Fin b) (Fin a) (EAf D)}
    {κ : Matrix (Fin a) (Fin c) (EAf D)} (hκ : IsIntM κ) (i : Fin b) (hN : ∀ l, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (N i l))
    (j : Fin c) : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I ((N * κ) i j) := by
  have hm : (N * κ) i j ∈ OO := by
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => mul_mem (hN l).1 (hκ l j)
  refine ⟨hm, ?_⟩
  have e : (⟨(N * κ) i j, hm⟩ : OO) = ∑ l, (⟨N i l, (hN l).1⟩ : OO) * ⟨κ l j, hκ l j⟩ := Subtype.ext (by
    show (N * κ) i j = _
    rw [Matrix.mul_apply]
    push_cast
    rfl)
  rw [e]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hN l).2

private theorem topL_mul {b a : ℕ} (N : Matrix (Fin b) (Fin a) (EAf D)) (κ : Matrix (Fin a) (Fin a) (EAf D)) :
    topL a (N * κ) = topL a N * κ := by
  ext i j
  simp only [topL, Matrix.mul_apply]
  by_cases hi : i.1 < b
  · simp [hi]
  · simp [hi]

end GlobalTheory.frameChangeUnitDeterminant

namespace GlobalTheory.frameChangeUnitDeterminant

open Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

variable {D : D7}

local notation "OO" => Formalism.L2.Herm.intAf D.host.F D.host.E

private theorem det_int {k : ℕ} {N : Matrix (Fin k) (Fin k) (EAf D)} (hN : IsIntM N) : N.det ∈ OO := by
  let A : Matrix (Fin k) (Fin k) OO := fun i j => ⟨N i j, hN i j⟩
  have eA : N.det = ((A.det : OO) : EAf D) := by
    rw [show N = (OO).subtype.mapMatrix A from rfl]
    exact (RingHom.map_det (OO).subtype A).symm
  rw [eA]
  exact A.det.2

private theorem isUnitDet_unique {e : AE D} {k : ℕ} {N : Matrix (Fin k) (Fin k) (EAf D)} {x x' : (AE D)ˣ}
    (h : IsUnitDet e N x) (h' : IsUnitDet e N x') : x = x' :=
  Units.ext (StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.eq_of_parts (h.1.trans h'.1.symm) (h.2.1.trans h'.2.1.symm))

private theorem idem_mul {R : Type} [CommRing R] {ε a b : R} (hε : ε * ε = ε) :
    (1 - ε + ε * a) * (1 - ε + ε * b) = 1 - ε + ε * (a * b) := by
  linear_combination (a * b - a - b + 1) * hε

private theorem succ_mul_succ_sub_one_div_succ {R : Type} [CommRing R] {ε z y yi a b : R} (hε : ε * ε = ε) (hz : z = 1 - ε + ε * (a * b))
    (hy : y = 1 - ε + ε * b) (hyy : y * yi = 1) : z * yi = 1 - ε + ε * a := by
  subst hz hy
  linear_combination (1 - ε + ε * a) * hyy - (a * b - a - b + 1) * yi * hε

private theorem isUnitDet_mul {e : AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S) {k : ℕ}
    {L κ : Matrix (Fin k) (Fin k) (EAf D)} {x y : (AE D)ˣ} (hx : IsUnitDet e L x) (hy : IsUnitDet e κ y) :
    IsUnitDet e (L * κ) (x * y) := by
  have hε : toEAf D e * toEAf D e = toEAf D e := by rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, map_mul, hx.1, hy.1, mul_one]
  · rw [Units.val_mul, map_mul, hx.2.1, hy.2.1, Matrix.det_mul, idem_mul hε]
  · rw [_root_.mul_inv_rev, Units.val_mul, map_mul]
    exact mul_mem hy.2.2 hx.2.2

set_option maxHeartbeats 1000000 in
private theorem isUnitDet_div {e : AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S) {k : ℕ}
    {L κ : Matrix (Fin k) (Fin k) (EAf D)} (hκ : IsIntM κ) {z y : (AE D)ˣ} (hz : IsUnitDet e (L * κ) z)
    (hy : IsUnitDet e κ y) : IsUnitDet e L (z * y⁻¹) := by
  have hε : toEAf D e * toEAf D e = toEAf D e := by rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  have hE := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
  have hyy : toEAf D (y : AE D) * toEAf D ((y⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hinv : infPart D ((y⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    have := congrArg (infPart D) (Units.mul_inv y)
    rwa [map_mul, hy.1, one_mul, map_one] at this
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, map_mul, hz.1, hinv, mul_one]
  · rw [Units.val_mul, map_mul]
    exact succ_mul_succ_sub_one_div_succ hε (hz.2.1.trans (by rw [Matrix.det_mul])) hy.2.1 hyy
  · have e0 : (z * y⁻¹)⁻¹ = y * z⁻¹ := by rw [_root_.mul_inv_rev, inv_inv]
    rw [e0]
    rw [Units.val_mul]
    rw [map_mul]
    refine mul_mem ?_ hz.2.2
    rw [hy.2.1]
    exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE (det_int hκ))

private theorem unitChar_mul (ν : (AE D)ˣ →* Circle) {e : AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S)
    {k : ℕ} (L κ : Matrix (Fin k) (Fin k) (EAf D)) (hκ : IsIntM κ) {y : (AE D)ˣ} (hy : IsUnitDet e κ y) :
    unitChar ν e (L * κ) = (((ν y)⁻¹ : Circle) : ℂ) * unitChar ν e L := by
  unfold unitChar
  by_cases hL : ∃ x, IsUnitDet e L x
  · have hLκ : ∃ x, IsUnitDet e (L * κ) x := ⟨_, isUnitDet_mul he hL.choose_spec hy⟩
    rw [dif_pos hL, dif_pos hLκ, isUnitDet_unique hLκ.choose_spec (isUnitDet_mul he hL.choose_spec hy), map_mul,
      _root_.mul_inv_rev, Circle.coe_mul]
  · have hLκ : ¬ ∃ x, IsUnitDet e (L * κ) x := fun ⟨z, hz⟩ => hL ⟨_, isUnitDet_div he hκ hz hy⟩
    rw [dif_neg hL, dif_neg hLκ, mul_zero]

end GlobalTheory.frameChangeUnitDeterminant

namespace GlobalTheory.frameChangeUnitDeterminant

open Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

variable {D : D7}

local notation "OO" => Formalism.L2.Herm.intAf D.host.F D.host.E

private theorem half_mul {e : AE D} {m m' n : ℕ} (P : Matrix (Fin m) (Fin m') (AE D)) {y : Mx D m' n} (h : IsHalf e y) :
    IsHalf e (P * y : Mx D m n) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, h l j]

private theorem pull_eq (A WW : HSp D) (k : GA D WW) (y : WO A WW) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt (GlobalTheory.Grid.neg A) WW 1 k y =
      HMul.hMul (mt WW k⁻¹) (y : Matrix (Fin WW.rank) (Fin A.rank) (AE D)) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt
  rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.mul_one]

private theorem exists_unitDet {e : AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S) {k : ℕ}
    {κ κ' : Matrix (Fin k) (Fin k) (EAf D)} (hκ : IsIntM κ) (hκ' : IsIntM κ') (hkk : κ * κ' = 1) :
    ∃ x, IsUnitDet e κ x ∧ Formalism.L2.Pj.FinUnit x := by
  have hε : toEAf D e * toEAf D e = toEAf D e := by rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  have hE := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
  have hu : (1 - toEAf D e + toEAf D e * κ.det) * (1 - toEAf D e + toEAf D e * κ'.det) = 1 := by
    rw [idem_mul hε, ← Matrix.det_mul, hkk, Matrix.det_one, mul_one, sub_add_cancel]
  obtain ⟨x, a, b, c⟩ := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.exists_unit hu
  have m1 : 1 - toEAf D e + toEAf D e * κ.det ∈ OO := add_mem (sub_mem (one_mem _) hE) (mul_mem hE (det_int hκ))
  have m2 : 1 - toEAf D e + toEAf D e * κ'.det ∈ OO := add_mem (sub_mem (one_mem _) hE) (mul_mem hE (det_int hκ'))
  exact ⟨x, ⟨a, b, c ▸ m2⟩, a, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (b ▸ m1),
    GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (c ▸ m2)⟩

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in

private theorem smul_inv_eq {n : ℕ} {ε : EAf D} {g B : GL (Fin n) (EAf D)} (h : ε • g.val = ε • B.val) :
    ε • (g⁻¹).val = ε • (B⁻¹).val := by
  calc ε • (g⁻¹).val = (g⁻¹).val * (ε • B.val) * (B⁻¹).val := by
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    _ = (g⁻¹).val * (ε • g.val) * (B⁻¹).val := by rw [h]
    _ = ε • (B⁻¹).val := by rw [Matrix.mul_smul, Units.inv_mul, Matrix.smul_mul, Matrix.one_mul]

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 2000000 in

private theorem frMapO_change {e : AE D} (A WW : HSp D) (βA βA' : GL (Fin A.rank) (EAf D)) (βW βW' : GL (Fin WW.rank) (EAf D))
    (k : GA D WW) (hk : ∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE WW k).1 i j = toEAf D e * (βW' * βW⁻¹).1 i j)
    {y : WO A WW} (hh : IsHalf e y) :
    frMapO A WW βA βW (HMul.hMul (mt WW k⁻¹) (y : Matrix (Fin WW.rank) (Fin A.rank) (AE D))) =
      HMul.hMul (frMapO A WW βA' βW' y) (HMul.hMul (βA'⁻¹).val βA.val : Matrix (Fin A.rank) (Fin A.rank) (EAf D)) := by
  have hy : toEAf D e • y.map (toEAf D) = y.map (toEAf D) := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, ← map_mul, hh i j]
  have hK : toEAf D e • (Formalism.IndefR.Lev.finE WW k).val = toEAf D e • (βW' * βW⁻¹).val := by
    ext i j
    exact hk i j
  have hKi := smul_inv_eq hK
  have hm : (mt WW k⁻¹).map (toEAf D) = ((Formalism.IndefR.Lev.finE WW k)⁻¹).val := by
    rw [← map_inv]
    rfl
  have hB : ((βW' * βW⁻¹)⁻¹ : GL (Fin WW.rank) (EAf D)) = βW * βW'⁻¹ := by rw [_root_.mul_inv_rev, inv_inv]
  have key : ((Formalism.IndefR.Lev.finE WW k)⁻¹).val * y.map (toEAf D) = (βW * βW'⁻¹).val * y.map (toEAf D) := by
    rw [← hy, Matrix.mul_smul, ← Matrix.smul_mul, hKi, Matrix.smul_mul, ← Matrix.mul_smul, hB]
  unfold frMapO
  rw [Matrix.map_mul, hm, Matrix.mul_assoc (βW⁻¹).val, key, Units.val_mul]
  simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc _ βA'.val, Units.mul_inv, Matrix.mul_one]

end GlobalTheory.frameChangeUnitDeterminant

namespace GlobalTheory.frameChangeUnitDeterminant

open Formalism.IndefR.Datum

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 4000000 in

private theorem stdFst_change_frames : ∀ {D : D7} (ν : (AE D)ˣ →* Circle) (e : AE D) (S : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e S →
    ∀ (I : Ideal (𝓞 D.host.E)) (A WW : HSp D) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (βA βA' : GL (Fin A.rank) (EAf D)), Formalism.L2.DIV.IsFrame βA ΛA → Formalism.L2.DIV.IsFrame βA' ΛA →
    ∀ (βW βW' : GL (Fin WW.rank) (EAf D)) (k : GA D WW), SuppAt e WW k →
    (∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE WW k).1 i j = toEAf D e * (βW' * βW⁻¹).1 i j) →
    ∃ x : (AE D)ˣ, Formalism.L2.Pj.FinUnit x ∧ ∀ y : WO A WW,
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA' βW' y =
        ((ν x : Circle) : ℂ) * GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt (GlobalTheory.Grid.neg A) WW 1 k y) := by
  intro D ν e S he I A WW ΛA βA βA' hA hA' βW βW' k _ hk
  have hκ := frame_ratio_int hA hA'
  have hκ' := frame_ratio_int hA' hA
  have hkk : (βA'⁻¹).val * βA.val * ((βA⁻¹).val * βA'.val) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc βA.val, Units.mul_inv, Matrix.one_mul, Units.inv_mul]
  obtain ⟨x, hx, hxu⟩ := exists_unitDet he hκ hκ' hkk
  refine ⟨x, hxu, fun y => ?_⟩
  rw [pull_eq]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  by_cases hh : IsHalf e y
  · have hh' : IsHalf e (HMul.hMul (mt WW k⁻¹) (y : Matrix (Fin WW.rank) (Fin A.rank) (AE D)) : Mx D WW.rank A.rank) :=
      half_mul _ hh
    rw [frMapO_change A WW βA βA' βW βW' k hk hh, topL_mul,
      unitChar_mul ν he _ _ hκ hx]
    have hI : IsIntM (frMapO A WW βA' βW' y * ((βA'⁻¹).val * βA.val)) ↔ IsIntM (frMapO A WW βA' βW' y) := by
      refine ⟨fun h => ?_, fun h => isIntM_mul h hκ⟩
      have := isIntM_mul h hκ'
      rwa [Matrix.mul_assoc, hkk, Matrix.mul_one] at this
    have hR : (∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I ((frMapO A WW βA' βW' y * ((βA'⁻¹).val * βA.val)) i j)) ↔
        ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (frMapO A WW βA' βW' y i j) := by
      refine ⟨fun h i j hi => ?_, fun h i j hi => inId_mul hκ i (fun l => h i l hi) j⟩
      have := inId_mul hκ' i (fun l => h i l hi) j
      rwa [Matrix.mul_assoc, hkk, Matrix.mul_one] at this
    by_cases hc : IsIntM (frMapO A WW βA' βW' y) ∧
        ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (frMapO A WW βA' βW' y i j)
    · rw [if_pos ⟨hh, hc⟩, if_pos ⟨hh', hI.2 hc.1, hR.2 hc.2⟩, ← mul_assoc, ← Circle.coe_mul, mul_inv_cancel,
        Circle.coe_one, one_mul]
    · rw [if_neg fun h => hc h.2, if_neg fun h => hc ⟨hI.1 h.2.1, hR.1 h.2.2⟩, mul_zero]
  · have hh' : ¬ IsHalf e (HMul.hMul (mt WW k⁻¹) (y : Matrix (Fin WW.rank) (Fin A.rank) (AE D)) : Mx D WW.rank A.rank) :=
      fun h => hh (by
        have := half_mul (mt WW k) h
        rwa [← Matrix.mul_assoc, ← GlobalTheory.AdelicLatMove.mt_mul, mul_inv_cancel, GlobalTheory.AdelicLatMove.mt_one,
          Matrix.one_mul] at this)
    rw [if_neg fun h => hh h.1, if_neg fun h => hh' h.1, mul_zero]

end GlobalTheory.frameChangeUnitDeterminant

end

theorem _root_.GlobalTheory.T.standardThetaPair_first_frameChange_unitTranslate : ∀ {D : D7} (ν : (AE D)ˣ →* Circle) (e : AE D) (S : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e S →
    ∀ (I : Ideal (𝓞 D.host.E)) (A WW : HSp D) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (βA βA' : GL (Fin A.rank) (EAf D)), Formalism.L2.DIV.IsFrame βA ΛA → Formalism.L2.DIV.IsFrame βA' ΛA →
    ∀ (βW βW' : GL (Fin WW.rank) (EAf D)) (k : GA D WW), SuppAt e WW k →
    (∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE WW k).1 i j = toEAf D e * (βW' * βW⁻¹).1 i j) →
    ∃ x : (AE D)ˣ, Formalism.L2.Pj.FinUnit x ∧ ∀ y : WO A WW,
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA' βW' y =
        ((ν x : Circle) : ℂ) * GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt (GlobalTheory.Grid.neg A) WW 1 k y) :=
  GlobalTheory.frameChangeUnitDeterminant.stdFst_change_frames
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SndFrames

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

variable {D : D7}

local notation "OO" => Formalism.L2.Herm.intAf D.host.F D.host.E

private theorem smul_mul_eq_of {n m p : Type} [Fintype m] {R : Type} [CommRing R] (c : R) (M : Matrix n m R)
    (N N' : Matrix m p R) (hM : c • M = M) (h : ∀ i j, c * N i j = c * N' i j) : M * N = M * N' := by
  have hN : c • N = c • N' := by
    ext i j
    simpa [Matrix.smul_apply, smul_eq_mul] using h i j
  calc M * N = (c • M) * N := by rw [hM]
    _ = M * (c • N) := by rw [Matrix.smul_mul, Matrix.mul_smul]
    _ = M * (c • N') := by rw [hN]
    _ = (c • M) * N' := by rw [Matrix.smul_mul, Matrix.mul_smul]
    _ = M * N' := by rw [hM]

private theorem isHalf_mul {c : AE D} {m n : ℕ} (P : Matrix (Fin m) (Fin m) (AE D)) (u : Matrix (Fin m) (Fin n) (AE D))
    (Q : Matrix (Fin n) (Fin n) (AE D)) (h : ∀ i j, c * u i j = u i j) :
    ∀ i j, c * (HMul.hMul (HMul.hMul P u : Matrix (Fin m) (Fin n) (AE D)) Q : Matrix (Fin m) (Fin n) (AE D)) i j =
      (HMul.hMul (HMul.hMul P u : Matrix (Fin m) (Fin n) (AE D)) Q : Matrix (Fin m) (Fin n) (AE D)) i j := by
  have hu : c • u = u := by
    ext i j
    exact h i j
  have : c • (HMul.hMul (HMul.hMul P u : Matrix (Fin m) (Fin n) (AE D)) Q : Matrix (Fin m) (Fin n) (AE D)) =
      (HMul.hMul (HMul.hMul P u : Matrix (Fin m) (Fin n) (AE D)) Q : Matrix (Fin m) (Fin n) (AE D)) := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hu]
  intro i j
  exact congrFun (congrFun this i) j

private theorem mt_one (S : HSp D) : mt S 1 = 1 := by
  have := GlobalTheory.AdjAct.mt_one_inv S
  rwa [inv_one] at this

private theorem isHalf_pull (c : AE D) (S T : HSp D) (g : GA D S) (k : GA D T) (y : WO S T) (h : IsHalf c y) :
    IsHalf c (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt S T g k y) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt
  exact isHalf_mul _ _ _ h

private theorem pull_pull (S T : HSp D) (k : GA D T) (y : WO S T) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt S T 1 k⁻¹ (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt S T 1 k y) = y := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt
  rw [inv_inv, mt_one, Matrix.mul_one, Matrix.mul_one, ← Matrix.mul_assoc, GlobalTheory.AdjAct.mt_mul_mt_inv, Matrix.one_mul]

private theorem isHalf_pull_iff (c : AE D) (S T : HSp D) (k : GA D T) (y : WO S T) :
    IsHalf c (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt S T 1 k y) ↔ IsHalf c y := by
  constructor
  · intro h
    have := isHalf_pull c S T 1 k⁻¹ _ h
    rwa [pull_pull] at this
  · exact isHalf_pull c S T 1 k y

private theorem isIntM_frames {n : ℕ} {β β' : GL (Fin n) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (h : Formalism.L2.DIV.IsFrame β Λ) (h' : Formalism.L2.DIV.IsFrame β' Λ) : IsIntM ((β⁻¹ * β').1) := by
  intro i j
  have hx := (h' (β'.1.mulVec (Pi.single j 1))).2 (fun l => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _)
  have := (h _).1 hx i
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, Matrix.mulVec_single_one] at this
  exact this

private theorem isIntM_mul {m n p : ℕ} {K : Matrix (Fin m) (Fin n) (EAf D)} {Z : Matrix (Fin n) (Fin p) (EAf D)}
    (hK : IsIntM K) (hZ : IsIntM Z) : IsIntM (K * Z) := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hK i l) (hZ l j)

private theorem inId_mul {I : Ideal (𝓞 D.host.E)} {m n p : ℕ} {K : Matrix (Fin m) (Fin n) (EAf D)}
    {Z : Matrix (Fin n) (Fin p) (EAf D)} (hK : IsIntM K) {j : Fin p} (hZ : ∀ l, InId I (Z l j)) (i : Fin m) :
    InId I ((K * Z) i j) := by
  have hmem : ∀ l, Z l j ∈ OO := fun l => (hZ l).1
  have hs : (K * Z) i j ∈ OO := by
    rw [Matrix.mul_apply]
    exact sum_mem fun l _ => mul_mem (hK i l) (hmem l)
  refine ⟨hs, ?_⟩
  have e1 : (⟨(K * Z) i j, hs⟩ : OO) = ∑ l, (⟨K i l, hK i l⟩ : OO) * ⟨Z l j, hmem l⟩ :=
    Subtype.ext (by simp [Matrix.mul_apply])
  rw [e1]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hZ l).2

private theorem rightBlock_mul {m d : ℕ} (a : ℕ) (K : Matrix (Fin m) (Fin m) (EAf D)) (Z : Matrix (Fin m) (Fin d) (EAf D)) :
    rightBlock a (K * Z) = K * rightBlock a Z := by
  ext i j
  simp only [rightBlock, Matrix.mul_apply]
  split_ifs <;> simp

private theorem idem_mul {R : Type} [CommRing R] {E a b : R} (hE : E * E = E) :
    (1 - E + E * a) * (1 - E + E * b) = 1 - E + E * (a * b) := by
  linear_combination (1 - a - b + a * b) * hE

private theorem det_mem {k : ℕ} {N : Matrix (Fin k) (Fin k) (EAf D)} (h : IsIntM N) : N.det ∈ OO := by
  let A : Matrix (Fin k) (Fin k) OO := fun i j => ⟨N i j, h i j⟩
  have : N = (OO).subtype.mapMatrix A := rfl
  rw [this, ← RingHom.map_det]
  exact (A.det).2

private theorem exists_unitFactor {e : AE D} (hE : toEAf D e * toEAf D e = toEAf D e) {k : ℕ} (κ : GL (Fin k) (EAf D)) :
    ∃ x : (AE D)ˣ, infPart D (x : AE D) = 1 ∧ toEAf D (x : AE D) = 1 - toEAf D e + toEAf D e * κ.1.det ∧
      toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 - toEAf D e + toEAf D e * (κ⁻¹).1.det := by
  apply StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.exists_unit
  have hd : κ.1.det * (κ⁻¹).1.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  rw [idem_mul hE, hd, mul_one, sub_add_cancel]

set_option maxHeartbeats 1000000 in

private theorem unitChar_mul (ν : (AE D)ˣ →* Circle) {e : AE D} (hE : toEAf D e * toEAf D e = toEAf D e) {k : ℕ}
    (κ : GL (Fin k) (EAf D)) (x : (AE D)ˣ) (h1 : infPart D (x : AE D) = 1)
    (h2 : toEAf D (x : AE D) = 1 - toEAf D e + toEAf D e * κ.1.det)
    (h3 : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 - toEAf D e + toEAf D e * (κ⁻¹).1.det)
    (hxI : toEAf D (x : AE D) ∈ OO) (hxI' : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ OO)
    (R : Matrix (Fin k) (Fin k) (EAf D)) :
    unitChar ν e R = ((ν x : Circle) : ℂ) * unitChar ν e (κ.1 * R) := by
  have uniq : ∀ {N : Matrix (Fin k) (Fin k) (EAf D)} {u u' : (AE D)ˣ}, IsUnitDet e N u → IsUnitDet e N u' → u = u' :=
    fun hu hu' => Units.ext (StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.eq_of_parts (hu.1.trans hu'.1.symm) (hu.2.1.trans hu'.2.1.symm))
  have hd : κ.1.det * (κ⁻¹).1.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have fwd : ∀ u, IsUnitDet e R u → IsUnitDet e (κ.1 * R) (u * x) := by
    rintro u ⟨a1, a2, a3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [Units.val_mul, map_mul, a1, h1, one_mul]
    · rw [Units.val_mul, map_mul, a2, h2, Matrix.det_mul]
      rw [idem_mul hE, mul_comm R.det]
    · rw [mul_inv_rev, Units.val_mul, map_mul]
      exact mul_mem hxI' a3
  have hinf : infPart D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    have := congrArg (infPart D) (Units.mul_inv x)
    rw [map_mul, h1, one_mul, map_one] at this
    exact this
  have bwd : ∀ u, IsUnitDet e (κ.1 * R) u → IsUnitDet e R (u * x⁻¹) := by
    rintro u ⟨a1, a2, a3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [Units.val_mul, map_mul, a1, hinf, one_mul]
    · rw [Units.val_mul, map_mul, a2, h3, Matrix.det_mul]
      rw [idem_mul hE, mul_comm κ.1.det R.det, mul_assoc, hd, mul_one]
    · rw [mul_inv_rev, inv_inv, Units.val_mul, map_mul]
      exact mul_mem hxI a3
  unfold unitChar
  by_cases hR : ∃ u, IsUnitDet e R u
  · have hK : ∃ u, IsUnitDet e (κ.1 * R) u := ⟨_, fwd _ hR.choose_spec⟩
    rw [dif_pos hR, dif_pos hK, uniq hK.choose_spec (fwd _ hR.choose_spec), ← Circle.coe_mul]
    congr 1
    rw [map_mul, mul_inv_rev, mul_inv_cancel_left]
  · have hK : ¬ ∃ u, IsUnitDet e (κ.1 * R) u := fun ⟨u, hu⟩ => hR ⟨_, bwd u hu⟩
    rw [dif_neg hR, dif_neg hK, mul_zero]

private theorem frMapAdj_pull (A' WW : HSp D) (βA βA' : GL (Fin A'.rank) (EAf D)) (βW βW' : GL (Fin WW.rank) (EAf D))
    (k : GA D WW) {e : AE D} (he : e * e = e)
    (hk : ∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE WW k).1 i j = toEAf D e * (βW' * βW⁻¹).1 i j)
    (y : WO A' WW) (hy : IsHalf (cA D e) y) :
    frMapAdj A' WW βA βW (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt A' WW 1 k y) = HMul.hMul (βA⁻¹ * βA').1 (frMapAdj A' WW βA' βW' y) := by
  have hfr : ∀ (βS : GL (Fin A'.rank) (EAf D)) (βT : GL (Fin WW.rank) (EAf D)),
      frMapAdj A' WW βS βT y = HMul.hMul (HMul.hMul (βS⁻¹).1 (frMapAdj A' WW 1 1 y)) βT.1 := by
    intro βS βT
    simp only [frMapAdj, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  have hM : toEAf D e • frMapAdj A' WW 1 1 y = frMapAdj A' WW 1 1 y := by
    ext i j
    exact GlobalTheory.HalfSupp.frMapAdj_supp A' WW 1 1 e y he hy i j
  have hinv : (βW⁻¹ * Formalism.IndefR.Lev.finE WW k⁻¹ * βW)⁻¹ = βW⁻¹ * Formalism.IndefR.Lev.finE WW k * βW := by
    rw [map_inv]
    group
  have key := smul_mul_eq_of _ _ _ _ hM hk
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt_eq_actO, inv_one, GlobalTheory.AdjAct.frMapAdj_actO, hinv, hfr βA βW, hfr βA' βW']
  simp only [Units.val_mul] at key ⊢
  simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
  rw [← Matrix.mul_assoc (frMapAdj A' WW 1 1 y), key]
  simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  rw [← Matrix.mul_assoc βA'.val (βA'⁻¹).val, Units.mul_inv, Matrix.one_mul]

set_option maxHeartbeats 1000000 in

private theorem stdSnd_frames : ∀ {D : D7} (ν : (AE D)ˣ →* Circle) (e : AE D) (S : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e S →
    ∀ (I : Ideal (𝓞 D.host.E)) (a : ℕ) (A' WW : HSp D) (ΛA : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
    (βA βA' : GL (Fin A'.rank) (EAf D)), Formalism.L2.DIV.IsFrame βA ΛA → Formalism.L2.DIV.IsFrame βA' ΛA →
    ∀ (βW βW' : GL (Fin WW.rank) (EAf D)) (k : GA D WW), SuppAt e WW k →
    (∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE WW k).1 i j = toEAf D e * (βW' * βW⁻¹).1 i j) →
    ∃ x : (AE D)ˣ, Formalism.L2.Pj.FinUnit x ∧ ∀ y : WO A' WW,
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a A' WW βA' βW' y =
        ((ν x : Circle) : ℂ) * GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a A' WW βA βW (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt A' WW 1 k y) := by
  intro D ν e S he I a A' WW ΛA βA βA' hβA hβA' βW βW' k _ hk
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hEi := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
  have hE : toEAf D e * toEAf D e = toEAf D e := by rw [← map_mul, hee]
  have hκ : IsIntM (βA⁻¹ * βA').1 := isIntM_frames hβA hβA'
  have hκ' : IsIntM ((βA⁻¹ * βA')⁻¹).1 := by
    rw [mul_inv_rev, inv_inv]
    exact isIntM_frames hβA' hβA
  obtain ⟨x, h1, h2, h3⟩ := exists_unitFactor hE (βA⁻¹ * βA')
  have hxI : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [h2]
    exact add_mem (sub_mem (one_mem _) hEi) (mul_mem hEi (det_mem hκ))
  have hxI' : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [h3]
    exact add_mem (sub_mem (one_mem _) hEi) (mul_mem hEi (det_mem hκ'))
  refine ⟨x, ⟨h1, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hxI, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hxI'⟩, fun y => ?_⟩
  have hh := isHalf_pull_iff (cA D e) A' WW k y
  unfold stdSnd
  by_cases hy : IsHalf (cA D e) y
  · have hZ : dualCoord A' WW βA βW (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt A' WW 1 k y) =
        HMul.hMul (βA⁻¹ * βA').1 (dualCoord A' WW βA' βW' y) := by
      unfold dualCoord
      rw [frMapAdj_pull A' WW βA βA' βW βW' k hee hk y hy]
      ext i j
      simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => mul_left_comm _ _ _
    rw [hZ]
    have hZZ : ∀ Z : Matrix (Fin A'.rank) (Fin WW.rank) (EAf D),
        HMul.hMul ((βA⁻¹ * βA')⁻¹).1 (HMul.hMul (βA⁻¹ * βA').1 Z : Matrix (Fin A'.rank) (Fin WW.rank) (EAf D)) = Z := fun Z => by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    have hint : ∀ Z : Matrix (Fin A'.rank) (Fin WW.rank) (EAf D), IsIntM (HMul.hMul (βA⁻¹ * βA').1 Z : Matrix (Fin A'.rank) (Fin WW.rank) (EAf D)) ↔ IsIntM Z :=
      fun Z => ⟨fun h => hZZ Z ▸ isIntM_mul hκ' h, fun h => isIntM_mul hκ h⟩
    have hid : ∀ Z : Matrix (Fin A'.rank) (Fin WW.rank) (EAf D),
        (∀ i j, j.1 < a → InId I ((HMul.hMul (βA⁻¹ * βA').1 Z : Matrix (Fin A'.rank) (Fin WW.rank) (EAf D)) i j)) ↔ ∀ i j, j.1 < a → InId I (Z i j) :=
      fun Z => ⟨fun H i j hj => hZZ Z ▸ inId_mul hκ' (fun l => H l j hj) i,
        fun H i j hj => inId_mul hκ (fun l => H l j hj) i⟩
    by_cases hc : IsIntM (dualCoord A' WW βA' βW' y) ∧
        ∀ i j, j.1 < a → InId I (dualCoord A' WW βA' βW' y i j)
    · rw [if_pos ⟨hy, hc⟩, if_pos ⟨hh.2 hy, (hint _).2 hc.1, (hid _).2 hc.2⟩, rightBlock_mul]
      exact unitChar_mul ν hE (βA⁻¹ * βA') x h1 h2 h3 hxI hxI' _
    · rw [if_neg (fun h => hc h.2), if_neg (fun h => hc ⟨(hint _).1 h.2.1, (hid _).1 h.2.2⟩), mul_zero]
  · rw [if_neg (fun h => hy h.1), if_neg (fun h => hy (hh.1 h.1)), mul_zero]

end GlobalTheory.SndFrames

end

theorem _root_.GlobalTheory.T.standardThetaPair_second_frameChange_unitTranslate : ∀ {D : D7} (ν : (AE D)ˣ →* Circle) (e : AE D) (S : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e S →
    ∀ (I : Ideal (𝓞 D.host.E)) (a : ℕ) (A' WW : HSp D) (ΛA : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
    (βA βA' : GL (Fin A'.rank) (EAf D)), Formalism.L2.DIV.IsFrame βA ΛA → Formalism.L2.DIV.IsFrame βA' ΛA →
    ∀ (βW βW' : GL (Fin WW.rank) (EAf D)) (k : GA D WW), SuppAt e WW k →
    (∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE WW k).1 i j = toEAf D e * (βW' * βW⁻¹).1 i j) →
    ∃ x : (AE D)ˣ, Formalism.L2.Pj.FinUnit x ∧ ∀ y : WO A' WW,
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a A' WW βA' βW' y =
        ((ν x : Circle) : ℂ) * GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a A' WW βA βW (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt A' WW 1 k y) :=
  @GlobalTheory.SndFrames.stdSnd_frames
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameChange

open Formalism.L2.DIV
open scoped Matrix TensorProduct

set_option synthInstance.maxHeartbeats 160000

private theorem int_of_parts {R : Type} [CommRing R] (O : Subring R) {n : Type} [Fintype n] [DecidableEq n]
    (G Gi : Matrix n n R) (hGG : G * Gi = 1) (ε ε' : R) (hε : ε ∈ O) (hε' : ε' ∈ O)
    (hs : (ε + ε') • (G - 1) = G - 1) (h1 : ∀ i j, ε * G i j ∈ O) (h2 : ∀ i j, ε' * G i j ∈ O)
    (h3 : ∀ i j, ε * Gi i j ∈ O) (h4 : ∀ i j, ε' * Gi i j ∈ O) :
    (∀ i j, G i j ∈ O) ∧ ∀ i j, Gi i j ∈ O := by
  have hone : ∀ i j, (1 : Matrix n n R) i j ∈ O := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  have hs1 : (1 - ε - ε') ∈ O := O.sub_mem (O.sub_mem O.one_mem hε) hε'
  have hA : (1 - (ε + ε')) • G = (1 - (ε + ε')) • (1 : Matrix n n R) := by
    have : (1 - (ε + ε')) • (G - 1) = 0 := by rw [sub_smul, one_smul, hs, sub_self]
    rw [smul_sub, sub_eq_zero] at this
    exact this
  have hB : (1 - (ε + ε')) • Gi = (1 - (ε + ε')) • (1 : Matrix n n R) := by
    calc (1 - (ε + ε')) • Gi = ((1 - (ε + ε')) • (1 : Matrix n n R)) * Gi := by
          rw [Matrix.smul_mul, Matrix.one_mul]
      _ = ((1 - (ε + ε')) • G) * Gi := by rw [hA]
      _ = (1 - (ε + ε')) • (1 : Matrix n n R) := by rw [Matrix.smul_mul, hGG]
  constructor
  · intro i j
    have e1 := congrFun (congrFun hA i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at e1
    have e2 : G i j = (1 - ε - ε') * (1 : Matrix n n R) i j + ε * G i j + ε' * G i j := by
      linear_combination e1
    rw [e2]
    exact O.add_mem (O.add_mem (O.mul_mem hs1 (hone i j)) (h1 i j)) (h2 i j)
  · intro i j
    have e1 := congrFun (congrFun hB i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at e1
    have e2 : Gi i j = (1 - ε - ε') * (1 : Matrix n n R) i j + ε * Gi i j + ε' * Gi i j := by
      linear_combination e1
    rw [e2]
    exact O.add_mem (O.add_mem (O.mul_mem hs1 (hone i j)) (h3 i j)) (h4 i j)

private theorem smul_conj {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (b b' X : GL n R) (ε : R)
    (h : ε • X.1 = ε • (b' * b⁻¹ : GL n R).1) :
    ε • (b⁻¹ * X * b : GL n R).1 = ε • (b⁻¹ * b' : GL n R).1 ∧
      ε • ((b⁻¹ * X * b)⁻¹ : GL n R).1 = ε • (b'⁻¹ * b : GL n R).1 := by
  have key : ∀ u v : GL n R, ε • (u * X * v : GL n R).1 = ε • (u * (b' * b⁻¹) * v : GL n R).1 := by
    intro u v
    simp only [Units.val_mul] at h ⊢
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, h, Matrix.mul_smul, Matrix.smul_mul]
  constructor
  · rw [key, show b⁻¹ * (b' * b⁻¹) * b = b⁻¹ * b' by group]
  · have := key (b⁻¹ * X⁻¹) (b * b'⁻¹ * b)
    rw [show b⁻¹ * X⁻¹ * X * (b * b'⁻¹ * b) = b'⁻¹ * b by group,
      show b⁻¹ * X⁻¹ * (b' * b⁻¹) * (b * b'⁻¹ * b) = (b⁻¹ * X * b)⁻¹ by group] at this
    exact this.symm

private theorem smul_conj_sub_one {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (b X : GL n R) (s : R)
    (h : s • (X.1 - 1) = X.1 - 1) :
    s • ((b⁻¹ * X * b : GL n R).1 - 1) = (b⁻¹ * X * b : GL n R).1 - 1 := by
  have e : (b⁻¹ * X * b : GL n R).1 - 1 = (b⁻¹).1 * (X.1 - 1) * b.1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul, Units.val_mul, Units.val_mul]
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, h]

private theorem exists_int_GL {R : Type} [CommRing R] (O : Subring R) {n : Type} [Fintype n] [DecidableEq n] (γ : GL n R)
    (h1 : ∀ i j, γ.1 i j ∈ O) (h2 : ∀ i j, (γ⁻¹).1 i j ∈ O) : ∃ y : GL n O, y.1.map O.subtype = γ.1 := by
  let A : Matrix n n O := Matrix.of fun i j => ⟨γ.1 i j, h1 i j⟩
  let B : Matrix n n O := Matrix.of fun i j => ⟨(γ⁻¹).1 i j, h2 i j⟩
  have hA : A.map O.subtype = γ.1 := rfl
  have hB : B.map O.subtype = (γ⁻¹).1 := rfl
  have hinj : Function.Injective (fun M : Matrix n n O => M.map O.subtype) :=
    Matrix.map_injective O.subtype_injective
  refine ⟨⟨A, B, hinj ?_, hinj ?_⟩, hA⟩
  · show (A * B).map O.subtype = (1 : Matrix n n O).map O.subtype
    rw [Matrix.map_mul, hA, hB, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  · show (B * A).map O.subtype = (1 : Matrix n n O).map O.subtype
    rw [Matrix.map_mul, hA, hB, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

private theorem frame_inv_mul_int {D : D7} {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {b b' : GL (Fin n) (EAf D)} (hb : IsFrame b Λ) (hb' : IsFrame b' Λ) (i j : Fin n) :
    (b⁻¹ * b' : GL (Fin n) (EAf D)).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have h1 : b'.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    rw [hb']
    intro k
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  have h2 := (hb _).1 h1 i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h2
  exact h2

set_option maxHeartbeats 800000 in

private theorem mem_St_of_comp {D : D7} (e : AE D) (he : e * e = e) (V : HSp D)
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hΛ : IsSelfDualC V Λ)
    (b b' : GL (Fin V.rank) (EAf D)) (hb : IsFrame b Λ) (hb' : IsFrame b' Λ) (k : GA D V) (hk : SuppAt e V k)
    (hc : ∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE V k).1 i j = toEAf D e * (b' * b⁻¹).1 i j) :
    Formalism.IndefR.Lev.finE V k ∈ St b := by
  have hidem : ∀ a : AE D, a * a = a → toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun a ha =>
    Formalism.IndefR.Fin.LevelGroupLemmas.toEAf_mem_intAf (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, ha]))
  have hε := hidem e he
  have hε' := hidem (cA D e) (by rw [← map_mul, he])
  obtain ⟨X, hX⟩ : ∃ X : GL (Fin V.rank) (EAf D), X = Formalism.IndefR.Lev.finE V k := ⟨_, rfl⟩
  have hXv : X.1 = (mt V k).map (toEAf D) := by rw [hX]; rfl
  have hc' : toEAf D e • X.1 = toEAf D e • (b' * b⁻¹ : GL (Fin V.rank) (EAf D)).1 := by
    rw [hX]; exact Matrix.ext fun i j => hc i j
  obtain ⟨c1, c2⟩ := smul_conj b b' X (toEAf D e) hc'
  have hs : (toEAf D e + toEAf D (cA D e)) • (X.1 - 1) = X.1 - 1 := by
    refine Matrix.ext fun i j => ?_
    have h0 := congrArg (toEAf D) (hk i j)
    have h1 : toEAf D ((mt V k - 1) i j) = (X.1 - 1) i j := by
      rw [hXv, Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
      split_ifs
      · rw [map_one]
      · rw [map_zero]
    rw [map_mul, RingHom.map_add, h1] at h0
    exact h0
  have i1 : ∀ i j, (toEAf D e • (b⁻¹ * X * b : GL (Fin V.rank) (EAf D)).1) i j ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j; rw [c1]; exact Subring.mul_mem _ hε (frame_inv_mul_int hb hb' i j)
  have i2 : ∀ i j, (toEAf D e • ((b⁻¹ * X * b)⁻¹ : GL (Fin V.rank) (EAf D)).1) i j ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j; rw [c2]; exact Subring.mul_mem _ hε (frame_inv_mul_int hb' hb i j)
  obtain ⟨j1, j2⟩ := GlobalTheory.ConjIntegral.conj_smul_isIntM V Λ b hΛ hb X (hX ▸ GlobalTheory.LevSplit.finE_mem_UA V k)
    (b⁻¹ * X * b) rfl e i1 i2
  obtain ⟨g1, g2⟩ := int_of_parts (Formalism.L2.Herm.intAf D.host.F D.host.E) _ _ (Units.mul_inv (b⁻¹ * X * b)) _ _ hε hε'
    (smul_conj_sub_one b X _ hs) i1 j1 i2 j2
  obtain ⟨y, hy⟩ := exists_int_GL _ _ g1 g2
  refine ⟨y, ?_⟩
  have hy' : intGL D.host.F D.host.E V.rank y = b⁻¹ * X * b := Units.ext hy
  rw [← hX]
  show b * intGL D.host.F D.host.E V.rank y * b⁻¹ = X
  rw [hy']; group

set_option maxHeartbeats 800000 in

private theorem exists_unitary_frame_change : ∀ {D : D7} (e : AE D) (S : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e S →
    ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ →
    ∀ (b b' : GL (Fin V.rank) (EAf D)), Formalism.L2.DIV.IsFrame b Λ → Formalism.L2.DIV.IsFrame b' Λ →
    ∃ k : GA D V, SuppAt e V k ∧ GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.StabLat V Λ k ∧
      (∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE V k).1 i j = toEAf D e * (b' * b⁻¹).1 i j) ∧
      ∀ y : (AE D)ˣ, IsDetAt e V k y → Formalism.L2.Pj.FinUnit y := by
  intro D e S hS V Λ hΛ b b' hb hb'
  have he : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hS
  have he' : e * cA D e = 0 := hS.2
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum hS
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hφ' : ∀ z, (φ z).1 = infPart D z ∧ (φ z).2 = finPart D z := hφ
  have hJK : JR (AF D.host.F) V.gram * (V.gram⁻¹).map (incA D) = 1 := by
    show V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.UnitaryGlue.gram_det_ne_zero V).isUnit,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ : Formalism.UG.cT (cA D) (JR (AF D.host.F) V.gram) = JR (AF D.host.F) V.gram := by
    refine Matrix.ext fun i j => ?_
    show cA D (incA D (V.gram j i)) = incA D (V.gram i j)
    rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]
  let inv : EAf D →+* (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    (Algebra.TensorProduct.comm D.host.F D.host.E (Formalism.L2.Herm.Af D.host.F)).toRingEquiv.toRingHom
  have hinv : ∀ x, Lev.swapAE D (inv x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a c => rfl
    | add a c ha hc => rw [RingHom.map_add, RingHom.map_add, ha, hc]
  let P : Matrix (Fin V.rank) (Fin V.rank) (EAf D) := (b' * b⁻¹ : GL (Fin V.rank) (EAf D)).1
  let Q : Matrix (Fin V.rank) (Fin V.rank) (EAf D) := (b * b'⁻¹ : GL (Fin V.rank) (EAf D)).1
  have hPQ : P * Q = 1 := by
    show (b' * b⁻¹ * (b * b'⁻¹) : GL (Fin V.rank) (EAf D)).1 = 1
    rw [show b' * b⁻¹ * (b * b'⁻¹) = 1 by group]
    rfl
  obtain ⟨g, hg, h1, h2⟩ := GlobalTheory.SplitLift.exists_unitary_prod (infPart D) (finPart D) φ hφ' (cA D)
    GlobalTheory.DualPairCheck.cA_cA _ _ hJ hJK e he he' hinf (P.map inv) (Q.map inv)
    (by rw [← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _)])
  let k : GA D V := ⟨g, hg⟩
  have hval : ∀ i j, (Lev.finE V k).1 i j = Lev.swapAE D (finPart D (g.1 i j)) := fun i j => rfl
  have hcomp : ∀ i j, toEAf D e * (Lev.finE V k).1 i j = toEAf D e * P i j := by
    intro i j
    have h3 : finPart D e * finPart D (g.1 i j) = finPart D e * inv (P i j) := congrFun (congrFun h2 i) j
    rw [hval, show toEAf D e = Lev.swapAE D (finPart D e) from rfl, ← map_mul, h3, map_mul, hinv]
  have hk : SuppAt e V k := h1
  have hSt := mem_St_of_comp e he V Λ hΛ b b' hb hb' k hk hcomp
  refine ⟨k, hk, GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.stabLat_of_mem_St V Λ b hb k hSt, hcomp, ?_⟩
  intro y hy
  have hyv : (y : AE D) = e * (mt V k).det + (1 - e) := hy
  have hyd : y = Formalism.IndefR.Fin.LevelGroupLemmas.detAt e V k :=
    Units.ext (hyv.trans (Formalism.IndefR.Fin.LevelGroupLemmas.detAt_val he V k).symm)
  have hint : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he])
  refine ⟨?_, ?_, ?_⟩
  · rw [hyv, RingHom.map_add, map_mul, RingHom.map_sub, map_one, hinf, zero_mul, zero_add, sub_zero]
  · rw [hyd]; exact Formalism.IndefR.Fin.LevelGroupLemmas.finPart_detAt_int he hint V hSt
  · rw [hyd]; exact Formalism.IndefR.Fin.LevelGroupLemmas.finPart_detAt_inv_int he hint V hSt

end GlobalTheory.FrameChange

end

theorem _root_.GlobalTheory.T.exists_unitaryStabilizer_transition_selfDualFrames : ∀ {D : D7} (e : AE D) (S : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e S →
    ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ →
    ∀ (b b' : GL (Fin V.rank) (EAf D)), Formalism.L2.DIV.IsFrame b Λ → Formalism.L2.DIV.IsFrame b' Λ →
    ∃ k : GA D V, SuppAt e V k ∧ GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.StabLat V Λ k ∧
      (∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE V k).1 i j = toEAf D e * (b' * b⁻¹).1 i j) ∧
      ∀ y : (AE D)ˣ, IsDetAt e V k y → Formalism.L2.Pj.FinUnit y :=
  GlobalTheory.FrameChange.exists_unitary_frame_change
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BottomFrames
theorem away_of_root {K : Type} [Field K] (ζ : K) (n : ℕ) (hn : 0 < n) (hζ : ζ ^ n = 1) (m : ℕ) :
    GlobalTheory.Square.IsAwayUnit m ζ := by
  have hi : IsIntegral ℤ ζ := IsIntegral.of_pow hn (by rw [hζ]; exact isIntegral_one)
  set a : 𝓞 K := ⟨ζ, hi⟩ with ha
  have h1 : (a : K) = ζ := rfl
  refine ⟨a, 0, 0, ?_, by rw [pow_zero, mul_one, h1]⟩
  rw [pow_zero]
  refine ⟨a ^ (n - 1), ?_⟩
  apply RingOfIntegers.ext
  push_cast [h1]
  rw [← pow_succ', Nat.sub_add_cancel hn, hζ]

theorem ratio_alg {u1 u2 a b : ℂ} (h2 : u2 ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    u1 * (a / b) / u2 = (u1 * b⁻¹) / (u2 * a⁻¹) := by
  field_simp

theorem const_alg {c1 c2 c x : ℂ} (h2 : c2 ≠ 0) : c1 * (c * x) = c1 / c2 * c * (c2 * x) := by
  field_simp
end GlobalTheory.BottomFrames

namespace GlobalTheory.BottomFrames

theorem compAt_supp {D : D7} (θ : InfFam D) {e : AE D} (he : infPart D e = 0) {V : HSp D} {k : GA D V}
    (hk : SuppAt e V k) (τ : D.what₂.Tau) : compAt θ τ (Formalism.L2.Theta.mt V k) = 1 := by
  have h1 := GlobalTheory.StdUnn.CartanMove.compAt_mt_one θ τ V
  rw [GlobalTheory.AdelicLatMove.mt_one] at h1
  ext a b
  have e1 : Formalism.L2.Theta.mt V k a b = (e + cA D e) * (Formalism.L2.Theta.mt V k - 1) a b + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) a b := by
    rw [hk a b, Matrix.sub_apply, sub_add_cancel]
  have h2 := congrFun (congrFun h1 a) b
  simp only [compAt, Matrix.map_apply] at h2 ⊢
  have h0 : infPart D (e + cA D e) = 0 := by rw [RingHom.map_add, he, GlobalTheory.PlaceDatum.infPart_cA he, add_zero]
  rw [e1, RingHom.map_add (infPart D), RingHom.map_mul (infPart D), h0, zero_mul, zero_add, h2]

theorem suppAt_one' {D : D7} (e : AE D) (V : HSp D) : SuppAt e V 1 := fun i j => by
  rw [GlobalTheory.AdelicLatMove.mt_one, sub_self]; simp

theorem stabLat_one' {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.StabLat V Λ 1 := fun y => by simp

theorem isDetAt_one' {D : D7} (e : AE D) (V : HSp D) : IsDetAt e V 1 1 := by
  show ((1 : (AE D)ˣ) : AE D) = e * (Formalism.L2.Theta.mt V 1).det + (1 - e)
  rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.det_one]; simp

theorem selfDual_neg {D : D7} {A : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} (hA : IsSelfDualC A Λ) :
    IsSelfDualC (GlobalTheory.Grid.neg A) Λ := by
  refine ⟨hA.1, fun y => (hA.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
  · simp [GlobalTheory.Grid.neg_gram, hc]
  · simp [GlobalTheory.Grid.neg_gram] at hc ⊢
    exact neg_eq_iff_eq_neg.2 hc

set_option maxHeartbeats 4000000 in
theorem frames_change : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (μ₀ : T), Lc.Is μ₀ → ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ →
  ∀ (i j : Fin D.R.m) {A A' WW : HSp D} (X Y : Tri T A A' WW), IsBottomTri W i j X → GlobalTheory.SqTower.IsStageC W i j 0 0 Y →
  Y.rA.Λ = X.rA.Λ → Y.rA'.Λ = X.rA'.Λ → Y.rW.Λ = X.rW.Λ →
  ∃ (Z : Tri T A A' WW) (v : T → ℂ), GlobalTheory.SqTower.IsStageC W i j 0 0 Z ∧
    Z.rA.Λ = X.rA.Λ ∧ Z.rA'.Λ = X.rA'.Λ ∧ Z.rW.Λ = X.rW.Λ ∧ Z.rA.β = X.rA.β ∧ Z.rA'.β = X.rA'.β ∧ Z.rW.β = X.rW.β ∧
    (∀ t, v t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ v t = D.what₂.embLL ζ * v μ₀) ∧ ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → Z.IsConst W.ψ W.θ (fun t => v t * c t) := by
  intro D T Lc sc G μ₀ hL W S hN i j A A' WW X Y hX hY eA eA' eW
  classical
  obtain ⟨p1, p2, p3, p4, n1, n2, n3, hI⟩ := hY
  have hXI := hX.is
  have fA : Formalism.L2.DIV.IsFrame X.rA.β Y.rA.Λ := eA ▸ hXI.rigA.2.1
  have fA' : Formalism.L2.DIV.IsFrame X.rA'.β Y.rA'.Λ := eA' ▸ hXI.rigA'.2.1
  have fW : Formalism.L2.DIV.IsFrame X.rW.β Y.rW.Λ := eW ▸ hXI.rigW.2.1
  set α : T → ((AE D)ˣ →* Circle) := fun t => Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) with hα
  set β : T → ((AE D)ˣ →* Circle) := fun _ => G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2) with hβ
  have hee : ∀ t, Y.e t * Y.e t = Y.e t := fun t => GlobalTheory.PlaceDatum.idemSum_mul_self (hI.idem t)
  choose k hk1 hk2 hk3 hk4 using fun t =>
    GlobalTheory.T.exists_unitaryStabilizer_transition_selfDualFrames (Y.e t) (locPl G t) (hI.idem t) WW Y.rW.Λ hI.rigW.1 Y.rW.β X.rW.β hI.rigW.2.1 fW
  choose x1 hx1 hx1' using fun t => GlobalTheory.T.standardThetaPair_first_frameChange_unitTranslate (α t / β t) (Y.e t) (locPl G t) (hI.idem t) (Y.ideal (locPl G) t) A WW
    Y.rA.Λ Y.rA.β X.rA.β hI.rigA.2.1 fA Y.rW.β X.rW.β (k t) (hk1 t) (hk3 t)
  choose x2 hx2 hx2' using fun t => GlobalTheory.T.standardThetaPair_second_frameChange_unitTranslate (α t / β t) (Y.e t) (locPl G t) (hI.idem t) (Y.ideal (locPl G) t) A.rank
    A' WW Y.rA'.Λ Y.rA'.β X.rA'.β hI.rigA'.2.1 fA' Y.rW.β X.rW.β (k t) (hk1 t) (hk3 t)
  set y : T → (AE D)ˣ := fun t => GlobalTheory.VecInv.detAt (Y.e t) (hee t) WW (k t) with hy
  have hy1 : ∀ t, IsDetAt (Y.e t) WW (k t) (y t) := fun t => GlobalTheory.VecInv.isDetAt_detAt _ _ _ _
  set c1 : T → ℂ := fun t => (((α t / β t) (x1 t) : Circle) : ℂ) * (((β t (y t) : Circle) : ℂ))⁻¹ with hc1
  set c2 : T → ℂ := fun t => (((α t / β t) (x2 t) : Circle) : ℂ) * (((α t (y t) : Circle) : ℂ))⁻¹ with hc2

  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  have hSdA := selfDual_neg hI.rigA.1
  have hinf : ∀ t, infPart D (Y.e t) = 0 := fun t => GlobalTheory.PlaceDatum.infPart_idemSum (hI.idem t)
  have hinf' : ∀ t, infPart D (cA D (Y.e t)) = 0 := fun t => GlobalTheory.PlaceDatum.infPart_cA (hinf t)
  have hee' : ∀ t, cA D (Y.e t) * cA D (Y.e t) = cA D (Y.e t) := fun t => by rw [← RingHom.map_mul, hee t]
  have hSB : ∀ t, IsSBHalf (Y.e t) (latO (GlobalTheory.Grid.neg A) WW (Y.rA.Λ : Set (Fin A.rank → D.host.E)) (Y.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (α t / β t) (Y.e t) (Y.ideal (locPl G) t) A WW Y.rA.β Y.rW.β) := fun t => by
    obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO (S := GlobalTheory.Grid.neg A) hSdA.1 hI.rigW.1.1 Y.rA.β Y.rW.β
    exact StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.stdFst_isSB (hI.weil' t).hecT.1 (hI.idem t) (GlobalTheory.ConstRatio.ideal_ne_bot Y (locPl G) t)
      A WW Y.rA.β Y.rW.β _ (GlobalTheory.PlaceDatum.exists_den_frMapO (S := GlobalTheory.Grid.neg A) hSdA.1.fg hI.rigW.1.1.fg Y.rA.β Y.rW.β)
      ⟨K, hK, fun t' ht => hC t' (GlobalTheory.PlaceDatum.infPart_of_half (hinf t) ht)⟩
  have hSB' : ∀ t, IsSBHalf (cA D (Y.e t)) (latO A' WW (Y.rA'.Λ : Set (Fin A'.rank → D.host.E)) (Y.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (α t / β t) (Y.e t) (Y.ideal (locPl G) t) A.rank A' WW Y.rA'.β Y.rW.β) := fun t =>
    GlobalTheory.T.standardThetaPair_second_isSchwartzBruhat_conjHalf _ (hI.weil' t).hecT.1 (Y.e t) (locPl G t) (hI.idem t) _ (GlobalTheory.ConstRatio.ideal_ne_bot Y (locPl G) t) A.rank A' WW
      Y.rA'.Λ Y.rW.Λ hI.rigA'.1 hI.rigW.1 Y.rA'.β Y.rW.β
  have thY : ∀ t, IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (Y.f t) := fun t => by
    obtain ⟨Tm, hTm⟩ := (hI.fst t).1
    rw [(hI.fst t).2 Tm hTm]
    exact GlobalTheory.SchrTheta.isTheta_placeModel D W.ψ hψ (GlobalTheory.Grid.neg A) WW Y.rA.Λ Y.rW.Λ hSdA hI.rigW.1 (Y.e t) (hee t) (hinf t)
      Y.vac hI.isVac.2.theta Tm hTm _ (hSB t)
  have thY' : ∀ t, IsThetaFunO W.ψ A' WW (Y.f' t) := fun t => by
    obtain ⟨Tm, hTm⟩ := (hI.snd t).1
    rw [(hI.snd t).2 Tm hTm]
    exact GlobalTheory.SchrTheta.isTheta_placeModel D W.ψ hψ A' WW Y.rA'.Λ Y.rW.Λ hI.rigA'.1 hI.rigW.1 (cA D (Y.e t)) (hee' t) (hinf' t)
      Y.vac' hI.isVac'.2.theta Tm hTm _ (hSB' t)
  let Z : Tri T A A' WW :=
    ⟨⟨Y.rA.Λ, X.rA.β, Y.rA.s, Y.rA.B⟩, ⟨Y.rA'.Λ, X.rA'.β, Y.rA'.s, Y.rA'.B⟩, ⟨Y.rW.Λ, X.rW.β, Y.rW.s, Y.rW.B⟩, Y.ω, Y.ω',
      Y.vac, Y.vac', Y.e, Y.c, fun t => c1 t • (Y.ω t).toSgn true (1, k t) (Y.f t), fun t => c2 t • Y.ω' t (1, k t) (Y.f' t),
      Y.m, Y.fd, Y.m', Y.fd'⟩
  have hZI : Z.Is W.ψ W.θ α β (fun t => nuH G t i j) (locPl G) := by
    refine ⟨hI.rank, ⟨hI.rigA.1, fA, hI.rigA.2.2⟩, ⟨hI.rigA'.1, fA', hI.rigA'.2.2⟩, ⟨hI.rigW.1, fW, hI.rigW.2.2⟩, hI.weil,
      hI.weil', hI.isVac, hI.isVac', hI.idem, hI.expo, fun t => ?_, fun t => ?_, hI.meas, hI.meas'⟩
    · refine ⟨(hI.fst t).1, fun Tm hTm => ?_⟩
      have hY := (hI.fst t).2 Tm hTm
      have hLaw := ((GlobalTheory.WeilSplit.weilSplitFormula D W.ψ W.θ (GlobalTheory.Grid.neg A) WW (β t) (β t / α t) ((Y.ω t).toSgn true)
        (hI.weil t) (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.Λ Y.rW.Λ hSdA hI.rigW.1 Y.vac hI.isVac (Y.e t)
        (Or.inr ⟨_, hI.idem t⟩)).1 Tm hTm) 1 (k t) (suppAt_one' _ _) (hk1 t) (stabLat_one' _ _) (hk2 t) 1 (y t)
        (isDetAt_one' _ _) (hy1 t) _ (hSB t)
      have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (α t / β t) (Y.e t) (Y.ideal (locPl G) t) A WW X.rA.β X.rW.β =
          (((α t / β t) (x1 t) : Circle) : ℂ) • fun s => GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (α t / β t) (Y.e t) (Y.ideal (locPl G) t) A WW
            Y.rA.β Y.rW.β (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt (GlobalTheory.Grid.neg A) WW 1 (k t) s) := funext fun s => hx1' t s
      show c1 t • (Y.ω t).toSgn true (1, k t) (Y.f t) = Tm (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (α t / β t) (Y.e t) (Y.ideal (locPl G) t) A WW X.rA.β X.rW.β)
      rw [hY, hLaw, e1, map_smul, smul_smul]
      congr 1
      rw [hc1, map_one, Circle.coe_one, inv_one, one_mul, mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero _), mul_one]
    · refine ⟨(hI.snd t).1, fun Tm hTm => ?_⟩
      have hY := (hI.snd t).2 Tm hTm
      have hLaw := ((GlobalTheory.WeilSplit.weilSplitFormula D W.ψ W.θ A' WW (α t) (α t / β t) (Y.ω' t)
        (hI.weil' t) Y.rA'.s Y.rW.s Y.rA'.Λ Y.rW.Λ hI.rigA'.1 hI.rigW.1 Y.vac' hI.isVac' (Y.e t)
        (Or.inr ⟨_, hI.idem t⟩)).2 Tm hTm) 1 (k t) (suppAt_one' _ _) (hk1 t) (stabLat_one' _ _) (hk2 t) 1 (y t)
        (isDetAt_one' _ _) (hy1 t) _ (hSB' t)
      have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (α t / β t) (Y.e t) (Y.ideal (locPl G) t) A.rank A' WW X.rA'.β X.rW.β =
          (((α t / β t) (x2 t) : Circle) : ℂ) • fun s => GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (α t / β t) (Y.e t) (Y.ideal (locPl G) t) A.rank A' WW
            Y.rA'.β Y.rW.β (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt A' WW 1 (k t) s) := funext fun s => hx2' t s
      show c2 t • Y.ω' t (1, k t) (Y.f' t) = Tm (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (α t / β t) (Y.e t) (Y.ideal (locPl G) t) A.rank A' WW X.rA'.β X.rW.β)
      rw [hY, hLaw, e1, map_smul, smul_smul]
      congr 1
      rw [hc2, map_one, Circle.coe_one, inv_one, one_mul, mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero _), mul_one]

  have tsg : ∀ t (h' : GA D WW), (Y.ω t).toSgn true (1, h') = Y.ω t (1, h') := fun t h' => by
    show Y.ω t ((GlobalTheory.Grid.ofSgn true A) 1, h') = _
    rw [map_one]
  have kerZ : ∀ t P h' g, Z.ker W.ψ W.θ t P h' g = c1 t * Y.ker W.ψ W.θ t P (h' * k t) g := by
    intro t P h' g
    have hop := (GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ (GlobalTheory.Grid.neg A) WW _ _ ((Y.ω t).toSgn true) (hI.weil t) W.θ_is
      (fun τ => -Y.rA.s τ) (fun τ => -Y.rA.s τ) Y.rA.B Y.rA.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B 1 (k t)
      (fun τ => by rw [GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [compAt_supp W.θ (hinf t) (hk1 t), Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.one_mul])
      (fun τ => by rw [compAt_supp W.θ (hinf t) (hk1 t), Matrix.one_mul]) (Y.f t) (thY t) P).2
    have hm : ∀ F, Y.ω t (g, h') (Y.ω t (1, k t) F) = Y.ω t (g, h' * k t) F := fun F => by
      have e := (Y.ω t).map_mul (g, h') (1, k t)
      rw [Prod.mk_mul_mk, mul_one] at e
      rw [e]; rfl
    have e1 : pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B
        (c1 t • (Y.ω t).toSgn true (1, k t) (Y.f t)) P = c1 t • (Y.ω t) (1, k t)
        (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P) := by
      rw [GlobalTheory.SeeSaw.Resc.pureTensorO_smul, LinearMap.smul_apply, ← tsg, hop]
    calc Z.ker W.ψ W.θ t P h' g = (Y.ω t (g, h') (c1 t • Y.ω t (1, k t)
          (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P))) 0 := by
          rw [← e1]; rfl
      _ = c1 t * (Y.ω t (g, h') (Y.ω t (1, k t)
          (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P))) 0 := by
          rw [LinearMap.map_smul]; rfl
      _ = c1 t * Y.ker W.ψ W.θ t P (h' * k t) g :=
          congrArg (c1 t * ·) (congrFun (hm (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P)) 0)
  have kerZ' : ∀ t P h' g, Z.ker' W.ψ W.θ t P h' g = c2 t * Y.ker' W.ψ W.θ t P (h' * k t) g := by
    intro t P h' g
    have hw' : IsWeilDatumO W.ψ A' WW (α t) (α t / β t) (Y.ω' t) := hI.weil' t
    have hop := (GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ A' WW (α t) (α t / β t) (Y.ω' t) hw' W.θ_is
      Y.rA'.s Y.rA'.s Y.rA'.B Y.rA'.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B 1 (k t)
      (fun τ => by rw [GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [compAt_supp W.θ (hinf t) (hk1 t), Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.one_mul])
      (fun τ => by rw [compAt_supp W.θ (hinf t) (hk1 t), Matrix.one_mul]) (Y.f' t) (thY' t) P).2
    have hm : ∀ F, Y.ω' t (g, h') (Y.ω' t (1, k t) F) = Y.ω' t (g, h' * k t) F := fun F => by
      have e : Y.ω' t ((g, h') * (1, k t)) = Y.ω' t (g, h') * Y.ω' t (1, k t) := map_mul _ _ _
      rw [Prod.mk_mul_mk, mul_one] at e
      rw [e]; rfl
    have e1 : pureTensorO W.ψ W.θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B
        (c2 t • Y.ω' t (1, k t) (Y.f' t)) P = c2 t • (Y.ω' t) (1, k t)
        (pureTensorO W.ψ W.θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) P) := by
      rw [GlobalTheory.SeeSaw.Resc.pureTensorO_smul, LinearMap.smul_apply, hop]
    calc Z.ker' W.ψ W.θ t P h' g = (Y.ω' t (g, h') (c2 t • Y.ω' t (1, k t)
          (pureTensorO W.ψ W.θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) P))) 0 := by
          rw [← e1]; rfl
      _ = c2 t * (Y.ω' t (g, h') (Y.ω' t (1, k t)
          (pureTensorO W.ψ W.θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) P))) 0 := by
          rw [LinearMap.map_smul]; rfl
      _ = c2 t * Y.ker' W.ψ W.θ t P (h' * k t) g :=
          congrArg (c2 t * ·) (congrFun (hm (pureTensorO W.ψ W.θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) P)) 0)
  have IZ : ∀ t P h', Z.I W.ψ W.θ t P h' = c1 t * Y.I W.ψ W.θ t P (h' * k t) := fun t P h' => by
    show ∫ g in Y.fd, Z.ker W.ψ W.θ t P h' g ∂Y.m = _
    simp only [kerZ]
    exact MeasureTheory.integral_const_mul _ _
  have IZ' : ∀ t P h', Z.I' W.ψ W.θ t P h' = c2 t * Y.I' W.ψ W.θ t P (h' * k t) := fun t P h' => by
    show ∫ g in Y.fd', Z.ker' W.ψ W.θ t P h' g ∂Y.m' = _
    simp only [kerZ']
    exact MeasureTheory.integral_const_mul _ _
  have c1ne : ∀ t, c1 t ≠ 0 := fun t => mul_ne_zero (Circle.coe_ne_zero _) (inv_ne_zero (Circle.coe_ne_zero _))
  have c2ne : ∀ t, c2 t ≠ 0 := fun t => mul_ne_zero (Circle.coe_ne_zero _) (inv_ne_zero (Circle.coe_ne_zero _))

  have hv : ∀ t, ∃ ζ : D.what₂.LL, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧ D.what₂.embLL ζ = c1 t / c2 t := by
    intro t
    obtain ⟨z1, ⟨n1, hn1, hz1⟩, e1⟩ := GlobalTheory.T.gridSquareCharQuotient_finiteUnitIdele_rootOfUnity μ₀ hL hN.chars i j t (x1 t) (hx1 t)
    obtain ⟨z2, ⟨n2, hn2, hz2⟩, e2⟩ := GlobalTheory.T.gridSquareCharQuotient_finiteUnitIdele_rootOfUnity μ₀ hL hN.chars i j t (x2 t) (hx2 t)
    obtain ⟨z3, ⟨n3, hn3, hz3⟩, e3⟩ := GlobalTheory.T.gridSquareCharQuotient_finiteUnitIdele_rootOfUnity μ₀ hL hN.chars i j t (y t) (hk4 t _ (hy1 t))
    refine ⟨z1 * z3 / z2, ⟨n1 * n2 * n3, by positivity, ?_⟩, ?_⟩
    · have r1 : z1 ^ (n1 * n2 * n3) = 1 := by rw [mul_assoc, pow_mul, hz1, one_pow]
      have r2 : z2 ^ (n1 * n2 * n3) = 1 := by rw [mul_comm n1 n2, mul_assoc, pow_mul, hz2, one_pow]
      have r3 : z3 ^ (n1 * n2 * n3) = 1 := by rw [mul_comm, pow_mul, hz3, one_pow]
      rw [div_pow, mul_pow, r1, r2, r3]; simp
    · rw [map_div₀, map_mul, e1, e2, e3, MonoidHom.div_apply, Circle.coe_div]
      exact ratio_alg (Circle.coe_ne_zero _) (Circle.coe_ne_zero _) (Circle.coe_ne_zero _)
  refine ⟨Z, fun t => c1 t / c2 t, ⟨p1, p2, p3, p4, n1, n2, n3, hZI⟩, eA, eA', eW, rfl, rfl, rfl, fun t => ?_, fun c hc => ?_⟩
  · obtain ⟨z, ⟨n, hn, hz⟩, ez⟩ := hv t
    obtain ⟨z0, ⟨n0, hn0, hz0⟩, ez0⟩ := hv μ₀
    have hz0' : z0 ≠ 0 := fun h => by rw [h, zero_pow hn0.ne'] at hz0; exact zero_ne_one hz0
    refine ⟨div_ne_zero (c1ne t) (c2ne t), z / z0, away_of_root (z / z0) (n * n0) (by positivity) ?_ _, ?_⟩
    · have r1 : z ^ (n * n0) = 1 := by rw [pow_mul, hz, one_pow]
      have r2 : z0 ^ (n * n0) = 1 := by rw [mul_comm, pow_mul, hz0, one_pow]
      rw [div_pow, r1, r2, div_one]
    · rw [map_div₀, ez, ez0, div_mul_cancel₀ _ (div_ne_zero (c1ne μ₀) (c2ne μ₀))]
  · obtain ⟨⟨t0, ht0⟩, P, P', H⟩ := hc
    refine ⟨⟨t0, mul_ne_zero (div_ne_zero (c1ne t0) (c2ne t0)) ht0⟩, P, P', fun t => ⟨fun h' => ⟨?_, ?_⟩, ?_, fun h' => ?_⟩⟩
    · have e : Z.ker W.ψ W.θ t P h' = fun g => c1 t * Y.ker W.ψ W.θ t P (h' * k t) g := funext (kerZ t P h')
      rw [e]
      exact ((H t).1 (h' * k t)).1.const_mul _
    · have e : Z.ker' W.ψ W.θ t P' h' = fun g => c2 t * Y.ker' W.ψ W.θ t P' (h' * k t) g := funext (kerZ' t P' h')
      rw [e]
      exact ((H t).1 (h' * k t)).2.const_mul _
    · obtain ⟨h0, hh0⟩ := (H t).2.1
      refine ⟨h0 * (k t)⁻¹, ?_⟩
      rw [IZ', inv_mul_cancel_right]
      exact mul_ne_zero (c2ne t) hh0
    · show Z.I W.ψ W.θ t P h' = c1 t / c2 t * c t * Z.I' W.ψ W.θ t P' h'
      rw [IZ, IZ', (H t).2.2]
      exact const_alg (c2ne t)

end GlobalTheory.BottomFrames
end
end
