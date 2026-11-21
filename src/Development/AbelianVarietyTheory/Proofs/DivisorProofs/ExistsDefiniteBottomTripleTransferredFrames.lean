import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdLatEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentPlaceChartFiniteAdeles
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaLiftIdempotentForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdeleCMMemIntegralOfIdempotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHomLatticeIffFrameStabilizerActMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharInvCentralFlipIdeleEqProdLocalComponents
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardLiftLevelActsByInverseCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTowerConstantsDifferByFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.KerDiag
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_lift_idempotent_form : ∀ {D : D7} (V : HSp D), V.gram = 1 → ∀ (e : AE D), e * e = e → e * cA D e = 0 →
    ∀ (P Q : Matrix (Fin V.rank) (Fin V.rank) (AE D)), e • (P * Q) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) →
      e • (Q * P) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) →
    ∃ g : GA D V,
      Formalism.L2.Theta.mt V g = (1 - e - cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) + e • P + cA D e • (Q.map (cA D)).transpose ∧
      Formalism.L2.Theta.mt V g⁻¹ = (1 - e - cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) + e • Q + cA D e • (P.map (cA D)).transpose := by
  first | exact @GlobalTheory.UnitaryMove.exists_blockUnit | exact GlobalTheory.UnitaryMove.exists_blockUnit | (intros; apply GlobalTheory.UnitaryMove.exists_blockUnit <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.StabMove

theorem mul_entries_mem {A : Type} [CommRing A] (R : Subring A) {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) A) (hM : ∀ i j, M i j ∈ R) (hN : ∀ i j, N i j ∈ R) :
    ∀ i j, (M * N) i j ∈ R := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem R fun k _ => R.mul_mem (hM i k) (hN k j)

def lift {A : Type} [CommRing A] (R : Subring A) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (hM : ∀ i j, M i j ∈ R) : Matrix (Fin n) (Fin n) R :=
  fun i j => ⟨M i j, hM i j⟩

theorem lift_map {A : Type} [CommRing A] (R : Subring A) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (hM : ∀ i j, M i j ∈ R) :
    (lift R M hM).map R.subtype = M := by
  ext i j; rfl

def liftGL {A : Type} [CommRing A] (R : Subring A) {n : ℕ} (u : GL (Fin n) A)
    (hu : ∀ i j, u.val i j ∈ R) (hu' : ∀ i j, (u⁻¹).val i j ∈ R) : GL (Fin n) R where
  val := lift R u.val hu
  inv := lift R (u⁻¹).val hu'
  val_inv := by
    apply Matrix.map_injective (f := R.subtype) Subtype.val_injective
    dsimp only
    rw [Matrix.map_mul (f := R.subtype), lift_map, lift_map, Matrix.map_one _ (map_zero _) (map_one _)]
    exact u.mul_inv
  inv_val := by
    apply Matrix.map_injective (f := R.subtype) Subtype.val_injective
    dsimp only
    rw [Matrix.map_mul (f := R.subtype), lift_map, lift_map, Matrix.map_one _ (map_zero _) (map_one _)]
    exact u.inv_mul

theorem liftGL_map {A : Type} [CommRing A] (R : Subring A) {n : ℕ} (u : GL (Fin n) A)
    (hu : ∀ i j, u.val i j ∈ R) (hu' : ∀ i j, (u⁻¹).val i j ∈ R) :
    Formalism.UG.bc R.subtype (liftGL R u hu hu') = u := by
  ext i j; rfl

end GlobalTheory.StabMove

open GlobalTheory.StabMove in
theorem GlobalTheory.StabMove.finE_mem_St : ∀ {D : D7} (V : HSp D) (g : GA D V) (β₀ β₁ : GL (Fin V.rank) (Lev.EAf D)),
    (∀ i j, β₀.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₀⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    (∀ i j, β₁.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₁⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    ∀ ε φ : Lev.EAf D, ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → φ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
    (Formalism.L2.Theta.mt V g).map (toEAf D) = (1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
      ε • (β₁ * β₀⁻¹).val + φ • ((β₀ * β₁⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose →
    (Formalism.L2.Theta.mt V g⁻¹).map (toEAf D) = (1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
      ε • (β₀ * β₁⁻¹).val + φ • ((β₁ * β₀⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose →
    Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β₁ := by
  intro D V g β₀ β₁ h₀ h₁ ε φ hε hφ hg hg'
  set R := Formalism.L2.Herm.intAf D.host.F D.host.E with hR
  have hcF : ∀ M : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D), (∀ i j, M i j ∈ R) →
      ∀ i j, ((M.map (GlobalTheory.AdelicLatMove.cF D)).transpose) i j ∈ R := by
    intro M hM i j
    exact GlobalTheory.LevSplit.sigR_int (hM j i)
  have hshape : ∀ (a b : GL (Fin V.rank) (Lev.EAf D)), (∀ i j, a.val i j ∈ R ∧ (a⁻¹).val i j ∈ R) →
      (∀ i j, b.val i j ∈ R ∧ (b⁻¹).val i j ∈ R) →
      ∀ i j, ((1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
        ε • (a * b⁻¹).val + φ • ((b * a⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose) i j ∈ R := by
    intro a b ha hb i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine R.add_mem (R.add_mem (R.mul_mem ?_ ?_) (R.mul_mem hε ?_)) (R.mul_mem hφ ?_)
    · exact R.sub_mem (R.sub_mem R.one_mem hε) hφ
    · rw [Matrix.one_apply]; split_ifs
      · exact R.one_mem
      · exact R.zero_mem
    · rw [Units.val_mul]
      exact mul_entries_mem R _ _ (fun i j => (ha i j).1) (fun i j => (hb i j).2) i j
    · apply hcF
      rw [Units.val_mul]
      exact mul_entries_mem R _ _ (fun i j => (hb i j).1) (fun i j => (ha i j).2)
  have hE : ∀ i j, (Formalism.IndefR.Lev.finE V g).val i j ∈ R := by
    have : (Formalism.IndefR.Lev.finE V g).val = (Formalism.L2.Theta.mt V g).map (toEAf D) := rfl
    rw [this, hg]; exact hshape β₁ β₀ h₁ h₀
  have hE' : ∀ i j, ((Formalism.IndefR.Lev.finE V g)⁻¹).val i j ∈ R := by
    have : ((Formalism.IndefR.Lev.finE V g)⁻¹).val = (Formalism.L2.Theta.mt V g⁻¹).map (toEAf D) := by
      rw [← map_inv]; rfl
    rw [this, hg']; exact hshape β₀ β₁ h₀ h₁
  set u := β₁⁻¹ * Formalism.IndefR.Lev.finE V g * β₁ with hu
  have hu1 : ∀ i j, u.val i j ∈ R := by
    intro i j
    simp only [hu, Units.val_mul]
    exact mul_entries_mem R _ _ (mul_entries_mem R _ _ (fun i j => (h₁ i j).2) hE) (fun i j => (h₁ i j).1) i j
  have hu2 : ∀ i j, (u⁻¹).val i j ∈ R := by
    intro i j
    have : u⁻¹ = β₁⁻¹ * (Formalism.IndefR.Lev.finE V g)⁻¹ * β₁ := by
      simp only [hu, mul_inv_rev, inv_inv, mul_assoc]
    rw [this]
    simp only [Units.val_mul]
    exact mul_entries_mem R _ _ (mul_entries_mem R _ _ (fun i j => (h₁ i j).2) hE') (fun i j => (h₁ i j).1) i j
  refine ⟨liftGL R u hu1 hu2, ?_⟩
  show MulAut.conj β₁ (Formalism.UG.bc R.subtype (liftGL R u hu1 hu2)) = _
  rw [liftGL_map, MulAut.conj_apply, hu]
  group
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryFinitePart_idempotentBlend_mem_latticeStabilizer : ∀ {D : D7} (V : HSp D) (g : GA D V) (β₀ β₁ : GL (Fin V.rank) (Lev.EAf D)),
    (∀ i j, β₀.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₀⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    (∀ i j, β₁.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₁⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    ∀ ε φ : Lev.EAf D, ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → φ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
    (Formalism.L2.Theta.mt V g).map (toEAf D) = (1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
      ε • (β₁ * β₀⁻¹).val + φ • ((β₀ * β₁⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose →
    (Formalism.L2.Theta.mt V g⁻¹).map (toEAf D) = (1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
      ε • (β₀ * β₁⁻¹).val + φ • ((β₁ * β₀⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose →
    Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β₁ := by
  atlas_forward_decl GlobalTheory.StabMove.finE_mem_St
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotUnitMove

variable {D : D7}

theorem mul_eq_of_toEAf_eq {e : AE D} (he : GlobalTheory.PlaceModelSum.IsOrthSum e) {a b : AE D}
    (h : toEAf D a = toEAf D b) : e * a = e * b := by
  obtain ⟨ι, P, es, h1, -, rfl⟩ := he
  rw [← sub_eq_zero, ← mul_sub, Finset.sum_mul]
  refine Finset.sum_eq_zero fun i hi => ?_
  refine (GlobalTheory.DownLift.SplitCoef.toEAf_idem_mul_eq_zero (h1 i hi) _).1 ?_
  rw [map_mul, map_sub, h, sub_self, mul_zero]

theorem frame_int {V : HSp D} {r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V} (hs : r.IsStd) (hr : r.Is) (i j : Fin V.rank) :
    r.β.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (r.β⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have hΛ : r.Λ = Formalism.L2.Col.stdLat D.host.E V.rank := by
    ext y
    rw [hs.2.1]
    simp [Formalism.L2.Col.stdLat, Submodule.mem_pi, Submodule.mem_one]
  have hf := hr.2.1
  rw [hΛ] at hf
  constructor
  · have h := (hf (fun k => r.β.val k j)).2 fun k => by
      have e : (r.β⁻¹).val.mulVec
          (fun k => r.β.val k j) k = ((r.β⁻¹).val * r.β.val) k j := by
        simp [Matrix.mulVec, Matrix.mul_apply, dotProduct]
      rw [e, Units.inv_mul, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    exact (GlobalTheory.CongStdLoc.mem_hatL_std_iff _).1 h i
  · have h := (hf (Pi.single j 1)).1 ((GlobalTheory.CongStdLoc.mem_hatL_std_iff _).2 fun k => by
      by_cases hk : k = j
      · subst hk; simp only [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne hk]; exact zero_mem _)
    have e : (r.β⁻¹).val.mulVec
        (Pi.single j 1) i = (r.β⁻¹).val i j := by
      simp [Matrix.mulVec_single]
    rw [← e]
    exact h i

theorem exists_unitary : ∀ {D : D7} (V : HSp D), V.gram = 1 → ∀ (e : AE D), e * e = e → e * cA D e = 0 →
    ∀ (P Q : Matrix (Fin V.rank) (Fin V.rank) (AE D)), e • (P * Q) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) →
      e • (Q * P) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) →
    ∃ g : GA D V,
      Formalism.L2.Theta.mt V g = (1 - e - cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) + e • P + cA D e • (Q.map (cA D)).transpose ∧
      Formalism.L2.Theta.mt V g⁻¹ = (1 - e - cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) + e • Q + cA D e • (P.map (cA D)).transpose := GlobalTheory.T.exists_theta_lift_idempotent_form

theorem mem_St : ∀ {D : D7} (V : HSp D) (g : GA D V) (β₀ β₁ : GL (Fin V.rank) (Lev.EAf D)),
    (∀ i j, β₀.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₀⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    (∀ i j, β₁.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₁⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    ∀ ε φ : Lev.EAf D, ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → φ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
    (Formalism.L2.Theta.mt V g).map (toEAf D) = (1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
      ε • (β₁ * β₀⁻¹).val + φ • ((β₀ * β₁⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose →
    (Formalism.L2.Theta.mt V g⁻¹).map (toEAf D) = (1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
      ε • (β₀ * β₁⁻¹).val + φ • ((β₁ * β₀⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose →
    Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β₁ := GlobalTheory.T.unitaryFinitePart_idempotentBlend_mem_latticeStabilizer

theorem smul_entry {e : AE D} {n : ℕ} (P Q : Matrix (Fin n) (Fin n) (AE D)) (he : e * e = e) (hef : e * cA D e = 0)
    (i k : Fin n) :
    e * ((1 - e - cA D e) • (1 : Matrix (Fin n) (Fin n) (AE D)) + e • P + cA D e • (Q.map (cA D)).transpose) i k =
      e * P i k := by
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination (P i k - (1 : Matrix (Fin n) (Fin n) (AE D)) i k) * he +
    ((Q.map (cA D)).transpose i k - (1 : Matrix (Fin n) (Fin n) (AE D)) i k) * hef

theorem mul_half_eq {e : AE D} {n k : ℕ} (H P : Matrix (Fin n) (Fin n) (AE D)) (hH : ∀ i j, e * H i j = e * P i j)
    (u : Matrix (Fin n) (Fin k) (AE D)) (hu : ∀ a b, e * u a b = u a b) : HMul.hMul H u = HMul.hMul P u := by
  ext a b
  simp only [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← hu c b, ← mul_assoc, ← mul_assoc, mul_comm (H a c), mul_comm (P a c), hH]

theorem half_mul_eq {e : AE D} {n k : ℕ} (H P : Matrix (Fin n) (Fin n) (AE D)) (hH : ∀ i j, e * H i j = e * P i j)
    (u : Matrix (Fin k) (Fin n) (AE D)) (hu : ∀ a b, e * u a b = u a b) : HMul.hMul u H = HMul.hMul u P := by
  ext a b
  simp only [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← hu a c, mul_assoc, mul_assoc, mul_left_comm e, mul_left_comm e, hH]

theorem supp_alg {R : Type} [CommRing R] (e f o p q : R) (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) :
    (e + f) * ((1 - e - f) * o + e * p + f * q - o) = (1 - e - f) * o + e * p + f * q - o := by
  linear_combination (p - o) * he + (q - o) * hf + (p + q - o - o) * hef

theorem toEAf_prod {n : ℕ} (A B : Matrix (Fin n) (Fin n) (AE D)) (a b : GL (Fin n) (Lev.EAf D))
    (hA : A.map (toEAf D) = a.val) (hB : B.map (toEAf D) = b.val) (hab : a * b = 1) (i j : Fin n) :
    toEAf D ((A * B) i j) = toEAf D ((1 : Matrix (Fin n) (Fin n) (AE D)) i j) := by
  rw [← Matrix.map_apply (f := toEAf D), Matrix.map_mul, hA, hB, ← Units.val_mul, hab, Units.val_one,
    ← Matrix.map_apply (f := toEAf D), Matrix.map_one _ (map_zero _) (map_one _)]

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_move : ∀ {D : D7} (V : HSp D), V.gram = 1 → ∀ (e : AE D), GlobalTheory.PlaceModelSum.IsOrthSum e → e * cA D e = 0 →
    ∀ (β₀ β₁ : GL (Fin V.rank) (Lev.EAf D)),
    (∀ i j, β₀.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₀⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    (∀ i j, β₁.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₁⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    ∃ (g : GA D V) (x : (AE D)ˣ), Formalism.L2.Theta.SuppAt e V g ∧ Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β₁ ∧
      Formalism.L2.Theta.IsDetAt e V g x ∧
      (∀ (k : ℕ) (u : Matrix (Fin V.rank) (Fin k) (AE D)), (∀ a b, e * u a b = u a b) →
        (HMul.hMul (Formalism.L2.Theta.mt V g) u).map (toEAf D) = HMul.hMul (β₁ * β₀⁻¹).val (u.map (toEAf D))) ∧
      ∀ (k : ℕ) (u : Matrix (Fin k) (Fin V.rank) (AE D)), (∀ a b, e * u a b = u a b) →
        (HMul.hMul u (Formalism.L2.Theta.mt V g⁻¹)).map (toEAf D) = HMul.hMul (u.map (toEAf D)) (β₀ * β₁⁻¹).val := by
  intro D V hV e hO hef β₀ β₁ h₀ h₁
  have he : e * e = e := hO.idem
  have hc : cA D e * cA D e = cA D e := by rw [← map_mul, he]
  have hce : cA D e * e = 0 := by rw [mul_comm, hef]
  choose P hP using fun i j => GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) ((β₁ * β₀⁻¹).val i j)
  choose Q hQ using fun i j => GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) ((β₀ * β₁⁻¹).val i j)
  have hPm : (Matrix.of P).map (toEAf D) = (β₁ * β₀⁻¹).val := by ext i j; exact hP i j
  have hQm : (Matrix.of Q).map (toEAf D) = (β₀ * β₁⁻¹).val := by ext i j; exact hQ i j
  have hPQ : e • (Matrix.of P * Matrix.of Q) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact mul_eq_of_toEAf_eq hO (toEAf_prod _ _ _ _ hPm hQm (by group) i j)
  have hQP : e • (Matrix.of Q * Matrix.of P) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact mul_eq_of_toEAf_eq hO (toEAf_prod _ _ _ _ hQm hPm (by group) i j)
  obtain ⟨g, hg, hgi⟩ := exists_unitary V hV e he hef _ _ hPQ hQP
  have hdd : (Formalism.L2.Theta.mt V g).det * (Formalism.L2.Theta.mt V g⁻¹).det = 1 := by
    rw [← Matrix.det_mul, ← GlobalTheory.AdelicLatMove.mt_mul, mul_inv_cancel, GlobalTheory.AdelicLatMove.mt_one, Matrix.det_one]
  have hdd' : (Formalism.L2.Theta.mt V g⁻¹).det * (Formalism.L2.Theta.mt V g).det = 1 := by rw [mul_comm, hdd]
  refine ⟨g, ⟨e * (Formalism.L2.Theta.mt V g).det + (1 - e), e * (Formalism.L2.Theta.mt V g⁻¹).det + (1 - e), ?_, ?_⟩,
    fun i j => ?_, ?_, rfl, fun k u hu => ?_, fun k u hu => ?_⟩
  · linear_combination ((Formalism.L2.Theta.mt V g).det * (Formalism.L2.Theta.mt V g⁻¹).det - (Formalism.L2.Theta.mt V g).det -
      (Formalism.L2.Theta.mt V g⁻¹).det + 1) * he + e * hdd
  · linear_combination ((Formalism.L2.Theta.mt V g⁻¹).det * (Formalism.L2.Theta.mt V g).det - (Formalism.L2.Theta.mt V g⁻¹).det -
      (Formalism.L2.Theta.mt V g).det + 1) * he + e * hdd'
  · clear hPQ hQP hdd hdd' hPm hQm hP hQ h₀ h₁
    simp only [hg, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact supp_alg _ _ _ _ _ he hc hef
  · refine mem_St V g β₀ β₁ h₀ h₁ (toEAf D e) (toEAf D (cA D e)) (GlobalTheory.IdemFin.toEAf_mem_intAf_of_idem he)
      (GlobalTheory.IdemFin.toEAf_mem_intAf_of_idem hc) ?_ ?_
    · ext i j
      simp only [hg, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply, map_add,
        map_mul, map_sub, map_one, GlobalTheory.AdelicLatMove.toEAf_cA, Matrix.of_apply, hP, hQ]
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    · ext i j
      simp only [hgi, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply, map_add,
        map_mul, map_sub, map_one, GlobalTheory.AdelicLatMove.toEAf_cA, Matrix.of_apply, hP, hQ]
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
  · rw [mul_half_eq (Formalism.L2.Theta.mt V g) (Matrix.of P) (fun i j => by rw [hg]; exact smul_entry _ _ he hef i j) u hu,
      Matrix.map_mul, hPm]
  · rw [half_mul_eq (Formalism.L2.Theta.mt V g⁻¹) (Matrix.of Q) (fun i j => by rw [hgi]; exact smul_entry _ _ he hef i j) u hu,
      Matrix.map_mul, hQm]

theorem adj_eq_inv {V : HSp D} (hV : V.gram = 1) (g : GA D V) :
    ((Formalism.L2.Theta.mt V g).map (cA D)).transpose = Formalism.L2.Theta.mt V g⁻¹ := by
  have h := GlobalTheory.AdelicLatMove.gram_mul_inv V g
  have e1 : V.gram.map (incA D) = 1 := by rw [hV]; exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [e1, Matrix.one_mul, Matrix.mul_one] at h
  exact h.symm

theorem adj_inv_eq {V : HSp D} (hV : V.gram = 1) (g : GA D V) :
    ((Formalism.L2.Theta.mt V g⁻¹).map (cA D)).transpose = Formalism.L2.Theta.mt V g := by
  rw [adj_eq_inv hV, inv_inv]

theorem frame_cancel {R : Type} [CommRing R] {m n : ℕ} (a₀ a₁ : GL (Fin m) R) (b₀ b₁ : GL (Fin n) R)
    (x : Matrix (Fin n) (Fin m) R) :
    HMul.hMul (HMul.hMul (b₁⁻¹).val (HMul.hMul (HMul.hMul (b₁ * b₀⁻¹).val x) (a₀ * a₁⁻¹).val)) a₁.val =
      HMul.hMul (HMul.hMul (b₀⁻¹).val x) a₀.val := by
  simp only [Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (b₁⁻¹).val, Units.inv_mul, Matrix.one_mul, Units.inv_mul, Matrix.mul_one]

theorem frame_cancel' {R : Type} [CommRing R] {m n : ℕ} (a₀ a₁ : GL (Fin m) R) (b₀ b₁ : GL (Fin n) R)
    (x : Matrix (Fin n) (Fin m) R) :
    HMul.hMul (HMul.hMul (b₁⁻¹).val (HMul.hMul (b₁ * b₀⁻¹).val (HMul.hMul x (a₀ * a₁⁻¹).val))) a₁.val =
      HMul.hMul (HMul.hMul (b₀⁻¹).val x) a₀.val := by
  rw [← Matrix.mul_assoc (b₁ * b₀⁻¹).val]
  exact frame_cancel a₀ a₁ b₀ b₁ x

theorem adj_key {R S : Type} [CommRing R] [CommRing S] (c : R →+* R) (f : R →+* S) {a w : ℕ}
    (G' Gi' : Matrix (Fin a) (Fin a) R) (H Hi : Matrix (Fin w) (Fin w) R) (u : Matrix (Fin w) (Fin a) R)
    (βa₀ βa₁ : GL (Fin a) S) (βw₀ βw₁ : GL (Fin w) S)
    (hG : (Gi'.map c).transpose = G') (hH : (H.map c).transpose = Hi)
    (h4 : (HMul.hMul G' (u.map c).transpose).map f = HMul.hMul (βa₁ * βa₀⁻¹).val ((u.map c).transpose.map f))
    (h5 : (HMul.hMul (HMul.hMul G' (u.map c).transpose) Hi).map f =
      HMul.hMul ((HMul.hMul G' (u.map c).transpose).map f) (βw₀ * βw₁⁻¹).val) :
    HMul.hMul (HMul.hMul (βa₁⁻¹).val (((HMul.hMul (HMul.hMul H u) Gi').map c).transpose.map f)) βw₁.val =
      HMul.hMul (HMul.hMul (βa₀⁻¹).val ((u.map c).transpose.map f)) βw₀.val := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, hG, hH, ← Matrix.mul_assoc, h5, h4]
  exact frame_cancel βw₀ βw₁ βa₀ βa₁ _

theorem half_mul_right {e : AE D} {m n k : ℕ} {u : Matrix (Fin m) (Fin n) (AE D)} (hu : ∀ a b, e * u a b = u a b)
    (M : Matrix (Fin n) (Fin k) (AE D)) : ∀ a b, e * (HMul.hMul u M) a b = (HMul.hMul u M) a b := by
  intro a b
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← mul_assoc, hu]

theorem half_mul_left {e : AE D} {m n k : ℕ} {u : Matrix (Fin m) (Fin n) (AE D)} (hu : ∀ a b, e * u a b = u a b)
    (M : Matrix (Fin k) (Fin m) (AE D)) : ∀ a b, e * (HMul.hMul M u) a b = (HMul.hMul M u) a b := by
  intro a b
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_left_comm, hu]

theorem move_elts : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ t : T,
    ∃ (g : GA D A) (g' : GA D A') (h : GA D WW) (x x' y : (AE D)ˣ),
      (Formalism.L2.Theta.SuppAt (Y.e t) A g ∧ Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.St Y.rA.β ∧
        Formalism.L2.Theta.IsDetAt (Y.e t) A g x) ∧
      (Formalism.L2.Theta.SuppAt (Y.e t) A' g' ∧ Formalism.IndefR.Lev.finE A' g' ∈ Formalism.L2.DIV.St Y.rA'.β ∧
        Formalism.L2.Theta.IsDetAt (Y.e t) A' g' x') ∧
      (Formalism.L2.Theta.SuppAt (Y.e t) WW h ∧ Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β ∧
        Formalism.L2.Theta.IsDetAt (Y.e t) WW h y) ∧
      (∀ u : WO A WW, IsHalf (Y.e t) u → frMapO A WW Y.rA.β Y.rW.β (actO A WW g h u) = frMapO A WW X.rA.β X.rW.β u) ∧
      ∀ u : WO A' WW, IsHalf (cA D (Y.e t)) u →
        frMapAdj A' WW Y.rA'.β Y.rW.β (actO A' WW g' h u) = frMapAdj A' WW X.rA'.β X.rW.β u := by
  intro D T L sc G W i j A A' WW X Y hX hY t
  have hI := hY.is.idem t
  have hO := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hI
  obtain ⟨g, x, g1, g2, g3, g4, g5⟩ := exists_move A hY.std.1 _ hO hI.2 X.rA.β Y.rA.β
    (frame_int hX.std hX.is.rigA) (frame_int hY.std hY.is.rigA)
  obtain ⟨g', x', g'1, g'2, g'3, g'4, g'5⟩ := exists_move A' hY.std'.1 _ hO hI.2 X.rA'.β Y.rA'.β
    (frame_int hX.std' hX.is.rigA') (frame_int hY.std' hY.is.rigA')
  obtain ⟨h, y, h1, h2, h3, h4, h5⟩ := exists_move WW hY.stdW.1 _ hO hI.2 X.rW.β Y.rW.β
    (frame_int hX.stdW hX.is.rigW) (frame_int hY.stdW hY.is.rigW)
  refine ⟨g, g', h, x, x', y, ⟨g1, g2, g3⟩, ⟨g'1, g'2, g'3⟩, ⟨h1, h2, h3⟩, fun u hu => ?_, fun u hu => ?_⟩
  · simp only [frMapO, actO]
    rw [Matrix.mul_assoc (Formalism.L2.Theta.mt WW h), h4 _ _ (half_mul_right hu _), g5 _ _ hu]
    exact frame_cancel' X.rA.β Y.rA.β X.rW.β Y.rW.β _
  · have hA' : A'.gram = 1 := hY.std'.1
    have hW : WW.gram = 1 := hY.stdW.1
    have hd : ∀ a b, Y.e t * ((u.map (cA D)).transpose) a b = ((u.map (cA D)).transpose) a b := by
      intro a b
      simp only [Matrix.transpose_apply, Matrix.map_apply]
      conv_rhs => rw [← hu b a]
      rw [map_mul, cA_cA]
    simp only [frMapAdj, actO, hA', hW, inv_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one]
    exact adj_key (cA D) (toEAf D) _ _ _ _ u X.rA'.β Y.rA'.β X.rW.β Y.rW.β (adj_inv_eq hA' g') (adj_eq_inv hW h)
      (g'4 _ _ hd) (h5 _ _ (half_mul_left hd _))

end GlobalTheory.BotUnitMove

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_supported_unitaries_moving_bottomTriples : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ t : T,
    ∃ (g : GA D A) (g' : GA D A') (h : GA D WW) (x x' y : (AE D)ˣ),
      (Formalism.L2.Theta.SuppAt (Y.e t) A g ∧ Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.St Y.rA.β ∧
        Formalism.L2.Theta.IsDetAt (Y.e t) A g x) ∧
      (Formalism.L2.Theta.SuppAt (Y.e t) A' g' ∧ Formalism.IndefR.Lev.finE A' g' ∈ Formalism.L2.DIV.St Y.rA'.β ∧
        Formalism.L2.Theta.IsDetAt (Y.e t) A' g' x') ∧
      (Formalism.L2.Theta.SuppAt (Y.e t) WW h ∧ Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β ∧
        Formalism.L2.Theta.IsDetAt (Y.e t) WW h y) ∧
      (∀ u : WO A WW, IsHalf (Y.e t) u → frMapO A WW Y.rA.β Y.rW.β (actO A WW g h u) = frMapO A WW X.rA.β X.rW.β u) ∧
      ∀ u : WO A' WW, IsHalf (cA D (Y.e t)) u →
        frMapAdj A' WW Y.rA'.β Y.rW.β (actO A' WW g' h u) = frMapAdj A' WW X.rA'.β X.rW.β u := by
  atlas_forward_decl GlobalTheory.BotUnitMove.move_elts
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotFrames

theorem stdFst_actO {D : D7} {A WW : HSp D} (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E))
    (βA βA' : GL (Fin A.rank) (Lev.EAf D)) (βW βW' : GL (Fin WW.rank) (Lev.EAf D)) (g : GA D A) (h : GA D WW)
    (hfr : ∀ u : WO A WW, IsHalf e u → frMapO A WW βA' βW' (actO A WW g h u) = frMapO A WW βA βW u) (u : WO A WW) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA' βW' (actO A WW g h u) = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW u := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  by_cases hu : IsHalf e u
  · rw [hfr u hu]
    have hu' : IsHalf e (actO A WW g h u) := (GlobalTheory.SchrMove.isHalf_actO_iff g h u).2 hu
    by_cases hr : IsIntM (frMapO A WW βA βW u) ∧
        ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (frMapO A WW βA βW u i j)
    · rw [if_pos ⟨hu', hr⟩, if_pos ⟨hu, hr⟩]
    · rw [if_neg fun hh => hr hh.2, if_neg fun hh => hr hh.2]
  · rw [if_neg fun hh => hu ((GlobalTheory.SchrMove.isHalf_actO_iff g h u).1 hh.1), if_neg fun hh => hu hh.1]

theorem move_fst : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (t : T) (g : GA D A) (h : GA D WW) (x y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A g → Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.St Y.rA.β → Formalism.L2.Theta.IsDetAt (Y.e t) A g x →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    (∀ u : WO A WW, IsHalf (Y.e t) u → frMapO A WW Y.rA.β Y.rW.β (actO A WW g h u) = frMapO A WW X.rA.β X.rW.β u) →
    IsThetaAt W.ψ (symplO (GlobalTheory.Grid.neg A) WW) (heisO W.ψ (GlobalTheory.Grid.neg A) WW) (Y.e t)
      (latO (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ fun _ => True) 1 Y.vac
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t) (Y.ideal (locPl G) t) A WW
        X.rA.β X.rW.β)
      (((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) •
        Y.ω t (g⁻¹, h⁻¹) (Y.f t)) := by
  intro D T L sc G W i j A A' WW X Y hX hY t g h x y hsg hstg hdg hsh hsth hdh hfr
  classical
  have hI := hY.is
  have hW : IsWeilDatumO W.ψ (GlobalTheory.Grid.neg A) WW (GlobalTheory.BotFrames.botBeta G i j)
      (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) ((Y.ω t).toSgn true) := hI.weil t
  have hSA : IsSelfDualC (GlobalTheory.Grid.neg A) Y.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hI.rigA.1
  have hSW : IsSelfDualC WW Y.rW.Λ := hI.rigW.1
  let g' : GA D (GlobalTheory.Grid.neg A) := (GlobalTheory.Grid.ofSgn true A).symm g
  have hL : ∀ u, u ∈ (latO (GlobalTheory.Grid.neg A) WW (Y.rA.Λ : Set (Fin A.rank → D.host.E)) (Y.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) ↔
      actO (GlobalTheory.Grid.neg A) WW g' h u ∈ (latO (GlobalTheory.Grid.neg A) WW (Y.rA.Λ : Set (Fin A.rank → D.host.E)) (Y.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) :=
    GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D (GlobalTheory.Grid.neg A) WW Y.rA.Λ Y.rW.Λ Y.rA.β Y.rW.β hSA hSW hI.rigA.2.1 hI.rigW.2.1
      g' h hstg hsth
  have hvθ := hI.isVac.2.theta
  have hvL := hI.isVac.2.lat
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem t)
  have hec := (hI.idem t).2
  have h0 : (Y.ω t).toSgn true (g', h) Y.vac =
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) • Y.vac := by
    obtain ⟨ι, P, es, h1, h2, he⟩ := ho
    rw [he] at hec hsg hsh hdg hdh
    have h3 : ∀ a ∈ P, ∀ b ∈ P, es a * cA D (es b) = 0 := fun a ha b hb => by
      rw [← GlobalTheory.PlaceModelSum.mul_sum_orth h1 h2 ha, ← GlobalTheory.PlaceModelSum.mul_sum_orth h1 h2 hb, RingHom.map_mul,
        mul_mul_mul_comm, hec, mul_zero]
    exact GlobalTheory.WeilSplit.om_latVac_sum hW hSA hSW hvθ hvL es P h1 h2 h3 g' h hsg hsh hL x y hdg hdh
  rw [← isStd_lat_eq hY.std hX.std, ← isStd_lat_eq hY.stdW hX.stdW]
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hI.fst t
  refine ⟨⟨T₀, hT₀⟩, fun T' hT' => ?_⟩
  have hth := GlobalTheory.SchrTheta.isTheta_placeModel D W.ψ hW.std (GlobalTheory.Grid.neg A) WW Y.rA.Λ Y.rW.Λ hSA hSW (Y.e t) ho.idem
    ho.infPart_eq Y.vac hvθ T' hT'
  have hc : ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) ≠ 0 :=
    Circle.coe_ne_zero _
  have pm := GlobalTheory.SchrMove.isPlaceModel_move hW hL hT' hth hc h0
  have hf := hall _ pm
  have hΦ : (fun u => GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t)
      (Y.ideal (locPl G) t) A WW Y.rA.β Y.rW.β (actO (GlobalTheory.Grid.neg A) WW g' h u)) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t)
      (Y.ideal (locPl G) t) A WW X.rA.β X.rW.β :=
    funext fun u => stdFst_actO _ _ _ X.rA.β Y.rA.β X.rW.β Y.rW.β g h hfr u
  have e1 : Y.ω t (g⁻¹, h⁻¹) = (Y.ω t).toSgn true (g'⁻¹, h⁻¹) := rfl
  have hf' : Y.f t = ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ)⁻¹ •
      (Y.ω t).toSgn true (g', h) (T' (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t)
      (Y.ideal (locPl G) t) A WW X.rA.β X.rW.β)) := by
    rw [hf, ← hΦ]; rfl
  rw [e1, hf', map_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel,
    Prod.mk_one_one, map_one, Module.End.one_apply, smul_smul, mul_inv_cancel₀ hc, one_smul]

end GlobalTheory.BotFrames

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardPairFirstMember_movedDatum_splittingScale : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (t : T) (g : GA D A) (h : GA D WW) (x y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A g → Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.St Y.rA.β → Formalism.L2.Theta.IsDetAt (Y.e t) A g x →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    (∀ u : WO A WW, IsHalf (Y.e t) u → frMapO A WW Y.rA.β Y.rW.β (actO A WW g h u) = frMapO A WW X.rA.β X.rW.β u) →
    IsThetaAt W.ψ (symplO (GlobalTheory.Grid.neg A) WW) (heisO W.ψ (GlobalTheory.Grid.neg A) WW) (Y.e t)
      (latO (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ fun _ => True) 1 Y.vac
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t) (Y.ideal (locPl G) t) A WW
        X.rA.β X.rW.β)
      (((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) •
        Y.ω t (g⁻¹, h⁻¹) (Y.f t)) := by
  atlas_forward_decl GlobalTheory.BotFrames.move_fst
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotFrames

theorem isThetaAt_stdSnd_move : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (t : T) (g' : GA D A') (h : GA D WW) (x' y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A' g' → Formalism.IndefR.Lev.finE A' g' ∈ Formalism.L2.DIV.St Y.rA'.β →
    Formalism.L2.Theta.IsDetAt (Y.e t) A' g' x' →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    (∀ u : WO A' WW, IsHalf (cA D (Y.e t)) u →
      frMapAdj A' WW Y.rA'.β Y.rW.β (actO A' WW g' h u) = frMapAdj A' WW X.rA'.β X.rW.β u) →
    IsThetaAt W.ψ (symplO A' WW) (heisO W.ψ A' WW) (cA D (Y.e t))
      (latO A' WW X.rA'.Λ X.rW.Λ fun _ => True) 1 Y.vac'
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t) (Y.ideal (locPl G) t)
        A.rank A' WW X.rA'.β X.rW.β)
      (((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) • Y.ω' t (g'⁻¹, h⁻¹) (Y.f' t)) := by
  intro D T L sc G W i j A A' WW X Y hX hY t g' h x' y hS1 hSt1 hD1 hS2 hSt2 hD2 hfr
  have hi := hY.is
  have hW : IsWeilDatumO W.ψ A' WW (botAlpha L i j t) (botAlpha L i j t / botBeta G i j) (Y.ω' t) :=
    (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hi.weil' t)
  have hSA : IsSelfDualC A' Y.rA'.Λ := hi.rigA'.1
  have hSW : IsSelfDualC WW Y.rW.Λ := hi.rigW.1
  have hFA : Formalism.L2.DIV.IsFrame Y.rA'.β Y.rA'.Λ := hi.rigA'.2.1
  have hFW : Formalism.L2.DIV.IsFrame Y.rW.β Y.rW.Λ := hi.rigW.2.1
  have eA : X.rA'.Λ = Y.rA'.Λ := isStd_lat_eq hX.std' hY.std'
  have eW : X.rW.Λ = Y.rW.Λ := isStd_lat_eq hX.stdW hY.stdW
  rw [eA, eW]
  have hL := GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D A' WW Y.rA'.Λ Y.rW.Λ Y.rA'.β Y.rW.β hSA hSW hFA hFW g' h hSt1 hSt2
  have hvac := hi.isVac'
  have hIS := hi.idem t
  obtain ⟨ι, P, es, hsp, horth, hsum⟩ := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hIS
  have hc0 : Y.e t * cA D (Y.e t) = 0 := hIS.2
  have hes : ∀ k ∈ P, es k * Y.e t = es k := by
    intro k hk
    rw [hsum, Finset.mul_sum, Finset.sum_eq_single_of_mem k hk (fun b hb hne => horth k hk b hb hne)]
    exact (hsp k hk).1
  have hecs : ∀ a ∈ P, ∀ b ∈ P, es a * cA D (es b) = 0 := by
    intro a ha b hb
    have h2 : cA D (es b) * cA D (Y.e t) = cA D (es b) := by rw [← map_mul, hes b hb]
    rw [← hes a ha, ← h2]
    calc es a * Y.e t * (cA D (es b) * cA D (Y.e t)) = es a * cA D (es b) * (Y.e t * cA D (Y.e t)) := by ring
      _ = 0 := by rw [hc0, mul_zero]
  have h0 : Y.ω' t (g', h) Y.vac' =
      ((splitFacO (botAlpha L i j t) (botAlpha L i j t / botBeta G i j) x' y : Circle) : ℂ) • Y.vac' := by
    rw [hsum] at hS1 hS2 hD1 hD2
    exact GlobalTheory.WeilSplit.om_latVac_sum hW hSA hSW hvac.2.theta hvac.2.lat es P hsp horth hecs g' h hS1 hS2 hL x' y hD1 hD2
  have hos := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hIS).conj
  have hc : ((splitFacO (botAlpha L i j t) (botAlpha L i j t / botBeta G i j) x' y : Circle) : ℂ) ≠ 0 :=
    Circle.coe_ne_zero _
  have hΦ : (LinearMap.funLeft ℂ ℂ (actO A' WW g' h))
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (botAlpha L i j t / botBeta G i j) (Y.e t) (Y.ideal (locPl G) t) A.rank A' WW Y.rA'.β Y.rW.β) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (botAlpha L i j t / botBeta G i j) (Y.e t) (Y.ideal (locPl G) t) A.rank A' WW X.rA'.β X.rW.β := by
    funext u
    rw [LinearMap.funLeft_apply]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd
    by_cases hu : IsHalf (cA D (Y.e t)) u
    · have hd : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW Y.rA'.β Y.rW.β (actO A' WW g' h u) =
          GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW X.rA'.β X.rW.β u := by
        unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord
        rw [hfr u hu]
      rw [hd, GlobalTheory.SchrMove.isHalf_actO_iff]
    · rw [if_neg, if_neg]
      · exact fun hh => hu hh.1
      · exact fun hh => hu ((GlobalTheory.SchrMove.isHalf_actO_iff g' h u).1 hh.1)
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hi.snd t
  refine ⟨⟨T₀, hT₀⟩, fun T' hT' => ?_⟩
  have th1 := GlobalTheory.SchrTheta.isTheta_placeModel D W.ψ hW.std A' WW Y.rA'.Λ Y.rW.Λ hSA hSW (cA D (Y.e t)) hos.idem
    hos.infPart_eq Y.vac' hvac.2.theta T' hT'
  have pm := GlobalTheory.SchrMove.isPlaceModel_move hW hL hT' th1 hc h0
  have hf' := hall _ pm
  have omm : ∀ p q (F : WO A' WW → ℂ), Y.ω' t p (Y.ω' t q F) = Y.ω' t (p * q) F := fun p q F => by
    rw [map_mul]; rfl
  show _ = T' _
  rw [← hΦ, hf']
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [omm, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]
  rfl

end GlobalTheory.BotFrames
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_pair_second_eq_moved_bottom_datum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (t : T) (g' : GA D A') (h : GA D WW) (x' y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A' g' → Formalism.IndefR.Lev.finE A' g' ∈ Formalism.L2.DIV.St Y.rA'.β →
    Formalism.L2.Theta.IsDetAt (Y.e t) A' g' x' →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    (∀ u : WO A' WW, IsHalf (cA D (Y.e t)) u →
      frMapAdj A' WW Y.rA'.β Y.rW.β (actO A' WW g' h u) = frMapAdj A' WW X.rA'.β X.rW.β u) →
    IsThetaAt W.ψ (symplO A' WW) (heisO W.ψ A' WW) (cA D (Y.e t))
      (latO A' WW X.rA'.Λ X.rW.Λ fun _ => True) 1 Y.vac'
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t) (Y.ideal (locPl G) t)
        A.rank A' WW X.rA'.β X.rW.β)
      (((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) • Y.ω' t (g'⁻¹, h⁻¹) (Y.f' t)) := by
  atlas_forward_decl GlobalTheory.BotFrames.isThetaAt_stdSnd_move
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotFrames

open Formalism.L2.JoinChr

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem chr_mem_of_idemSum {K : Type} [Field K] {σ : K →+* ℂ} {D : D7} {c : (AE D)ˣ →* Circle}
    {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ) (hχ : LocIn σ χ) {e : AE D}
    {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S) (x : (AE D)ˣ) (d : AE D)
    (hx : (x : AE D) = e * d + (1 - e)) : ((c x : Circle) : ℂ) ∈ σ.fieldRange := by
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have heT : ∀ P, ι (finPart D (∑ PP ∈ S, es PP)) P = if P ∈ S then 1 else 0 := by
    intro P
    rw [map_sum, map_sum, GlobalTheory.FlipCharFormula.fa_sum,
      Finset.sum_congr rfl (fun PP hPP => GlobalTheory.FlipCharFormula.comp_of_isIdemAt ι h1 h2 (hes PP hPP) P)]
    exact Finset.sum_ite_eq S P (fun _ => (1 : HeightOneSpectrum.adicCompletion D.host.E P))
  have hinfT : infPart D (∑ PP ∈ S, es PP) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero (fun PP hPP => GlobalTheory.FlipCharFormula.infPart_of_isIdemAt (hes PP hPP))
  have hinf : infPart D (x : AE D) = 1 := by
    rw [hx, map_add, map_mul, map_sub, hinfT, map_one, zero_mul, zero_add, sub_zero]
  have hout : ∀ P, P ∉ S → ι (finPart D (x : AE D)) P = 1 := by
    intro P hP
    rw [hx, map_add, map_mul, map_sub, map_one, map_add, map_mul, map_sub, map_one, GlobalTheory.FlipCharFormula.fa_add,
      GlobalTheory.FlipCharFormula.fa_mul, GlobalTheory.FlipCharFormula.fa_sub, GlobalTheory.FlipCharFormula.fa_one, heT, if_neg hP]
    simp
  have hne : ∀ P, ι (finPart D (x : AE D)) P ≠ 0 := by
    intro P h0
    have h := congrArg (fun z => ι (finPart D z) P) (Units.mul_inv x)
    simp only [map_mul, map_one, GlobalTheory.FlipCharFormula.fa_mul, GlobalTheory.FlipCharFormula.fa_one, h0, zero_mul] at h
    exact zero_ne_one h
  have hk : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ k : D.host.Eˣ,
      Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k : D.host.E) ∧
      Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k : D.host.E)) ≤
        P.valuation D.host.E (N : D.host.E) * P.valuation D.host.E (k : D.host.E) := fun P => by
    obtain ⟨k, a, b, -⟩ := GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P _ (hne P)
    exact ⟨k, a, b⟩
  choose k hk1 hk2 using hk
  have hI : Ideal.span {((N : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  have key := hprod x hinf (S ∪ (Ideal.finite_factors hI).toFinset) k (fun P _ => ⟨hk1 P, hk2 P⟩)
    (fun P hP => by
      have hPS : P ∉ S := fun h => hP (Finset.mem_union_left _ h)
      refine ⟨by rw [hout P hPS, map_one], fun hNP => hP (Finset.mem_union_right _ ?_)⟩
      rw [Set.Finite.mem_toFinset]
      exact Ideal.dvd_span_singleton.mpr hNP)
  rw [key]
  refine Subfield.prod_mem _ fun P _ => ?_
  rw [← SetLike.mem_coe, RingHom.coe_fieldRange]
  exact hχ P _

set_option maxHeartbeats 800000 in

theorem factor_mem_field : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (S : GridChoice W Set.univ)
    (μ₀ : T), L.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (Y : Tri T A A' WW),
    IsBottomTri W i j Y → ∀ (t : T) (g : GA D A) (g' : GA D A') (h : GA D WW) (x x' y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A g → Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.St Y.rA.β → Formalism.L2.Theta.IsDetAt (Y.e t) A g x →
    Formalism.L2.Theta.SuppAt (Y.e t) A' g' → Formalism.IndefR.Lev.finE A' g' ∈ Formalism.L2.DIV.St Y.rA'.β →
    Formalism.L2.Theta.IsDetAt (Y.e t) A' g' x' →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    ∃ z : D.what₂.LLˣ, D.what₂.embLL z =
      ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) /
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) := by
  intro D T L sc G W S μ₀ hL hN i j A A' WW Y hY t g g' h x x' y _ _ hx _ _ hx' _ _ hy
  have he := hY.is.idem t
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have mem : ∀ (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → LocIn D.what₂.embLL χ →
      ∀ (u : (AE D)ˣ) (d : AE D), (u : AE D) = Y.e t * d + (1 - Y.e t) → ((c u : Circle) : ℂ) ∈ D.what₂.embLL.fieldRange :=
    fun c χ hc hχ u d hu => chr_mem_of_idemSum hc hχ he u d hu
  have m1 := mem _ _ (hL.mu0 j) (hN.chars.mu0 j)
  have m2 := mem _ _ (hL.xi t) (hN.chars.xi t)
  have m3 := mem _ _ (G.ch.chi_eq _ hm.1 hm.2) (hN.chars.chi _ hm.1 hm.2)
  set a := L.mu0 ((j : ℕ) + 1)
  set b := L.xi t
  set c := G.ch.chi (D.R.m - (i : ℕ))
  set η := L.eta ^ (rankV D i j % 2)
  have hv : ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) /
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) =
      ((a x' : ℂ) * b x')⁻¹ * c x' * (((a x : ℂ) * b x)⁻¹ * c x) * ((a y : ℂ) * b y * (c y : ℂ)⁻¹) := by
    have e1 : GlobalTheory.BotFrames.botAlpha L i j t = a * b * η := rfl
    have e2 : GlobalTheory.BotFrames.botBeta G i j = c * η := rfl
    rw [e1, e2]
    simp only [splitFacO, MonoidHom.div_apply, MonoidHom.mul_apply, Circle.coe_mul, Circle.coe_inv, Circle.coe_div]
    have n1 := Circle.coe_ne_zero (a x'); have n2 := Circle.coe_ne_zero (b x'); have n3 := Circle.coe_ne_zero (c x')
    have n4 := Circle.coe_ne_zero (η x'); have n5 := Circle.coe_ne_zero (a x); have n6 := Circle.coe_ne_zero (b x)
    have n7 := Circle.coe_ne_zero (c x); have n8 := Circle.coe_ne_zero (η x); have n9 := Circle.coe_ne_zero (a y)
    have n10 := Circle.coe_ne_zero (b y); have n11 := Circle.coe_ne_zero (c y); have n12 := Circle.coe_ne_zero (η y)
    field_simp
  have hmem : (((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) /
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ)) ∈
      D.what₂.embLL.fieldRange := by
    rw [hv]
    refine mul_mem (mul_mem (mul_mem (inv_mem (mul_mem (m1 _ _ hx') (m2 _ _ hx'))) (m3 _ _ hx'))
      (mul_mem (inv_mem (mul_mem (m1 _ _ hx) (m2 _ _ hx))) (m3 _ _ hx)))
      (mul_mem (mul_mem (m1 _ _ hy) (m2 _ _ hy)) (inv_mem (m3 _ _ hy)))
  obtain ⟨z, hz⟩ := hmem
  have hne : ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) /
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) ≠ 0 :=
    div_ne_zero (Circle.coe_ne_zero _) (Circle.coe_ne_zero _)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero] at hz
    exact hne hz.symm
  exact ⟨Units.mk0 z hz0, hz⟩

end GlobalTheory.BotFrames

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definite_bottom_triple_basis_change_factor_mem_field : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (S : GridChoice W Set.univ)
    (μ₀ : T), L.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (Y : Tri T A A' WW),
    IsBottomTri W i j Y → ∀ (t : T) (g : GA D A) (g' : GA D A') (h : GA D WW) (x x' y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A g → Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.St Y.rA.β → Formalism.L2.Theta.IsDetAt (Y.e t) A g x →
    Formalism.L2.Theta.SuppAt (Y.e t) A' g' → Formalism.IndefR.Lev.finE A' g' ∈ Formalism.L2.DIV.St Y.rA'.β →
    Formalism.L2.Theta.IsDetAt (Y.e t) A' g' x' →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    ∃ z : D.what₂.LLˣ, D.what₂.embLL z =
      ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) /
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) := by
  atlas_forward_decl GlobalTheory.BotFrames.factor_mem_field
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotTranslate

open GlobalTheory.Grid (neg sgn ofSgn)

variable {D : D7}

theorem compAt_eq_map (θ : InfFam D) (τ : D.what₂.Tau) {m n : ℕ} (w : Mx D m n) :
    compAt θ τ w = w.map ((θ τ).comp (infPart D)) := rfl

theorem compAt_mt_of_suppAt {e : AE D} (he : infPart D e = 0) (hce : infPart D (cA D e) = 0) {V : HSp D} {g : GA D V}
    (hg : SuppAt e V g) (θ : InfFam D) (τ : D.what₂.Tau) : compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
  ext i j
  have h1 := hg i j
  have e1 : Formalism.L2.Theta.mt V g i j = (e + cA D e) * (Formalism.L2.Theta.mt V g - 1) i j + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j := by
    rw [h1, Matrix.sub_apply, sub_add_cancel]
  simp only [compAt, Matrix.map_apply]
  rw [e1, (infPart D).map_add, (infPart D).map_mul, (infPart D).map_add, he, hce, add_zero, zero_mul, (θ τ).map_add,
    (θ τ).map_zero, zero_add]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [Matrix.one_apply_ne hij]

theorem compAt_mt_inv {V : HSp D} {g : GA D V} {θ : InfFam D} {τ : D.what₂.Tau} (hg : compAt θ τ (Formalism.L2.Theta.mt V g) = 1) :
    compAt θ τ (Formalism.L2.Theta.mt V g⁻¹) = 1 := by
  have hm : Formalism.L2.Theta.mt V g⁻¹ * Formalism.L2.Theta.mt V g = 1 := by
    simp only [Formalism.L2.Theta.mt]
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have h2 : compAt θ τ (Formalism.L2.Theta.mt V g⁻¹) * compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
    rw [compAt_eq_map, compAt_eq_map, ← Matrix.map_mul, hm, Matrix.map_one _ (map_zero _) (map_one _)]
  rwa [hg, Matrix.mul_one] at h2

theorem integrableOn_mul_right_iff {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (k : G) (hk : Measure.map (fun g => g * k) μ = μ) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) :
    IntegrableOn (fun g => f (g * k)) 𝓕 μ ↔ IntegrableOn f 𝓕 μ := by
  have hmp : MeasurePreserving (fun g : G => g * k) μ μ := ⟨measurable_mul_const k, hk⟩
  have hemb : MeasurableEmbedding (fun g : G => g * k) := measurableEmbedding_mulRight k
  have h2 : IsFundamentalDomain Γ ((fun g : G => g * k) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id ?_
    intro γ g
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  rw [h𝓕.integrableOn_iff h2 (fun γ g => by simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]; exact hf γ γ.2 _)]
  exact hmp.integrableOn_comp_preimage hemb

end GlobalTheory.BotTranslate

namespace GlobalTheory.BotTranslate

open GlobalTheory.Grid (neg sgn ofSgn)

set_option maxHeartbeats 2000000 in

theorem translate : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (g : T → GA D A) (g' : T → GA D A') (h : T → GA D WW) (κ κ' : T → ℂ), (∀ t, κ t ≠ 0) → (∀ t, κ' t ≠ 0) →
    (∀ t, Formalism.L2.Theta.SuppAt (Y.e t) A (g t) ∧ Formalism.IndefR.Lev.finE A (g t) ∈ Formalism.L2.DIV.St Y.rA.β) →
    (∀ t, Formalism.L2.Theta.SuppAt (Y.e t) A' (g' t) ∧ Formalism.IndefR.Lev.finE A' (g' t) ∈ Formalism.L2.DIV.St Y.rA'.β) →
    (∀ t, Formalism.L2.Theta.SuppAt (Y.e t) WW (h t) ∧ Formalism.IndefR.Lev.finE WW (h t) ∈ Formalism.L2.DIV.St Y.rW.β) →
    ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c →
      (GlobalTheory.BotFrames.reRig Y X.rA X.rA' X.rW (fun t => κ t • Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t))
        (fun t => κ' t • Y.ω' t ((g' t)⁻¹, (h t)⁻¹) (Y.f' t))).IsConst W.ψ W.θ fun t => κ t / κ' t * c t := by
  intro D T L sc G W i j A A' WW X Y hX hY g g' h κ κ' hκ hκ' hg hg' hh c hc
  obtain ⟨⟨t₀, hc₀⟩, P, P', H⟩ := hc
  have hYi := hY.is
  have hψ := hYi.isVac.1
  have hθ := hYi.isVac.2.inf
  have sA := GlobalTheory.BotFrames.isStd_s_eq hX.std hY.std
  have sA' := GlobalTheory.BotFrames.isStd_s_eq hX.std' hY.std'
  have sW := GlobalTheory.BotFrames.isStd_s_eq hX.stdW hY.stdW
  have bA := GlobalTheory.BotFrames.isStd_B_eq hX.std hY.std
  have bA' := GlobalTheory.BotFrames.isStd_B_eq hX.std' hY.std'
  have bW := GlobalTheory.BotFrames.isStd_B_eq hX.stdW hY.stdW
  have he := fun t => Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_of_idemSum (hYi.idem t)
  have hce := fun t => Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_cA_idemSum (hYi.idem t)
  have cg : ∀ t τ, compAt W.θ τ (Formalism.L2.Theta.mt A (g t)⁻¹) = 1 := fun t τ =>
    compAt_mt_inv (compAt_mt_of_suppAt (he t) (hce t) (hg t).1 W.θ τ)
  have cg' : ∀ t τ, compAt W.θ τ (Formalism.L2.Theta.mt A' (g' t)⁻¹) = 1 := fun t τ =>
    compAt_mt_inv (compAt_mt_of_suppAt (he t) (hce t) (hg' t).1 W.θ τ)
  have ch : ∀ t τ, compAt W.θ τ (Formalism.L2.Theta.mt WW (h t)⁻¹) = 1 := fun t τ =>
    compAt_mt_inv (compAt_mt_of_suppAt (he t) (hce t) (hh t).1 W.θ τ)
  set Y₁ := GlobalTheory.BotFrames.reRig Y X.rA X.rA' X.rW (fun t => κ t • Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t))
    (fun t => κ' t • Y.ω' t ((g' t)⁻¹, (h t)⁻¹) (Y.f' t)) with hY₁

  have hK : ∀ t Q h'' g'', Y₁.ker W.ψ W.θ t Q h'' g'' = κ t * Y.ker W.ψ W.θ t Q (h'' * (h t)⁻¹) (g'' * (g t)⁻¹) := by
    intro t Q h'' g''
    have tf := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (hYi.fst t) hYi.isVac.2.theta
    have c0 : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt (neg A) ((ofSgn true A).symm (g t)⁻¹)) = 1 := cg t
    have key := (GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ (neg A) WW _ _ ((Y.ω t).toSgn true) (hYi.weil t) hθ
      (fun τ => -Y.rA.s τ) (fun τ => -Y.rA.s τ) Y.rA.B Y.rA.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B
      ((ofSgn true A).symm (g t)⁻¹) (h t)⁻¹ (fun τ => by rw [c0 τ, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [ch t τ, Matrix.mul_one, Matrix.one_mul]) (fun τ => by rw [c0 τ, Matrix.one_mul])
      (fun τ => by rw [ch t τ, Matrix.one_mul]) (Y.f t) tf Q).2
    have key' : Y.ω t ((g t)⁻¹, (h t)⁻¹)
        (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) Q) =
        pureTensorO W.ψ W.θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t)) Q :=
      key
    show thetaKO (Y.ω t) g'' h'' (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B
        (κ t • Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t)) Q) =
      κ t * thetaKO (Y.ω t) (g'' * (g t)⁻¹) (h'' * (h t)⁻¹)
        (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) Q)
    rw [sA, sW, bA, bW, Formalism.IndefR.Eqv.KerDiag.pureTensorO_smul, ← key']
    unfold thetaKO
    rw [map_smul, Pi.smul_apply, smul_eq_mul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]
  have hK' : ∀ t Q h'' g'', Y₁.ker' W.ψ W.θ t Q h'' g'' = κ' t * Y.ker' W.ψ W.θ t Q (h'' * (h t)⁻¹) (g'' * (g' t)⁻¹) := by
    intro t Q h'' g''
    have tf := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (hYi.snd t) hYi.isVac'.2.theta
    have hw : IsWeilDatumO W.ψ A' WW _ _ (Y.ω' t) := hYi.weil' t
    have key := (GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ A' WW _ _ (Y.ω' t) hw hθ
      Y.rA'.s Y.rA'.s Y.rA'.B Y.rA'.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B
      (g' t)⁻¹ (h t)⁻¹ (fun τ => by rw [cg' t τ, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [ch t τ, Matrix.mul_one, Matrix.one_mul]) (fun τ => by rw [cg' t τ, Matrix.one_mul])
      (fun τ => by rw [ch t τ, Matrix.one_mul]) (Y.f' t) tf Q).2
    show thetaKO (Y.ω' t) g'' h'' (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B
        (κ' t • Y.ω' t ((g' t)⁻¹, (h t)⁻¹) (Y.f' t)) Q) =
      κ' t * thetaKO (Y.ω' t) (g'' * (g' t)⁻¹) (h'' * (h t)⁻¹)
        (pureTensorO W.ψ W.θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) Q)
    rw [sA', sW, bA', bW, Formalism.IndefR.Eqv.KerDiag.pureTensorO_smul, ← key]
    unfold thetaKO
    rw [map_smul, Pi.smul_apply, smul_eq_mul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]

  haveI := hYi.meas.1
  haveI := hYi.meas'.1
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D A Y.m hYi.meas.1).1
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D A' Y.m' hYi.meas'.1).1
  have mk : ∀ k : GA D A, Measure.map (fun x => x * k) Y.m = Y.m := fun k => MeasureTheory.map_mul_right_eq_self Y.m k
  have mk' : ∀ k : GA D A', Measure.map (fun x => x * k) Y.m' = Y.m' := fun k => MeasureTheory.map_mul_right_eq_self Y.m' k
  have hI : ∀ t Q h'', Y₁.I W.ψ W.θ t Q h'' = κ t * Y.I W.ψ W.θ t Q (h'' * (h t)⁻¹) := by
    intro t Q h''
    show ∫ x in Y.fd, Y₁.ker W.ψ W.θ t Q h'' x ∂Y.m = κ t * ∫ x in Y.fd, Y.ker W.ψ W.θ t Q (h'' * (h t)⁻¹) x ∂Y.m
    simp_rw [hK]
    rw [integral_const_mul]
    congr 1
    exact GlobalTheory.DownLift.TypeLaw.setIntegral_mul_right_of_fd (GQ A) Y.m Y.fd hYi.meas.2 _ (mk _) _
      (GlobalTheory.SqTower.Normal.ker_left hYi t Q _)
  have hI' : ∀ t Q h'', Y₁.I' W.ψ W.θ t Q h'' = κ' t * Y.I' W.ψ W.θ t Q (h'' * (h t)⁻¹) := by
    intro t Q h''
    show ∫ x in Y.fd', Y₁.ker' W.ψ W.θ t Q h'' x ∂Y.m' = κ' t * ∫ x in Y.fd', Y.ker' W.ψ W.θ t Q (h'' * (h t)⁻¹) x ∂Y.m'
    simp_rw [hK']
    rw [integral_const_mul]
    congr 1
    exact GlobalTheory.DownLift.TypeLaw.setIntegral_mul_right_of_fd (GQ A') Y.m' Y.fd' hYi.meas'.2 _ (mk' _) _
      (GlobalTheory.SqTower.Normal.ker'_left hYi t Q _)
  refine ⟨⟨t₀, mul_ne_zero (div_ne_zero (hκ t₀) (hκ' t₀)) hc₀⟩, P, P', fun t => ⟨fun h'' => ⟨?_, ?_⟩, ?_, fun h'' => ?_⟩⟩
  · show IntegrableOn (Y₁.ker W.ψ W.θ t P h'') Y.fd Y.m
    rw [show Y₁.ker W.ψ W.θ t P h'' = fun x => κ t * Y.ker W.ψ W.θ t P (h'' * (h t)⁻¹) (x * (g t)⁻¹) from funext (hK t P h'')]
    exact ((integrableOn_mul_right_iff (GQ A) Y.m Y.fd hYi.meas.2 _ (mk _) _
      (GlobalTheory.SqTower.Normal.ker_left hYi t P _)).2 ((H t).1 _).1).const_mul _
  · show IntegrableOn (Y₁.ker' W.ψ W.θ t P' h'') Y.fd' Y.m'
    rw [show Y₁.ker' W.ψ W.θ t P' h'' = fun x => κ' t * Y.ker' W.ψ W.θ t P' (h'' * (h t)⁻¹) (x * (g' t)⁻¹) from funext (hK' t P' h'')]
    exact ((integrableOn_mul_right_iff (GQ A') Y.m' Y.fd' hYi.meas'.2 _ (mk' _) _
      (GlobalTheory.SqTower.Normal.ker'_left hYi t P' _)).2 ((H t).1 _).2).const_mul _
  · obtain ⟨h₀, hne⟩ := (H t).2.1
    refine ⟨h₀ * h t, ?_⟩
    rw [hI', mul_inv_cancel_right]
    exact mul_ne_zero (hκ' t) hne
  · rw [hI, hI', (H t).2.2]
    field_simp [hκ' t]

end GlobalTheory.BotTranslate

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottomTriple_weilMove_rightTranslate : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (g : T → GA D A) (g' : T → GA D A') (h : T → GA D WW) (κ κ' : T → ℂ), (∀ t, κ t ≠ 0) → (∀ t, κ' t ≠ 0) →
    (∀ t, Formalism.L2.Theta.SuppAt (Y.e t) A (g t) ∧ Formalism.IndefR.Lev.finE A (g t) ∈ Formalism.L2.DIV.St Y.rA.β) →
    (∀ t, Formalism.L2.Theta.SuppAt (Y.e t) A' (g' t) ∧ Formalism.IndefR.Lev.finE A' (g' t) ∈ Formalism.L2.DIV.St Y.rA'.β) →
    (∀ t, Formalism.L2.Theta.SuppAt (Y.e t) WW (h t) ∧ Formalism.IndefR.Lev.finE WW (h t) ∈ Formalism.L2.DIV.St Y.rW.β) →
    ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c →
      (GlobalTheory.BotFrames.reRig Y X.rA X.rA' X.rW (fun t => κ t • Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t))
        (fun t => κ' t • Y.ω' t ((g' t)⁻¹, (h t)⁻¹) (Y.f' t))).IsConst W.ψ W.θ fun t => κ t / κ' t * c t := by
  atlas_forward_decl GlobalTheory.BotTranslate.translate
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotFrames

theorem frames_transfer : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (S : GridChoice W Set.univ),
    IsStdChar D W.ψ (-1) → ∀ μ₀ : T, L.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
    (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y →
    ∃ Y₁ : Tri T A A' WW, IsBottomTri W i j Y₁ ∧ Y₁.rA = X.rA ∧ Y₁.rA' = X.rA' ∧ Y₁.rW = X.rW ∧
      ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → ∃ u : T → D.what₂.LLˣ, Y₁.IsConst W.ψ W.θ fun t => D.what₂.embLL (u t) * c t := by
  intro D T L sc G W S _ μ₀ hL hN i j A A' WW X Y hX hY
  choose g g' h x x' y hE using fun t => GlobalTheory.T.exists_supported_unitaries_moving_bottomTriples W i j A A' WW X Y hX hY t
  have hC := fun t => GlobalTheory.T.definite_bottom_triple_basis_change_factor_mem_field W S μ₀ hL hN i j A A' WW Y hY t (g t) (g' t) (h t) (x t) (x' t) (y t)
    (hE t).1.1 (hE t).1.2.1 (hE t).1.2.2 (hE t).2.1.1 (hE t).2.1.2.1 (hE t).2.1.2.2 (hE t).2.2.1.1 (hE t).2.2.1.2.1
    (hE t).2.2.1.2.2
  choose z hz using hC
  have κne : ∀ t, ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t)
      (x t) (y t) : Circle) : ℂ) ≠ 0 := fun t => Circle.coe_ne_zero _
  have κne' : ∀ t, ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j)
      (x' t) (y t) : Circle) : ℂ) ≠ 0 := fun t => Circle.coe_ne_zero _
  have sA := GlobalTheory.BotFrames.isStd_s_eq hX.std hY.std
  have sA' := GlobalTheory.BotFrames.isStd_s_eq hX.std' hY.std'
  have sW := GlobalTheory.BotFrames.isStd_s_eq hX.stdW hY.stdW
  have lA := GlobalTheory.BotFrames.isStd_lat_eq hX.std hY.std
  have lA' := GlobalTheory.BotFrames.isStd_lat_eq hX.std' hY.std'
  have lW := GlobalTheory.BotFrames.isStd_lat_eq hX.stdW hY.stdW
  refine ⟨GlobalTheory.BotFrames.reRig Y X.rA X.rA' X.rW
    (fun t => ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t)
      (x t) (y t) : Circle) : ℂ) • Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t))
    (fun t => ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j)
      (x' t) (y t) : Circle) : ℂ) • Y.ω' t ((g' t)⁻¹, (h t)⁻¹) (Y.f' t)),
    ⟨hY.rank, hY.rank', hX.std, hX.std', hX.stdW, ?_⟩, rfl, rfl, rfl, fun c hc => ?_⟩
  · have hi := hY.is
    refine ⟨hi.rank, hX.is.rigA, hX.is.rigA', hX.is.rigW, hi.weil, hi.weil', ?_, ?_, hi.idem, hi.expo,
      fun t => GlobalTheory.T.standardPairFirstMember_movedDatum_splittingScale W i j A A' WW X Y hX hY t (g t) (h t) (x t) (y t) (hE t).1.1 (hE t).1.2.1 (hE t).1.2.2 (hE t).2.2.1.1
        (hE t).2.2.1.2.1 (hE t).2.2.1.2.2 (hE t).2.2.2.1,
      fun t => GlobalTheory.T.standard_pair_second_eq_moved_bottom_datum W i j A A' WW X Y hX hY t (g' t) (h t) (x' t) (y t) (hE t).2.1.1 (hE t).2.1.2.1 (hE t).2.1.2.2
        (hE t).2.2.1.1 (hE t).2.2.1.2.1 (hE t).2.2.1.2.2 (hE t).2.2.2.2, hi.meas, hi.meas'⟩
    · show IsVacO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.Λ X.rW.Λ Y.vac
      rw [sA, sW, lA, lW]
      exact hi.isVac
    · show IsVacO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.Λ X.rW.Λ Y.vac'
      rw [sA', sW, lA', lW]
      exact hi.isVac'
  · refine ⟨fun t => (z t)⁻¹, ?_⟩
    have hD := GlobalTheory.T.definiteBottomTriple_weilMove_rightTranslate W i j A A' WW X Y hX hY g g' h _ _ κne κne' (fun t => ⟨(hE t).1.1, (hE t).1.2.1⟩)
      (fun t => ⟨(hE t).2.1.1, (hE t).2.1.2.1⟩) (fun t => ⟨(hE t).2.2.1.1, (hE t).2.2.1.2.1⟩) c hc
    convert hD using 2 with t
    rw [map_units_inv, hz t, inv_div]

end GlobalTheory.BotFrames

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_definiteBottomTriple_transferred_frames : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (S : GridChoice W Set.univ),
    IsStdChar D W.ψ (-1) → ∀ μ₀ : T, L.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
    (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y →
    ∃ Y₁ : Tri T A A' WW, IsBottomTri W i j Y₁ ∧ Y₁.rA = X.rA ∧ Y₁.rA' = X.rA' ∧ Y₁.rW = X.rW ∧
      ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → ∃ u : T → D.what₂.LLˣ, Y₁.IsConst W.ψ W.θ fun t => D.what₂.embLL (u t) * c t := by
  atlas_forward_decl GlobalTheory.BotFrames.frames_transfer
end
