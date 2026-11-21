import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.ZD
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Comparison
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Topology
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.Assembly
import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LeafDefs

section
noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open Reformulated.AutPerF Ideal

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R] [IsDomain R] [ValuationRing R] [CharZero R]
  [IsAlgClosed (FractionRing R)]



end Formalism.BasicNotions.CmpTie.Incl
end
end

section
noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable {l : ℕ} [Fact l.Prime] {A B P D : Type} [CommRing A] [CommRing B] [CommRing P] [CommRing D]
  [Algebra A B] [Algebra P D]

def IsCrisDRA (ι : A →+* P) (f : B →+* D) : Prop :=
  ∀ x : A, f (algebraMap A B x) = algebraMap P D (ι x)

theorem isCrisDRA_iff (cA : A ≃+* ACris.ACris ℂ_[l] l) (cBc : B ≃+* Formalism.Per6.Bcris l) (cP : P ≃+* Formalism.Per6.BdRp l)
    (cD : D ≃+* Formalism.Per6.BdR l) (ι : A →+* P)
    (hB : ∀ x : A, cBc (algebraMap A B x) = Formalism.Per6.cB l (cA x))
    (hD : ∀ y : P, cD (algebraMap P D y) = algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (cP y))
    (hι : ∀ x : A, cP (ι x) = ACris.iota ℂ_[l] l (cA x)) (f : B →+* D) :
    IsCrisDRA ι f ↔ Formalism.Per6.IsCrisDR l ((cD.toRingHom.comp f).comp cBc.symm.toRingHom) := by
  constructor
  · intro hf x6
    obtain ⟨x, rfl⟩ := cA.surjective x6
    have h1 : cBc.symm (Formalism.Per6.cB l (cA x)) = algebraMap A B x := by
      rw [← hB x, RingEquiv.symm_apply_apply]
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [h1, hf x, hD, hι]
  · intro hf x
    apply cD.injective
    have h2 := hf (cA x)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at h2
    rw [← hB x, RingEquiv.symm_apply_apply] at h2
    rw [h2, hD, hι]

end Formalism.BasicNotions.CmpTie.Incl
end
end

section
noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open Reformulated.AutPerF

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (Ideal.span {(p : R)}) R] [IsDomain R] [ValuationRing R] [CharZero R]
  [IsAlgClosed (FractionRing R)]

theorem isCrisDRA_toBdRPlus_iff (f : Bcris p R →+* BdR p R) :
    IsCrisDRA (Acris.toBdRPlus p R) f ↔ f = Bcris.toBdR p R := by
  constructor
  · intro hf
    refine Bcris.hom_ext fun x => ?_
    have h := BcrisPlus.hom_ext (f := f.comp (algebraMap (BcrisPlus p R) (Bcris p R)))
      (g := (Bcris.toBdR p R).comp (algebraMap (BcrisPlus p R) (Bcris p R))) (fun y => by
        simp only [RingHom.comp_apply]
        rw [← IsScalarTower.algebraMap_apply, hf y, Bcris.toBdR_algebraMap_acris])
    exact RingHom.congr_fun h x
  · rintro rfl x
    exact Bcris.toBdR_algebraMap_acris x

end Formalism.BasicNotions.CmpTie.Incl
end
end

section
noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open Reformulated.AutPerF Ideal

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R] [IsDomain R] [ValuationRing R] [CharZero R]
  [IsAlgClosed (FractionRing R)]

structure IsCrisDRF (f : Bcris p R →+* BdR p R) : Prop where
  on0 : ∀ a : AcrisZero p R, f (algebraMap (Acris p R) (Bcris p R) (algebraMap (AcrisZero p R) (Acris p R) a)) =
    algebraMap (BdRPlus p R) (BdR p R) (algebraMap (AinfInv p R) (BdRPlus p R) (a : AinfInv p R))
  bdd : ∀ n : ℕ, ∃ N : ℕ, ∀ x : Acris p R, ∃ (y : BdRPlus p R) (a : Ainf p R),
    f (algebraMap (Acris p R) (Bcris p R) x) = algebraMap (BdRPlus p R) (BdR p R) y ∧
      BdRPlus.eval p R n ((p : BdRPlus p R) ^ N * y) =
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) a)

theorem isCrisDRF_toBdR : IsCrisDRF (Bcris.toBdR p R) := by
  refine ⟨fun a => ?_, fun n => ⟨n, fun x => ?_⟩⟩
  · rw [Bcris.toBdR_algebraMap_acris, Acris.toBdRPlus_algebraMap_zero]
  · obtain ⟨b, hb⟩ := AcrisZero.exists_p_pow_mul_eq n (Acris.toRange p R n x)
    refine ⟨Acris.toBdRPlus p R x, b, Bcris.toBdR_algebraMap_acris x, ?_⟩
    have h1 := congrArg Subtype.val hb
    simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast, RingHom.coe_rangeRestrict] at h1
    rw [map_mul, map_pow, map_natCast, Acris.eval_toBdRPlus, h1]
    rfl

theorem eval_eq_of_isCrisDRF {f : Bcris p R →+* BdR p R} (hf : IsCrisDRF f) (x : Acris p R) (y : BdRPlus p R)
    (hy : f (algebraMap (Acris p R) (Bcris p R) x) = algebraMap (BdRPlus p R) (BdR p R) y) (n : ℕ) :
    BdRPlus.eval p R n y = BdRPlus.eval p R n (Acris.toBdRPlus p R x) := by
  have hinj : Function.Injective (algebraMap (BdRPlus p R) (BdR p R)) := IsFractionRing.injective _ _
  obtain ⟨N, hN⟩ := hf.bdd n

  set T := (AcrisZero.toQuot p R n).range
  have key : ∀ k : ℕ, ∃ c : Ainf p R, BdRPlus.eval p R n y - BdRPlus.eval p R n (Acris.toBdRPlus p R x) =
      (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ k *
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) c) := by
    intro k
    obtain ⟨a0, z, hz⟩ := Acris.exists_eq_add (N + n + k) x
    obtain ⟨yz, az, hyz, haz⟩ := hN z
    obtain ⟨bz, hbz⟩ := AcrisZero.exists_p_pow_mul_eq n (Acris.toRange p R n z)
    have hbz' := congrArg Subtype.val hbz
    simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast, RingHom.coe_rangeRestrict] at hbz'
    have hy2 : y = algebraMap (AinfInv p R) (BdRPlus p R) (a0 : AinfInv p R) + (p : BdRPlus p R) ^ (N + n + k) * yz := by
      apply hinj
      rw [← hy, hz]
      simp only [map_add, map_mul, map_pow, map_natCast]
      rw [hf.on0 a0, hyz]
    have hx2 : Acris.toBdRPlus p R x =
        algebraMap (AinfInv p R) (BdRPlus p R) (a0 : AinfInv p R) + (p : BdRPlus p R) ^ (N + n + k) * Acris.toBdRPlus p R z := by
      rw [hz, map_add, map_mul, map_pow, map_natCast, Acris.toBdRPlus_algebraMap_zero]
    refine ⟨(p : Ainf p R) ^ n * az - (p : Ainf p R) ^ N * bz, ?_⟩
    have e1 : BdRPlus.eval p R n ((p : BdRPlus p R) ^ N * yz) =
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) az) := haz
    have e2 : (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n * BdRPlus.eval p R n (Acris.toBdRPlus p R z) =
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) bz) := by
      rw [Acris.eval_toBdRPlus, hbz']
      rfl
    rw [map_mul, map_pow, map_natCast] at e1
    rw [hy2, hx2]
    simp only [map_add, map_mul, map_pow, map_natCast, map_sub]
    rw [add_sub_add_left_eq_sub, ← mul_sub]
    calc (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ (N + n + k) * (BdRPlus.eval p R n yz - BdRPlus.eval p R n (Acris.toBdRPlus p R z))
        = (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ k *
            ((p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n * ((p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ N * BdRPlus.eval p R n yz)
              - (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ N * ((p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n * BdRPlus.eval p R n (Acris.toBdRPlus p R z))) := by
          ring
      _ = _ := by rw [e1, e2]

  have hmem : ∀ c : Ainf p R, Ideal.Quotient.mk (AinfInv.kerTheta p R ^ n) (algebraMap (Ainf p R) (AinfInv p R) c) ∈ T :=
    fun c => ⟨algebraMap (Ainf p R) (AcrisZero p R) c, rfl⟩
  obtain ⟨c0, hc0⟩ := key 0
  rw [pow_zero, one_mul] at hc0
  have hH : IsHausdorff (span {(p : T)}) T := inferInstance
  have h0 : (⟨_, hmem c0⟩ : T) = 0 := by
    apply hH.haus
    intro k
    obtain ⟨c, hc⟩ := key k
    have hx : (⟨_, hmem c0⟩ : T) = ((p : T) ^ k) • (⟨_, hmem c⟩ : T) := by
      apply Subtype.ext
      simp only [smul_eq_mul, Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast]
      rw [← hc0, hc]
    rw [SModEq.zero, hx]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) k) Submodule.mem_top
  have h1 := congrArg Subtype.val h0
  simp only [ZeroMemClass.coe_zero] at h1
  rw [← hc0] at h1
  exact sub_eq_zero.1 h1

theorem eq_toBdR_of_isCrisDRF {f : Bcris p R →+* BdR p R} (hf : IsCrisDRF f) : f = Bcris.toBdR p R := by
  rw [← isCrisDRA_toBdRPlus_iff]
  intro x
  obtain ⟨N0, hN0⟩ := hf.bdd 0
  obtain ⟨y, -, hy, -⟩ := hN0 x
  rw [hy]
  congr 1
  exact BdRPlus.ext_eval fun n => eval_eq_of_isCrisDRF hf x y hy n

theorem isCrisDRF_iff (f : Bcris p R →+* BdR p R) : IsCrisDRF f ↔ f = Bcris.toBdR p R :=
  ⟨eq_toBdR_of_isCrisDRF, fun h => h ▸ isCrisDRF_toBdR⟩

end Formalism.BasicNotions.CmpTie.Incl
end
end

section
noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

theorem incl_native
    (hι : ∀ x : Reformulated.AutPerF.Acris l (Cmp6.OC l),
      Cmp6.cP l (Reformulated.AutPerF.Acris.toBdRPlus l (Cmp6.OC l) x) = ACris.iota ℂ_[l] l (Cmp6.cA l x))
    (f : Reformulated.AutPerF.Bcris l (Cmp6.OC l) →+* Reformulated.AutPerF.BdR l (Cmp6.OC l)) :
    IsCrisDRF f ↔ Formalism.Per6.IsCrisDR l (((Cmp6.cD l).toRingHom.comp f).comp (Cmp6.cBc l).symm.toRingHom) := by
  rw [isCrisDRF_iff, ← isCrisDRA_toBdRPlus_iff]
  exact isCrisDRA_iff (Cmp6.cA l) (Cmp6.cBc l) (Cmp6.cP l) (Cmp6.cD l) (Reformulated.AutPerF.Acris.toBdRPlus l (Cmp6.OC l))
    (fun x => Cmp6.cBc_algebraMap l x) (fun y => Cmp6.cD_algebraMap l y) hι f

end Formalism.BasicNotions.CmpTie.Incl
end
end

section
noncomputable section
namespace Formalism.BasicNotions.CmpTie.Incl
open GroundTheory.PAdicHodge
variable (l : ℕ) [Fact l.Prime]
set_option maxHeartbeats 200000 in
theorem zt1 (y : Reformulated.AutPerF.AcrisZero l (NC l)) :
    ((Cmp6.zeroEquiv l y : ACris.ACrisZero ℂ_[l] l) : Localization.Away ((l : ℕ) : AInf ℂ_[l] l)) =
      ((y : Reformulated.AutPerF.AcrisZero l (NC l)) : Reformulated.AutPerF.AinfInv l (NC l)) := by
  simp only [Cmp6.zeroEquiv, AlgEquiv.coe_ringEquiv, Subalgebra.equivOfEq_apply]
end Formalism.BasicNotions.CmpTie.Incl
end
end

section
noncomputable section
namespace Formalism.BasicNotions.CmpTie.Incl
open GroundTheory.PAdicHodge
variable (l : ℕ) [Fact l.Prime]
set_option maxHeartbeats 200000 in
theorem zt2 (z : Reformulated.AutPerF.AinfInv l (NC l)) :
    toBDeRhamPlus (↥(normInteger ℂ_[l])) l z = algebraMap (Reformulated.AutPerF.AinfInv l (NC l)) (Reformulated.AutPerF.BdRPlus l (NC l)) z := rfl
end Formalism.BasicNotions.CmpTie.Incl
end
end

section
noncomputable section
namespace Formalism.BasicNotions.CmpTie.Incl
open GroundTheory.PAdicHodge
variable (l : ℕ) [Fact l.Prime]
set_option maxHeartbeats 200000 in
theorem zt3 (a : Reformulated.AutPerF.AcrisZero l (Cmp6.OC l)) :
    ((Reformulated.AutPerF.AcrisZero.map l (Cmp6.e l).toRingHom a : Reformulated.AutPerF.AcrisZero l (NC l)) : Reformulated.AutPerF.AinfInv l (NC l)) =
      Reformulated.AutPerF.AinfInv.map l (Cmp6.e l).toRingHom (a : Reformulated.AutPerF.AinfInv l (Cmp6.OC l)) :=
  Reformulated.AutPerF.AcrisZero.coe_map _ _
end Formalism.BasicNotions.CmpTie.Incl
end
end

section
noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

set_option maxHeartbeats 200000 in
theorem jOC_zero (a : Reformulated.AutPerF.AcrisZero l (Cmp6.OC l)) :
    jOC l (algebraMap _ (Reformulated.AutPerF.Acris l (Cmp6.OC l)) a) =
      algebraMap (Reformulated.AutPerF.AinfInv l (Cmp6.OC l)) _ (a : Reformulated.AutPerF.AinfInv l (Cmp6.OC l)) := by
  show (Cmp6.cP l).symm (iotaP l (Cmp6.cA l (algebraMap _ _ a))) = _
  rw [RingEquiv.symm_apply_eq, Cmp6.cA_apply, Reformulated.AutPerF.Acris.map_algebraMap_zero, Cmp6.acrisNHom_algebraMap]
  erw [ACris.iota_of]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  erw [zt1, zt2, zt3]

end Formalism.BasicNotions.CmpTie.Incl
end
end

section
noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

theorem jOC_bounded (n : ℕ) : ∃ N : ℕ, ∀ x : Reformulated.AutPerF.Acris l (Cmp6.OC l), ∃ a : Reformulated.AutPerF.Ainf l (Cmp6.OC l),
    Reformulated.AutPerF.BdRPlus.eval l (Cmp6.OC l) n (((l : ℕ) : Reformulated.AutPerF.BdRPlus l (Cmp6.OC l)) ^ N * jOC l x) =
      Ideal.Quotient.mk _ (algebraMap (Reformulated.AutPerF.Ainf l (Cmp6.OC l)) (Reformulated.AutPerF.AinfInv l (Cmp6.OC l)) a) := by
  obtain ⟨N, hN⟩ := iota_bounded l n
  refine ⟨N, fun x => ?_⟩
  obtain ⟨a, ha⟩ := hN (Cmp6.cA l x)
  refine ⟨Reformulated.AutPerF.Ainf.map l (Cmp6.e l).symm.toRingHom a, ?_⟩
  have hsymm : ∀ z : Formalism.Per6.BdRp l,
      (Cmp6.cP l).symm z = Reformulated.AutPerF.BdRPlus.map l (Cmp6.e l).symm.toRingHom z := by
    intro z
    rw [RingEquiv.symm_apply_eq]
    show z = Reformulated.AutPerF.BdRPlus.map l (Cmp6.e l).toRingHom
      (Reformulated.AutPerF.BdRPlus.map l (Cmp6.e l).symm.toRingHom z)
    erw [Reformulated.AutPerF.BdRPlus.map_map, RingEquiv.toRingHom_comp_symm_toRingHom, Reformulated.AutPerF.BdRPlus.map_id]
  show Reformulated.AutPerF.BdRPlus.eval l (Cmp6.OC l) n
      (((l : ℕ) : Reformulated.AutPerF.BdRPlus l (Cmp6.OC l)) ^ N * (Cmp6.cP l).symm (iotaP l (Cmp6.cA l x))) = _
  erw [hsymm]
  rw [← map_natCast (Reformulated.AutPerF.BdRPlus.map l (Cmp6.e l).symm.toRingHom) l, ← map_pow]
  have hm := map_mul (Reformulated.AutPerF.BdRPlus.map l (Cmp6.e l).symm.toRingHom)
    (((l : ℕ) : Reformulated.AutPerF.BdRPlus l (NC l)) ^ N) (iotaF l (Cmp6.cA l x))
  erw [← hm, Reformulated.AutPerF.BdRPlus.eval_map]
  erw [ha]
  rw [Ideal.quotientMap_mk, Reformulated.AutPerF.AinfInv.map_algebraMap]

end Formalism.BasicNotions.CmpTie.Incl
end
end

section
noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

theorem comparison_toBdRPlus (x : Reformulated.AutPerF.Acris l (Cmp6.OC l)) :
    Cmp6.cP l (Reformulated.AutPerF.Acris.toBdRPlus l (Cmp6.OC l) x) = ACris.iota ℂ_[l] l (Cmp6.cA l x) := by
  have h := eq_toBdRPlus_of_bounded (jOC l) (jOC_zero l) (jOC_bounded l)
  rw [← h]
  show Cmp6.cP l ((Cmp6.cP l).symm (iotaP l (Cmp6.cA l x))) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

end Formalism.BasicNotions.CmpTie.Incl
end
end

section
noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

variable (l : ℕ) [Fact l.Prime]

theorem incl_F (f : Reformulated.AutPerF.Bcris l (Cmp6.OC l) →+* Reformulated.AutPerF.BdR l (Cmp6.OC l)) :
    IsCrisDRF f ↔ Formalism.Per6.IsCrisDR l (((Cmp6.cD l).toRingHom.comp f).comp (Cmp6.cBc l).symm.toRingHom) :=
  incl_native l (comparison_toBdRPlus l) f

end Formalism.BasicNotions.CmpTie.Incl
end
end

section
noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

def castCrystalline (l : ℕ) [Fact l.Prime] : Per.Bcris l ≃+* Reformulated.AutPerF.Bcris l (Cmp6.OC l) := RingEquiv.refl _
def castDeRham (l : ℕ) [Fact l.Prime] : Per.BdR l ≃+* Reformulated.AutPerF.BdR l (Cmp6.OC l) := RingEquiv.refl _
def castDeRhamPlus (l : ℕ) [Fact l.Prime] : Per.BdRp l ≃+* Reformulated.AutPerF.BdRPlus l (Cmp6.OC l) := RingEquiv.refl _

abbrev equivCrystalline (l : ℕ) [Fact l.Prime] : Per.Bcris l ≃+* Per6.Bcris l := (castCrystalline l).trans (Cmp6.cBc l)
abbrev equivDeRham (l : ℕ) [Fact l.Prime] : Per.BdR l ≃+* Per6.BdR l := (castDeRham l).trans (Cmp6.cD l)
abbrev equivDeRhamPlus (l : ℕ) [Fact l.Prime] : Per.BdRp l ≃+* Per6.BdRp l := (castDeRhamPlus l).trans (Cmp6.cP l)

end Formalism.BasicNotions.CmpTie
end
end
