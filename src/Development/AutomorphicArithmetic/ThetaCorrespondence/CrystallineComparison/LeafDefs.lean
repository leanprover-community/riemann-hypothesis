import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.Assembly
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Comparison
import GroundTheory.PAdicHodge.ACrisBdRGalois

section
noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

abbrev NC : Type := ↥(normInteger ℂ_[l])

def iotaF : ACris.ACris ℂ_[l] l →+* Reformulated.AutPerF.BdRPlus l (NC l) := ACris.iota ℂ_[l] l

theorem iota_bounded (n : ℕ) : ∃ N : ℕ, ∀ x : ACris.ACris ℂ_[l] l, ∃ a : Reformulated.AutPerF.Ainf l (NC l),
    Reformulated.AutPerF.BdRPlus.eval l (NC l) n (((l : ℕ) : Reformulated.AutPerF.BdRPlus l (NC l)) ^ N * iotaF l x) =
      Ideal.Quotient.mk _ (algebraMap (Reformulated.AutPerF.Ainf l (NC l)) (Reformulated.AutPerF.AinfInv l (NC l)) a) := by
  refine ⟨(n - 1).factorial.factorization l, fun x => ?_⟩
  obtain ⟨w, hw⟩ := ACris.pow_mul_mem_latticeQ n _ (ACris.embedding₂ ℂ_[l] l n x).2
  refine ⟨w, ?_⟩
  have h1 : Reformulated.AutPerF.BdRPlus.eval l (NC l) n (iotaF l x) =
      ((ACris.embedding₂ ℂ_[l] l n x : ACris.acrisQ ℂ_[l] l n) : Localization.Away ((l : ℕ) : AInf ℂ_[l] l) ⧸ ACris.kerAway ℂ_[l] l ^ n) := by
    have := ACris.evalₐ_iota (K := ℂ_[l]) (p := l) n x
    rw [ACris.iotaQ.eq_1] at this
    exact this
  rw [map_mul, map_pow, map_natCast, h1]
  exact hw.symm

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

theorem eq_toBdRPlus_of_bounded (j : Acris p R →+* BdRPlus p R)
    (h0 : ∀ a : AcrisZero p R, j (algebraMap (AcrisZero p R) (Acris p R) a) =
      algebraMap (AinfInv p R) (BdRPlus p R) (a : AinfInv p R))
    (hb : ∀ n : ℕ, ∃ N : ℕ, ∀ x : Acris p R, ∃ a : Ainf p R,
      BdRPlus.eval p R n ((p : BdRPlus p R) ^ N * j x) = Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) a)) :
    j = Acris.toBdRPlus p R := by
  ext x
  apply BdRPlus.ext_eval
  intro n
  obtain ⟨N, hN⟩ := hb n
  set T := (AcrisZero.toQuot p R n).range
  have key : ∀ k : ℕ, ∃ c : Ainf p R, BdRPlus.eval p R n (j x) - BdRPlus.eval p R n (Acris.toBdRPlus p R x) =
      (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ k *
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) c) := by
    intro k
    obtain ⟨a0, z, hz⟩ := Acris.exists_eq_add (N + n + k) x
    obtain ⟨az, haz⟩ := hN z
    obtain ⟨bz, hbz⟩ := AcrisZero.exists_p_pow_mul_eq n (Acris.toRange p R n z)
    have hbz' := congrArg Subtype.val hbz
    simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast, RingHom.coe_rangeRestrict] at hbz'
    have hy2 : j x = algebraMap (AinfInv p R) (BdRPlus p R) (a0 : AinfInv p R) + (p : BdRPlus p R) ^ (N + n + k) * j z := by
      rw [hz, map_add, map_mul, map_pow, map_natCast, h0 a0]
    have hx2 : Acris.toBdRPlus p R x =
        algebraMap (AinfInv p R) (BdRPlus p R) (a0 : AinfInv p R) + (p : BdRPlus p R) ^ (N + n + k) * Acris.toBdRPlus p R z := by
      rw [hz, map_add, map_mul, map_pow, map_natCast, Acris.toBdRPlus_algebraMap_zero]
    refine ⟨(p : Ainf p R) ^ n * az - (p : Ainf p R) ^ N * bz, ?_⟩
    have e1 : BdRPlus.eval p R n ((p : BdRPlus p R) ^ N * j z) =
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) az) := haz
    have e2 : (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n * BdRPlus.eval p R n (Acris.toBdRPlus p R z) =
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) bz) := by
      rw [Acris.eval_toBdRPlus, hbz']
      rfl
    rw [map_mul, map_pow, map_natCast] at e1
    rw [hy2, hx2]
    simp only [map_add, map_mul, map_pow, map_natCast, map_sub]
    rw [add_sub_add_left_eq_sub, ← mul_sub]
    calc (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ (N + n + k) * (BdRPlus.eval p R n (j z) - BdRPlus.eval p R n (Acris.toBdRPlus p R z))
        = (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ k *
            ((p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n * ((p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ N * BdRPlus.eval p R n (j z))
              - (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ N * ((p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n * BdRPlus.eval p R n (Acris.toBdRPlus p R z))) := by
          ring
      _ = _ := by rw [e1, e2]
  have hmem : ∀ c : Ainf p R, Ideal.Quotient.mk (AinfInv.kerTheta p R ^ n) (algebraMap (Ainf p R) (AinfInv p R) c) ∈ T :=
    fun c => ⟨algebraMap (Ainf p R) (AcrisZero p R) c, rfl⟩
  obtain ⟨c0, hc0⟩ := key 0
  rw [pow_zero, one_mul] at hc0
  have hH : IsHausdorff (span {(p : T)}) T := inferInstance
  have h0' : (⟨_, hmem c0⟩ : T) = 0 := by
    apply hH.haus
    intro k
    obtain ⟨c, hc⟩ := key k
    have hx : (⟨_, hmem c0⟩ : T) = ((p : T) ^ k) • (⟨_, hmem c⟩ : T) := by
      apply Subtype.ext
      simp only [smul_eq_mul, Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast]
      rw [← hc0, hc]
    rw [SModEq.zero, hx]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) k) Submodule.mem_top
  have h1 := congrArg Subtype.val h0'
  simp only [ZeroMemClass.coe_zero] at h1
  rw [← hc0] at h1
  exact sub_eq_zero.1 h1

end Formalism.BasicNotions.CmpTie.Incl
end
end

section
noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

def iotaP : ACris.ACris ℂ_[l] l →+* Formalism.Per6.BdRp l := ACris.iota ℂ_[l] l

def jOC : Reformulated.AutPerF.Acris l (Cmp6.OC l) →+* Reformulated.AutPerF.BdRPlus l (Cmp6.OC l) :=
  ((Cmp6.cP l).symm.toRingHom.comp (iotaP l)).comp (Cmp6.cA l).toRingHom

end Formalism.BasicNotions.CmpTie.Incl
end
end
