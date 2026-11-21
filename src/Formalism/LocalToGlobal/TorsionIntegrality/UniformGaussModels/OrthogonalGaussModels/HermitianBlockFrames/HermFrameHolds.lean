import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.Assembly
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.AreaCmLNe
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.FrobStep
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.IsUnitaryK
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.InsSuccAbove
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.MkLeOfDenseRange

section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

theorem delta_mem (l : ℕ) [Fact l.Prime] (dK : ℕ) (hd : dK.Prime) (hd4 : dK % 4 = 3) (hld : ¬ l ∣ dK)
    (ι : ℂ ≃+* ℂ_[l]) : ι (sq dK) ∈ MaximalUnramifiedExtension l := by
  haveI : Fact dK.Prime := ⟨hd⟩
  have hd2 : ringChar (ZMod dK) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hζ : IsPrimitiveRoot (ι (Complex.exp (2 * ↑Real.pi * Complex.I / ↑dK))) dK :=
    (Complex.isPrimitiveRoot_exp dK hd.ne_zero).map_of_injective ι.injective
  set χ := (quadraticChar (ZMod dK)).ringHomComp (Int.castRingHom ℂ_[l]) with hχ
  set ψ := AddChar.zmodChar dK hζ.pow_eq_one with hψdef
  have hψ : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root dK hζ
  have hχ1 : χ ≠ 1 := by
    obtain ⟨a, ha⟩ := MulChar.ne_one_iff.1 (quadraticChar_ne_one hd2)
    refine MulChar.ne_one_iff.2 ⟨a, fun h => ha ?_⟩
    rw [hχ, MulChar.ringHomComp_apply, eq_intCast] at h
    exact_mod_cast h
  have hG : gaussSum χ ψ ^ 2 = -(dK : ℂ_[l]) := by
    rw [gaussSum_sq hχ1 ((quadraticChar_isQuadratic (ZMod dK)).comp _) hψ, ZMod.card, hχ,
      MulChar.ringHomComp_apply, quadraticChar_neg_one hd2, ZMod.card, ZMod.χ₄_nat_three_mod_four hd4]
    simp
  have hx : ι (sq dK) ^ 2 = -(dK : ℂ_[l]) := by
    rw [← map_pow]
    have h2 : sq dK ^ 2 = -(dK : ℂ) := by
      unfold sq
      rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      push_cast
      ring
    rw [h2, map_neg, map_natCast]
  have hmem : gaussSum χ ψ ∈ MaximalUnramifiedExtension l := by
    unfold gaussSum
    refine Subfield.sum_mem _ (fun a _ => Subfield.mul_mem _ ?_ ?_)
    · rw [hχ, MulChar.ringHomComp_apply, eq_intCast]
      exact intCast_mem _ _
    · rw [hψdef, AddChar.zmodChar_apply]
      unfold MaximalUnramifiedExtension
      apply Subfield.le_topologicalClosure
      apply Subfield.subset_closure
      refine ⟨dK, hd.pos, hld, ?_⟩
      rw [← pow_mul, mul_comm a.val dK, pow_mul, hζ.pow_eq_one, one_pow]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hx.trans hG.symm) with h | h
  · rw [h]
    exact hmem
  · rw [h]
    exact Subfield.neg_mem _ hmem

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
end
end

section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

theorem norm_int_Kur (l : ℕ) [Fact l.Prime] (z : ℤ) (hz : ¬ (l : ℤ) ∣ z) : ‖((z : ℤ) : MaximalUnramifiedExtension l)‖ = 1 := by
  have h2 : ‖(z : ℚ_[l])‖ = 1 := by
    have h5 : ‖(z : ℤ_[l])‖ = 1 := le_antisymm (PadicInt.norm_le_one _)
      (not_lt.mp ((PadicInt.norm_int_lt_one_iff_dvd z).not.mpr hz))
    simpa using h5
  have h3 : ‖((z : ℚ_[l]) : PadicAlgCl l)‖ = 1 := by rw [PadicAlgCl.norm_extends]; exact h2
  have h4 : ‖(((z : ℚ_[l]) : PadicAlgCl l) : ℂ_[l])‖ = 1 := by rw [PadicComplex.norm_extends]; exact h3
  have e1 : (((z : ℚ_[l]) : PadicAlgCl l)) = (z : PadicAlgCl l) := map_intCast _ z
  have e2 : (((z : PadicAlgCl l)) : ℂ_[l]) = (z : ℂ_[l]) := by
    exact map_intCast (UniformSpace.Completion.coeRingHom (α := PadicAlgCl l)) z
  have e3 : ((z : Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) : ℂ_[l]) = (z : ℂ_[l]) := by simp
  show ‖((z : Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) : ℂ_[l])‖ = 1
  rw [e3, ← e2, ← e1]; exact h4

private theorem norm_add_le_max_maxUnramified_lemma (l : ℕ) [Fact l.Prime] (a b : Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) :
    ‖a + b‖ ≤ max ‖a‖ ‖b‖ :=
  IsUltrametricDist.norm_add_le_max (a : ℂ_[l]) (b : ℂ_[l])

private theorem inv_prime_lt_one_lemma_2 (l : ℕ) (hl : 1 < l) : (l : ℝ)⁻¹ < 1 := by
  have hpos : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have h1 : (l : ℝ)⁻¹ * l = 1 := inv_mul_cancel₀ hpos.ne'
  have h2 : (1 : ℝ) < l := by exact_mod_cast hl
  nlinarith [inv_pos.2 hpos]

private theorem norm_frobenius_of_norm_eq_one_lemma_3 (l : ℕ) [Fact l.Prime]
    (σ : Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l →+* Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) (hU : Formalism.L2.Th1.Top.FrP.UnrOK (Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) l σ)
    (u : Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) (hu : ‖u‖ = 1) : ‖σ u‖ = 1 := by
  have hl2 : 2 < l := hU.2.1
  have hinv : (l : ℝ)⁻¹ < 1 := inv_prime_lt_one_lemma_2 l (by omega)
  have hc := hU.2.2.2.2 u hu.le
  have hul : ‖u ^ l‖ = 1 := by rw [norm_pow, hu, one_pow]
  apply le_antisymm
  · have h := norm_add_le_max_maxUnramified_lemma l (σ u - u ^ l) (u ^ l)
    rw [sub_add_cancel, hul] at h
    exact h.trans (max_le (hc.trans hinv.le) le_rfl)
  · have h := norm_add_le_max_maxUnramified_lemma l (σ u) (-(σ u - u ^ l))
    have e : σ u + -(σ u - u ^ l) = u ^ l := by ring
    rw [e, hul, norm_neg] at h
    by_contra hlt
    have := max_lt (not_le.mp hlt) (hc.trans_lt hinv)
    linarith

private theorem norm_frobenius_eq_lemma_4 (l : ℕ) [Fact l.Prime] (σ : Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l →+* Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l)
    (hU : Formalism.L2.Th1.Top.FrP.UnrOK (Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) l σ) (x : Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) : ‖σ x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨k, hk⟩ := hU.2.2.2.1 x hx
  have hl2 : 2 < l := hU.2.1
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have hkpos : (0 : ℝ) < (l : ℝ) ^ k := zpow_pos hlpos k
  have hcn : ‖((l : Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) ^ k)‖ = ((l : ℝ) ^ k)⁻¹ := by
    rw [norm_zpow, hU.2.2.1, inv_zpow]
  have hσc : σ ((l : Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) ^ k) = (l : Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) ^ k := by
    rw [map_zpow₀, map_natCast]
  have hu : ‖x * (l : Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) ^ k‖ = 1 := by
    rw [norm_mul, hk, hcn, mul_inv_cancel₀ hkpos.ne']
  have h := norm_frobenius_of_norm_eq_one_lemma_3 l σ hU _ hu
  rw [map_mul, hσc, norm_mul, hcn] at h
  rw [hk]
  exact mul_right_cancel₀ (inv_ne_zero hkpos.ne') (h.trans (mul_inv_cancel₀ hkpos.ne').symm)

theorem frob_isom (l : ℕ) [Fact l.Prime] (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hU : UnrOK (MaximalUnramifiedExtension l) l σ) (x : MaximalUnramifiedExtension l) :
    ‖σ x‖ = ‖x‖ :=
  norm_frobenius_eq_lemma_4 l σ hU x

theorem frob_conj (l : ℕ) [Fact l.Prime] (dK : ℕ) (hl5 : 5 ≤ l) (hld : ¬ l ∣ dK)
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hU : UnrOK (MaximalUnramifiedExtension l) l σ)
    (δ : MaximalUnramifiedExtension l) (hδ2 : δ ^ 2 = -(dK : MaximalUnramifiedExtension l)) : σ δ = -δ := by

  have hdvd : ¬ (l : ℤ) ∣ (-(dK : ℤ)) := by
    rw [dvd_neg]; exact_mod_cast hld
  have hcast : (((-(dK : ℤ)) : ℤ) : MaximalUnramifiedExtension l) = -(dK : MaximalUnramifiedExtension l) := by push_cast; ring
  have hδn : ‖δ‖ = 1 := by
    have h : ‖δ‖ ^ 2 = 1 := by rw [← norm_pow, hδ2, ← hcast, norm_int_Kur l _ hdvd]
    have h0 : 0 ≤ ‖δ‖ := norm_nonneg _
    nlinarith [h]
  obtain ⟨a, ha⟩ : ∃ a : ZMod l, a = (((-(dK : ℤ)) : ℤ) : ZMod l) := ⟨_, rfl⟩
  have ha' : a = -(dK : ZMod l) := by rw [ha]; push_cast; ring
  have ha0 : a ≠ 0 := by
    rw [ha]; intro h; exact hdvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ l).mp h)
  have hsq : ¬ IsSquare a := by
    rintro ⟨b, hb⟩
    exact hin ⟨b, by rw [pow_two, ← hb, ha']⟩
  have hpow : a ^ (l / 2) = -1 := by
    rcases ZMod.pow_div_two_eq_neg_one_or_one l ha0 with h | h
    · exact absurd ((ZMod.euler_criterion l ha0).mpr h) hsq
    · exact h
  have hpow' : (-(dK : ZMod l)) ^ (l / 2) = -1 := by rw [← ha']; exact hpow
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = 1 - (-(dK : ℤ)) ^ (l / 2) := ⟨_, rfl⟩
  have hcnd : ¬ (l : ℤ) ∣ c := by
    intro hdc
    have h0 : ((c : ℤ) : ZMod l) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd c l).mpr hdc
    have h2 : ((c : ℤ) : ZMod l) = ((2 : ℤ) : ZMod l) := by
      rw [hc]; push_cast; rw [hpow']; ring
    rw [h2] at h0
    have := Int.le_of_dvd two_pos ((ZMod.intCast_zmod_eq_zero_iff_dvd 2 l).mp h0)
    omega
  have hodd : l = 2 * (l / 2) + 1 := by
    obtain ⟨k, hk⟩ := (Fact.out : l.Prime).odd_of_ne_two (by omega)
    omega
  have hpowl : δ ^ l = δ * (((-(dK : ℤ)) ^ (l / 2) : ℤ) : MaximalUnramifiedExtension l) := by
    have e : δ ^ l = δ ^ (2 * (l / 2) + 1) := by rw [← hodd]
    rw [e, pow_succ, pow_mul, hδ2]; push_cast; ring
  have hsq2 : (σ δ - δ) * (σ δ + δ) = 0 := by
    have h : σ δ ^ 2 = δ ^ 2 := by rw [← map_pow, hδ2, map_neg, map_natCast]
    linear_combination h
  rcases mul_eq_zero.mp hsq2 with h | h
  · exfalso
    have hσ : σ δ = δ := sub_eq_zero.mp h
    have hb := hU.2.2.2.2 δ hδn.le
    rw [hσ, hpowl] at hb
    have e : δ - δ * (((-(dK : ℤ)) ^ (l / 2) : ℤ) : MaximalUnramifiedExtension l) = δ * ((c : ℤ) : MaximalUnramifiedExtension l) := by
      rw [hc]; push_cast; ring
    rw [e, norm_mul, hδn, norm_int_Kur l c hcnd, one_mul] at hb
    have hinv : (l : ℝ)⁻¹ < 1 := inv_prime_lt_one_lemma_2 l (by omega)
    linarith
  · exact eq_neg_of_add_eq_zero_left h

theorem frobStep : FrobStep := by
  intro l hl dK hl5 hld hd hd8 hin ι σ hU
  refine ⟨frob_isom l σ hU, ?_⟩
  have hmem := delta_mem l dK hd (by omega) hld ι
  refine ⟨⟨ι (sq dK), hmem⟩, rfl, ?_⟩
  apply frob_conj l dK hl5 hld hin σ hU
  have hsqc : (ι (sq dK)) ^ 2 = -(dK : ℂ_[l]) := by
    rw [← map_pow, sq_sq, map_neg, map_natCast]
  apply Subtype.ext
  simpa using hsqc

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
end
end

section
namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame

theorem hermFrame_of_locCore (hL : LocCore) : Formalism.L2.Th1.Top.FrP.HermFrame := hermFrame_of frobStep ratStep hL

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
end

section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
open Formalism.L2.Th1.Top.FrP

variable (l : ℕ) [Fact l.Prime]

private theorem norm_alg_lemma (x : ℚ_[l]) : ‖algebraMap ℚ_[l] ℂ_[l] x‖ = ‖x‖ := by
  first
  | exact norm_algebraMap' ℂ_[l] x
  | (rw [← PadicAlgCl.norm_extends l x, ← PadicComplex.norm_extends l]; rfl)
  | (rw [IsScalarTower.algebraMap_apply ℚ_[l] (PadicAlgCl l) ℂ_[l], ← PadicAlgCl.norm_extends l x,
        ← PadicComplex.norm_extends l]; rfl)

private theorem cont_alg_lemma_2 : Continuous (algebraMap ℚ_[l] ℂ_[l]) :=
  (AddMonoidHomClass.isometry_of_norm (algebraMap ℚ_[l] ℂ_[l]) (norm_alg_lemma l)).continuous

private theorem closed_rat_lemma_3 (S : Set ℚ_[l]) (hS : IsClosed S) (hq : ∀ r : ℚ, (r : ℚ_[l]) ∈ S)
    (x : ℚ_[l]) : x ∈ S := by
  rw [← hS.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨r, hr⟩ := Padic.rat_dense l x hε
  exact ⟨r, hq r, by rw [dist_eq_norm]; exact hr⟩

theorem algebraMap_mem_Kur (x : ℚ_[l]) : algebraMap ℚ_[l] ℂ_[l] x ∈ MaximalUnramifiedExtension l := by
  have hK : IsClosed (MaximalUnramifiedExtension l : Set ℂ_[l]) := by
    first
    | exact Subfield.isClosed_topologicalClosure _
    | exact isClosed_closure
  refine closed_rat_lemma_3 l {y | algebraMap ℚ_[l] ℂ_[l] y ∈ MaximalUnramifiedExtension l} (hK.preimage (cont_alg_lemma_2 l)) ?_ x
  intro r
  show algebraMap ℚ_[l] ℂ_[l] (r : ℚ_[l]) ∈ MaximalUnramifiedExtension l
  rw [map_ratCast]
  first
  | exact SubfieldClass.ratCast_mem (MaximalUnramifiedExtension l) r
  | exact (MaximalUnramifiedExtension l).ratCast_mem r

def φ : ℚ_[l] →+* MaximalUnramifiedExtension l := (algebraMap ℚ_[l] ℂ_[l]).codRestrict (MaximalUnramifiedExtension l) (algebraMap_mem_Kur l)

def ψ : ℤ_[l] →+* MaximalUnramifiedExtension l := (φ l).comp PadicInt.Coe.ringHom

theorem norm_φ (x : ℚ_[l]) : ‖φ l x‖ = ‖x‖ := by
  exact norm_alg_lemma l x

theorem norm_ψ (x : ℤ_[l]) : ‖ψ l x‖ = ‖x‖ := by
  exact norm_φ l (x : ℚ_[l])

theorem norm_ψ_le (x : ℤ_[l]) : ‖ψ l x‖ ≤ 1 := by
  rw [norm_ψ]
  exact x.norm_le_one

theorem continuous_φ : Continuous (φ l) := by
  exact (AddMonoidHomClass.isometry_of_norm (φ l) (norm_φ l)).continuous

theorem σ_φ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hσ : ∀ x, ‖σ x‖ = ‖x‖) (x : ℚ_[l]) : σ (φ l x) = φ l x := by
  have hσc : Continuous σ := (AddMonoidHomClass.isometry_of_norm σ hσ).continuous
  refine closed_rat_lemma_3 l {y | σ (φ l y) = φ l y}
    (isClosed_eq (hσc.comp (continuous_φ l)) (continuous_φ l)) ?_ x
  intro r
  show σ (φ l (r : ℚ_[l])) = φ l (r : ℚ_[l])
  rw [map_ratCast, map_ratCast]

theorem σ_ψ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hσ : ∀ x, ‖σ x‖ = ‖x‖) (x : ℤ_[l]) : σ (ψ l x) = ψ l x := by
  exact σ_φ l σ hσ (x : ℚ_[l])

theorem norm_natCast_Kur (k : ℕ) : ‖(k : MaximalUnramifiedExtension l)‖ = ‖(k : ℚ_[l])‖ := by
  rw [← map_natCast (φ l) k, norm_φ]

theorem norm_l_Kur : ‖(l : MaximalUnramifiedExtension l)‖ = (l : ℝ)⁻¹ := by
  rw [norm_natCast_Kur, Padic.norm_p]

theorem toZMod_eq_zero_iff (z : ℤ_[l]) : PadicInt.toZMod z = 0 ↔ ‖z‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
  first
  | rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
  | rw [LocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

theorem norm_eq_one_iff (z : ℤ_[l]) : ‖z‖ = 1 ↔ PadicInt.toZMod z ≠ 0 := by
  rw [Ne, toZMod_eq_zero_iff]
  constructor
  · intro h h'
    rw [h] at h'
    exact lt_irrefl _ h'
  · intro h
    exact le_antisymm z.norm_le_one (not_lt.1 h)

theorem toZMod_natCast (k : ℕ) : PadicInt.toZMod (k : ℤ_[l]) = (k : ZMod l) := by
  exact map_natCast PadicInt.toZMod k

theorem odd_l (h5 : 5 ≤ l) : (2 : ZMod l) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod l) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (ZMod l) l] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem exists_sqrt (h5 : 5 ≤ l) (t : ℤ_[l]) (s : ZMod l) (hs : s ≠ 0) (ht : PadicInt.toZMod t = s ^ 2) :
    ∃ z : ℤ_[l], z * z = t := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨a, ha⟩ : ∃ a : ℤ_[l], PadicInt.toZMod a = s :=
    ⟨(s.val : ℤ_[l]), by rw [toZMod_natCast, ZMod.natCast_zmod_val]⟩
  set F : Polynomial ℤ_[l] := Polynomial.X ^ 2 - Polynomial.C t with hF
  have h1 : Polynomial.aeval a F = a ^ 2 - t := by simp [hF]
  have h2 : Polynomial.aeval a (Polynomial.derivative F) = 2 * a := by
    first
    | (norm_num [hF]; done)
    | (simp [hF]; left; norm_num; done)
    | (simp [hF]; left; rfl)
    | (simp only [hF, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
        sub_zero, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, Polynomial.aeval_X, map_natCast]; norm_num)
  have n1 : ‖a ^ 2 - t‖ < 1 := by
    rw [← toZMod_eq_zero_iff l, map_sub, map_pow, ha, ht, sub_self]
  have n2 : ‖(2 : ℤ_[l]) * a‖ = 1 := by
    rw [norm_eq_one_iff l, map_mul, map_ofNat, ha]
    exact mul_ne_zero (odd_l l h5) hs
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := a) (by rw [h1, h2, n2, one_pow]; exact n1)
  have hz2 : z ^ 2 = t := by
    have : z ^ 2 - t = 0 := by simpa [hF] using hz
    exact sub_eq_zero.1 this
  exact ⟨z, by rw [← sq]; exact hz2⟩

theorem exists_norm (h5 : 5 ≤ l) (dK : ℕ) (hld : ¬ l ∣ dK) (a : ℤ_[l]) (ha : ‖a‖ = 1) :
    ∃ x y : ℤ_[l], x * x + dK * (y * y) = a := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hd : ((dK : ℕ) : ZMod l) ≠ 0 := by
    rwa [Ne, CharP.cast_eq_zero_iff (ZMod l) l]
  have hA : PadicInt.toZMod a ≠ 0 := (norm_eq_one_iff l a).1 ha
  obtain ⟨x0, y0, hxy⟩ : ∃ x0 y0 : ZMod l, x0 ^ 2 + (dK : ZMod l) * y0 ^ 2 = PadicInt.toZMod a := by
    have hR : Fintype.card (ZMod l) % 2 = 1 := by
      rw [ZMod.card]
      exact Nat.odd_iff.1 ((Fact.out : l.Prime).odd_of_ne_two (by omega))
    have h2 : (Polynomial.C (dK : ZMod l) * Polynomial.X ^ 2).degree = 2 :=
      Polynomial.degree_C_mul_X_pow 2 hd
    have hg : (Polynomial.C (dK : ZMod l) * Polynomial.X ^ 2
        - Polynomial.C (PadicInt.toZMod a)).degree = 2 := by
      rw [Polynomial.degree_sub_C (by rw [h2]; first | decide | norm_num | exact WithBot.coe_lt_coe.2 (by norm_num)), h2]
    obtain ⟨x0, y0, h⟩ := FiniteField.exists_root_sum_quadratic (f := Polynomial.X ^ 2)
      (g := Polynomial.C (dK : ZMod l) * Polynomial.X ^ 2 - Polynomial.C (PadicInt.toZMod a))
      (Polynomial.degree_X_pow 2) hg hR
    refine ⟨x0, y0, ?_⟩
    simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C] at h
    linear_combination h
  by_cases hx0 : x0 = 0
  · subst hx0
    have hy0 : y0 ≠ 0 := by
      rintro rfl
      apply hA
      rw [← hxy]
      simp

    obtain ⟨w, hw⟩ := exists_sqrt l h5 ((dK : ℤ_[l]) * a) ((dK : ZMod l) * y0) (mul_ne_zero hd hy0)
      (by
        rw [map_mul, toZMod_natCast]
        linear_combination (-(dK : ZMod l)) * hxy)
    have hdu : IsUnit (dK : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, norm_eq_one_iff l, toZMod_natCast]
      exact hd
    obtain ⟨u, hu⟩ := hdu
    have key : (u : ℤ_[l]) * ↑u⁻¹ = 1 := u.mul_inv
    rw [← hu] at hw
    refine ⟨0, ↑u⁻¹ * w, ?_⟩
    rw [← hu]
    linear_combination ((u : ℤ_[l]) * ↑u⁻¹ * ↑u⁻¹) * hw + ((u : ℤ_[l]) * ↑u⁻¹ + 1) * a * key
  ·
    obtain ⟨x, hx⟩ := exists_sqrt l h5 (a - dK * ((y0.val : ℤ_[l]) * (y0.val : ℤ_[l]))) x0 hx0
      (by
        rw [map_sub, map_mul, map_mul, toZMod_natCast, toZMod_natCast, ZMod.natCast_zmod_val]
        linear_combination -hxy)
    exact ⟨x, y0.val, by rw [hx]; ring⟩

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
end
end

section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
open Formalism.L2.Th1.Top.FrP Jac

variable {l : ℕ} [Fact l.Prime]

def OO (dK : ℕ) (δ : MaximalUnramifiedExtension l) (hδ : δ ^ 2 = -(dK : MaximalUnramifiedExtension l)) : Subring (MaximalUnramifiedExtension l) where
  carrier := {x | ∃ a b : ℤ_[l], x = ψ l a + δ * ψ l b}
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
    refine ⟨a * c - dK * (b * e), a * e + b * c, ?_⟩
    simp only [map_add, map_sub, map_mul, map_natCast]
    linear_combination (ψ l b * ψ l e) * hδ
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
    exact ⟨a + c, b + e, by simp only [map_add]; ring⟩
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro _ ⟨a, b, rfl⟩
    exact ⟨-a, -b, by simp only [map_neg]; ring⟩

theorem norm_add_le_Kur (x y : MaximalUnramifiedExtension l) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  show ‖(x : ℂ_[l]) + y‖ ≤ max ‖(x : ℂ_[l])‖ ‖(y : ℂ_[l])‖
  exact IsUltrametricDist.norm_add_le_max _ _

theorem norm_δ_le {dK : ℕ} {δ : MaximalUnramifiedExtension l} (hδ : δ ^ 2 = -(dK : MaximalUnramifiedExtension l)) : ‖δ‖ ≤ 1 := by
  have h : ‖δ‖ ^ 2 ≤ 1 := by
    rw [← norm_pow, hδ, norm_neg, norm_natCast_Kur]
    have : ((dK : ℤ_[l]) : ℚ_[l]) = (dK : ℚ_[l]) := by push_cast; rfl
    rw [← this]; exact PadicInt.norm_le_one _
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

theorem norm_le_one_of_mem {dK : ℕ} {δ : MaximalUnramifiedExtension l} {hδ : δ ^ 2 = -(dK : MaximalUnramifiedExtension l)} {x : MaximalUnramifiedExtension l}
    (hx : x ∈ OO dK δ hδ) : ‖x‖ ≤ 1 := by
  obtain ⟨a, b, rfl⟩ := hx
  refine (norm_add_le_Kur _ _).trans (max_le (norm_ψ_le l a) ?_)
  rw [norm_mul]
  exact mul_le_one₀ (norm_δ_le hδ) (norm_nonneg _) (norm_ψ_le l b)

theorem ratCast_mem {dK : ℕ} {δ : MaximalUnramifiedExtension l} {hδ : δ ^ 2 = -(dK : MaximalUnramifiedExtension l)} (q : ℚ) (hq : padicNorm l q ≤ 1) :
    (q : MaximalUnramifiedExtension l) ∈ OO dK δ hδ := by
  have hq' : ‖(q : ℚ_[l])‖ ≤ 1 := by rw [Padic.eq_padicNorm]; exact_mod_cast hq
  refine ⟨⟨(q : ℚ_[l]), hq'⟩, 0, ?_⟩
  simp only [map_zero, mul_zero, add_zero]
  show (q : MaximalUnramifiedExtension l) = φ l (q : ℚ_[l])
  rw [map_ratCast]

theorem δ_mem {dK : ℕ} {δ : MaximalUnramifiedExtension l} {hδ : δ ^ 2 = -(dK : MaximalUnramifiedExtension l)} : δ ∈ OO dK δ hδ := ⟨0, 1, by simp⟩

theorem norm_sq_unit {dK : ℕ} (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) (a b : ℤ_[l])
    (h : ‖a‖ = 1 ∨ ‖b‖ = 1) : ‖a * a + dK * (b * b)‖ = 1 := by
  rw [norm_eq_one_iff]
  intro h0
  rw [map_add, map_mul, map_mul, map_mul, toZMod_natCast] at h0
  by_cases hB : PadicInt.toZMod b = 0
  · have hA : PadicInt.toZMod a = 0 := by
      rw [hB, mul_zero, mul_zero, add_zero] at h0; exact mul_self_eq_zero.mp h0
    rcases h with h | h
    · exact (norm_eq_one_iff l a).mp h hA
    · exact (norm_eq_one_iff l b).mp h hB
  · exact hin ⟨PadicInt.toZMod a / PadicInt.toZMod b, by field_simp; linear_combination h0⟩

def setup (h5 : 5 ≤ l) (dK : ℕ) (hld : ¬ l ∣ dK) (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l))
    (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hσ : ∀ x, ‖σ x‖ = ‖x‖) (δ : MaximalUnramifiedExtension l) (hδ : δ ^ 2 = -(dK : MaximalUnramifiedExtension l)) (hσδ : σ δ = -δ) :
    JSetup (MaximalUnramifiedExtension l) where
  σ := σ
  O := OO dK δ hδ
  p := (l : MaximalUnramifiedExtension l)
  hp0 := by
    intro h
    have := norm_l_Kur l
    rw [h, norm_zero] at this
    have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    exact (inv_pos.mpr hl).ne this
  hpO := ⟨l, 0, by simp⟩
  hσp := map_natCast σ l
  hσO := by
    rintro _ ⟨a, b, rfl⟩
    exact ⟨a, -b, by rw [map_add, map_mul, σ_ψ l σ hσ, σ_ψ l σ hσ, hσδ, map_neg]; ring⟩
  hσσ := by
    rintro _ ⟨a, b, rfl⟩
    simp only [map_add, map_mul, σ_ψ l σ hσ, hσδ, map_neg, neg_neg]
  hinv := by
    rintro _ ⟨a, b, rfl⟩ hnu
    have hab : ‖a‖ = 1 ∨ ‖b‖ = 1 := by
      by_contra hc
      push Not at hc
      apply hnu
      obtain ⟨a', rfl⟩ := (PadicInt.norm_lt_one_iff_dvd a).mp (lt_of_le_of_ne (PadicInt.norm_le_one a) hc.1)
      obtain ⟨b', rfl⟩ := (PadicInt.norm_lt_one_iff_dvd b).mp (lt_of_le_of_ne (PadicInt.norm_le_one b) hc.2)
      exact ⟨ψ l a' + δ * ψ l b', ⟨a', b', rfl⟩, by simp only [map_mul, map_natCast]; ring⟩
    obtain ⟨u, hu⟩ := PadicInt.isUnit_iff.mpr (norm_sq_unit hin a b hab)
    refine ⟨a * ↑u⁻¹, -(b * ↑u⁻¹), ?_⟩
    have hNu : ψ l (a * a + dK * (b * b)) * ψ l ↑u⁻¹ = 1 := by
      rw [← map_mul, ← hu, Units.mul_inv, map_one]
    have hmul : (ψ l a + δ * ψ l b) * (ψ l (a * ↑u⁻¹) + δ * ψ l (-(b * ↑u⁻¹))) = 1 := by
      simp only [map_mul, map_neg, map_add, map_natCast] at hNu ⊢
      linear_combination hNu + (-(ψ l b * ψ l b * ψ l ↑u⁻¹)) * hδ
    exact inv_eq_of_mul_eq_one_right hmul
  hone := by
    rintro ⟨y, hy, h⟩
    have h1 := congrArg norm h
    rw [norm_one, norm_mul, norm_l_Kur] at h1
    have hy1 := norm_le_one_of_mem hy
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    have : (l : ℝ)⁻¹ * ‖y‖ ≤ (l : ℝ)⁻¹ := mul_le_of_le_one_right (by positivity) hy1
    have : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
    linarith
  htwo := by
    have h2 : ‖(2 : ℤ_[l])‖ = 1 := by
      rw [norm_eq_one_iff, map_ofNat]; exact odd_l l h5
    obtain ⟨u, hu⟩ := PadicInt.isUnit_iff.mpr h2
    refine ⟨↑u⁻¹, 0, ?_⟩
    have : (2 : MaximalUnramifiedExtension l) * ψ l ↑u⁻¹ = 1 := by
      rw [← map_ofNat (ψ l) 2, ← map_mul, ← hu, Units.mul_inv, map_one]
    rw [map_zero, mul_zero, add_zero]
    exact inv_eq_of_mul_eq_one_right this
  h2 := two_ne_zero
  hnorm := by
    rintro _ ⟨a, b, rfl⟩ hσu hnu
    have hδ0 : δ ≠ 0 := by
      intro h0
      rw [h0, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero] at hδ
      exact hld (hδ ▸ dvd_zero l)
    have hb : ψ l b = 0 := by
      rw [map_add, map_mul, σ_ψ l σ hσ, σ_ψ l σ hσ, hσδ] at hσu
      have h2δ : (2 * δ) * ψ l b = 0 := by linear_combination -hσu
      rcases mul_eq_zero.mp h2δ with h | h
      · exact absurd h (mul_ne_zero two_ne_zero hδ0)
      · exact h
    have ha : ‖a‖ = 1 := by
      by_contra hc
      apply hnu
      obtain ⟨a', rfl⟩ := (PadicInt.norm_lt_one_iff_dvd a).mp (lt_of_le_of_ne (PadicInt.norm_le_one a) hc)
      exact ⟨ψ l a', ⟨a', 0, by simp⟩, by rw [hb]; simp [map_mul]⟩
    obtain ⟨x, y, hxy⟩ := exists_norm l h5 dK hld a ha
    refine ⟨ψ l x + δ * ψ l y, ⟨x, y, rfl⟩, ?_⟩
    rw [hb, mul_zero, add_zero, ← hxy]
    simp only [map_add, map_mul, σ_ψ l σ hσ, hσδ, map_natCast]
    linear_combination (-(ψ l y * ψ l y)) * hδ
  hsep := by
    intro x hx hx0
    have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl)
    refine ⟨N, ?_⟩
    rintro ⟨y, hy, rfl⟩
    have hy1 := norm_le_one_of_mem hy
    rw [norm_mul, norm_pow, norm_l_Kur] at hpos
    rw [norm_mul, norm_pow, norm_l_Kur] at hN
    have : (l : ℝ)⁻¹ ^ N * ‖y‖ ≤ (l : ℝ)⁻¹ ^ N := mul_le_of_le_one_right (by positivity) hy1
    linarith

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
end
end

section
noncomputable section
open scoped BigOperators
open Matrix

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
open Formalism.L2.Th1.Top.FrP

section Blocks
variable {K : Type*} [CommRing K] {n : Type} [Fintype n] [DecidableEq n]

def what₂ {m : Type*} (X : Matrix (Fin 4 × n) m K) (b : Fin 4) : Matrix n m K := fun i w => X (b, i) w

theorem blockDiag_mul_apply' {m : Type*} [Fintype m] (P : Matrix n n K) (Q : Matrix (Fin 4 × n) m K)
    (a : Fin 4) (i : n) (w : m) : (bd4 P * Q) (a, i) w = ∑ j, P i j * Q (a, j) w := by
  simp only [bd4, Matrix.mul_apply, Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

theorem mul_bd4_apply {m : Type*} [Fintype m] (X : Matrix m (Fin 4 × n) K) (P : Matrix n n K)
    (x : m) (a : Fin 4) (j : n) : (X * bd4 P) x (a, j) = ∑ k, X x (a, k) * P k j := by
  simp only [bd4, Matrix.mul_apply, Fintype.sum_prod_type, mul_ite, mul_zero]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem transpose_mul_blockDiag_mul {m m' : Type*} [Fintype m] [Fintype m'] (X : Matrix (Fin 4 × n) m K)
    (Y : Matrix (Fin 4 × n) m' K) (H : Matrix n n K) :
    Xᵀ * bd4 H * Y = ∑ b : Fin 4, (what₂ X b)ᵀ * H * what₂ Y b := by
  ext w w'
  rw [Matrix.sum_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_bd4_apply]
  simp only [what₂, Matrix.mul_apply, transpose_apply]

theorem blockShift_mul_apply {m : Type*} [Fintype m] (c : Fin 4) (X : Matrix (Fin 4 × n) m K) (b : Fin 4) (i : n)
    (w : m) : ((bmv0 c : Matrix (Fin 4 × n) (Fin 4 × n) K) * X) (b, i) w = if b = 0 then X (c, i) w else 0 := by
  simp only [bmv0, Matrix.mul_apply, ite_mul, one_mul, zero_mul]
  by_cases hb : b = 0
  · rw [if_pos hb, Finset.sum_eq_single (c, i)]
    · simp [hb]
    · rintro ⟨b', j⟩ _ hne
      rw [if_neg]
      rintro ⟨-, h1, h2⟩
      exact hne (Prod.ext h1 h2.symm)
    · simp
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [if_neg]
    rintro ⟨h, -⟩
    exact hb h

theorem blockDiag_map' {L : Type*} [CommRing L] (f : K →+* L) (P : Matrix n n K) : (bd4 P).map f = bd4 (P.map f) := by
  ext x y
  simp only [bd4, Matrix.map_apply]
  split_ifs <;> simp

theorem bd4_transpose (P : Matrix n n K) : (bd4 P)ᵀ = bd4 Pᵀ := by
  ext x y
  simp only [bd4, transpose_apply]
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd h1.symm h2 | exact absurd h2.symm h1

theorem blockDiag_mul' (P Q : Matrix n n K) : bd4 P * bd4 Q = bd4 (P * Q) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [blockDiag_mul_apply']
  simp only [bd4, Matrix.mul_apply]
  split_ifs with h <;> simp

theorem bd4_smul (r : K) (P : Matrix n n K) : bd4 (r • P) = r • bd4 P := by
  ext x y
  simp only [bd4, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

end Blocks

section Lmat
variable {l : ℕ} [Fact l.Prime] {m m' : Type}

theorem lmat_apply (δ : MaximalUnramifiedExtension l) (A B : Matrix m m' ℚ) (x : m) (y : m') :
    lmat δ A B x y = (A x y : MaximalUnramifiedExtension l) + δ * (B x y : MaximalUnramifiedExtension l) := by
  simp [lmat]

theorem lmat_map_σ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (δ : MaximalUnramifiedExtension l) (hσδ : σ δ = -δ) (A B : Matrix m m' ℚ) :
    (lmat δ A B).map σ = lmat δ A (-B) := by
  ext x y
  simp only [Matrix.map_apply, lmat_apply, map_add, map_mul, map_ratCast, hσδ, Matrix.neg_apply, Rat.cast_neg]
  ring

theorem lmat_mem {dK : ℕ} {δ : MaximalUnramifiedExtension l} {hδ : δ ^ 2 = -(dK : MaximalUnramifiedExtension l)} (U₁ U₂ : Matrix m m' ℚ)
    (hU : ∀ x y, padicNorm l (U₁ x y) ≤ 1 ∧ padicNorm l (U₂ x y) ≤ 1) (x : m) (y : m') :
    lmat δ U₁ U₂ x y ∈ OO dK δ hδ := by
  rw [lmat_apply]
  exact (OO dK δ hδ).add_mem (ratCast_mem _ (hU x y).1) ((OO dK δ hδ).mul_mem δ_mem (ratCast_mem _ (hU x y).2))

end Lmat

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
end
end

section
open Matrix

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
namespace JSetup

variable {K : Type*} [Field K] (S : JSetup K)

private theorem mulVec_comp_equiv_apply {ι : Type*} [Fintype ι] {m : ℕ} (Γ : Matrix ι ι K) (e : ι ≃ Fin m)
    (x : Fin m → K) (i : ι) :
    (Γ *ᵥ (x ∘ e)) i = (Γ.submatrix e.symm e.symm *ᵥ x) (e i) := by
  simp only [mulVec, dotProduct, submatrix_apply, Equiv.symm_apply_apply, Function.comp]
  exact Fintype.sum_equiv e _ _ (fun j => by simp)

private theorem vecMul_comp_equiv_apply {ι : Type*} [Fintype ι] {m : ℕ} (Γ : Matrix ι ι K) (e : ι ≃ Fin m)
    (x : Fin m → K) (j : ι) :
    ((x ∘ e) ᵥ* Γ) j = (x ᵥ* Γ.submatrix e.symm e.symm) (e j) := by
  simp only [vecMul, dotProduct, submatrix_apply, Equiv.symm_apply_apply, Function.comp]
  exact Fintype.sum_equiv e _ _ (fun i => by simp)

theorem jac {ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : Matrix ι ι K) (hΓ : S.IntM Γ) (hH : S.Herm Γ)
    (hU : S.UM Γ) :
    ∃ (k : ℕ) (v : Fin k → ι → K), (∀ c, S.IntV (v c)) ∧
      (∀ c c', S.hf Γ (v c) (v c') = if c = c' then 1 else 0) ∧
      ∑ c, Matrix.vecMulVec (Γ *ᵥ v c) (S.cv (v c) ᵥ* Γ) = Γ := by
  classical
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  have hU' : S.UM (Γ.submatrix e.symm e.symm) := by
    intro x hx hxd
    obtain ⟨x', hx', hxx'⟩ := hU (x ∘ e) (fun i => hx (e i)) (fun i => by
      rw [mulVec_comp_equiv_apply Γ e x i]; exact hxd (e i))
    refine ⟨x' ∘ e.symm, fun s => hx' (e.symm s), ?_⟩
    funext s
    have h1 := mulVec_comp_equiv_apply Γ e x (e.symm s)
    have h2 := mulVec_comp_equiv_apply Γ e (x' ∘ e.symm) (e.symm s)
    rw [Equiv.apply_symm_apply] at h1 h2
    have h3 : (x' ∘ e.symm) ∘ e = x' := by funext i; simp
    rw [h3] at h2
    rw [Pi.smul_apply, ← h1, ← h2, hxx', Pi.smul_apply]
  obtain ⟨k, v, hv, hort, hsum⟩ := S.jac_fin (Fintype.card ι) (Γ.submatrix e.symm e.symm)
    (fun s t => hΓ _ _) (fun s t => hH _ _) hU'
  have hconj : ∀ x : Fin (Fintype.card ι) → K, S.cv (x ∘ e) = S.cv x ∘ e := fun x => rfl
  refine ⟨k, fun c => v c ∘ e, fun c i => hv c (e i), fun c c' => ?_, ?_⟩
  · rw [← hort c c']
    simp only [hf, hconj, dotProduct]
    exact Fintype.sum_equiv e _ _ (fun i => by
      simp only [Function.comp, mulVec_comp_equiv_apply Γ e (v c') i])
  · ext i j
    have h := congrFun (congrFun hsum (e i)) (e j)
    simp only [Matrix.sum_apply, vecMulVec_apply, submatrix_apply, Equiv.symm_apply_apply] at h
    simp only [Matrix.sum_apply, vecMulVec_apply, hconj, mulVec_comp_equiv_apply Γ e _ i,
      vecMul_comp_equiv_apply Γ e _ j]
    exact h

end JSetup

theorem card_eq_of_mul_eq_one {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ}
    (V : Matrix n (Fin k) K) (W : Matrix (Fin k) n K) (h1 : V * W = 1) (h2 : W * V = 1) :
    Fintype.card n = k := by
  have e : (Fin k → K) ≃ₗ[K] (n → K) :=
    LinearEquiv.ofLinear (Matrix.toLin' V) (Matrix.toLin' W)
      (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
  have h := e.finrank_eq
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  omega

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
end

section
noncomputable section
open scoped BigOperators
open Matrix

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
open Formalism.L2.Th1.Top.FrP Jac

set_option maxHeartbeats 400000 in
theorem local_core' : LocCore := by
  intro l _ dK σ δ h5 hld hin hσ hδ hσδ n _ _ M₁ M₂ R₁ R₂ c hc hGram hmv
  set S := setup h5 dK hld hin σ hσ δ hδ hσδ with hS
  have hSσ : S.σ = σ := rfl
  set M := lmat δ M₁ M₂ with hM
  set Mb := lmat δ M₁ (-M₂) with hMb
  have hMσ : M.map σ = Mb := lmat_map_σ σ δ hσδ M₁ M₂
  have hMbσ : Mb.map σ = M := by rw [hMb, lmat_map_σ σ δ hσδ, neg_neg]
  have hc0 : (c : MaximalUnramifiedExtension l) ≠ 0 := by
    have : c ≠ 0 := by rintro rfl; simp at hc
    exact_mod_cast this
  set H₀ : Matrix n n (MaximalUnramifiedExtension l) := (c : MaximalUnramifiedExtension l)⁻¹ • (lmat δ R₁ R₂).map σ with hH₀

  have hE : Mbᵀ * bd4 H₀ * M = 1 := by
    have h1 := congrArg (fun X => X.map σ) hGram
    simp only [Matrix.map_mul, transpose_map, blockDiag_map', hMσ, hMbσ] at h1
    have h1' : ((c : MaximalUnramifiedExtension l) • (1 : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l))).map σ = (c : MaximalUnramifiedExtension l) • 1 := by
      refine Matrix.ext fun x y => ?_
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
    rw [h1'] at h1
    rw [hH₀, bd4_smul, Matrix.mul_smul, Matrix.smul_mul, h1, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hE2 : Mbᵀ * bd4 (H₀.map σ)ᵀ * M = 1 := by
    have h1 := congrArg (fun X => (X.map σ)ᵀ) hE
    simp only [Matrix.map_mul, transpose_map, blockDiag_map', hMσ, hMbσ, transpose_mul, transpose_transpose,
      Matrix.map_one σ (map_zero σ) (map_one σ), transpose_one, bd4_transpose] at h1
    simpa [Matrix.mul_assoc] using h1

  set Z : Matrix n (Fin 4 × n) (MaximalUnramifiedExtension l) := what₂ M 0 with hZ
  set Zb : Matrix n (Fin 4 × n) (MaximalUnramifiedExtension l) := what₂ Mb 0 with hZb'
  have hZb : Z.map σ = Zb := Matrix.ext fun i w => congrFun (congrFun hMσ (0, i)) w
  have hZbσ : Zb.map σ = Z := Matrix.ext fun i w => congrFun (congrFun hMbσ (0, i)) w
  have hZZ : Z * (Zbᵀ * H₀) = 1 := by
    have h1 : M * (Mbᵀ * bd4 H₀) = 1 := mul_eq_one_comm.mp hE
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun h1 (0, i)) (0, j)
    rw [← Matrix.mul_assoc, mul_bd4_apply] at this
    rw [← Matrix.mul_assoc, Matrix.mul_apply]
    simp only [Matrix.one_apply, Prod.mk.injEq, true_and] at this
    rw [Matrix.one_apply]
    simpa [Matrix.mul_apply, hZ, hZb', what₂] using this
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l), Γ = Zbᵀ * H₀ * Z := ⟨_, rfl⟩

  choose U₁ U₂ hUint hUeq using hmv
  set U : Fin 4 → Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l) := fun b => lmat δ (U₁ b) (U₂ b) with hU
  have hUO : ∀ b x y, U b x y ∈ S.O := fun b x y => lmat_mem (dK := dK) (hδ := hδ) (U₁ b) (U₂ b) (hUint b) x y
  have hZc : ∀ b, what₂ M b = Z * U b := by
    intro b; refine Matrix.ext fun i w => ?_
    have := congrFun (congrFun (hUeq b) (0, i)) w
    rw [blockShift_mul_apply, if_pos rfl] at this
    exact this
  have hrowsN : ∀ b, what₂ (M * U 0) b = if b = 0 then Z else 0 := by
    intro b; refine Matrix.ext fun i w => ?_
    have := congrFun (congrFun (hUeq 0) (b, i)) w
    rw [blockShift_mul_apply] at this
    rw [what₂, ← this]
    split_ifs <;> rfl
  have hΓU : Γ = ((U 0).map σ)ᵀ * U 0 := by
    have hN : ((M * U 0).map σ)ᵀ * bd4 H₀ * (M * U 0) = ((U 0).map σ)ᵀ * U 0 := by
      rw [Matrix.map_mul, hMσ, transpose_mul]
      calc ((U 0).map σ)ᵀ * Mbᵀ * bd4 H₀ * (M * U 0) = ((U 0).map σ)ᵀ * (Mbᵀ * bd4 H₀ * M) * U 0 := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hE, Matrix.mul_one]
    rw [← hN, transpose_mul_blockDiag_mul, Fin.sum_univ_four]
    have hr : ∀ b, what₂ ((M * U 0).map σ) b = (what₂ (M * U 0) b).map σ := fun b => rfl
    simp only [hr, hrowsN]
    simp [hZb, hΓ]
  have hΓI : S.IntM Γ := by
    intro w w'
    rw [hΓU, Matrix.mul_apply]
    exact S.O.sum_mem fun k _ => S.O.mul_mem (S.hσO _ (hUO 0 k w)) (hUO 0 k w')
  have hΓH : S.Herm Γ := by
    intro w w'
    rw [hΓU]
    simp only [hSσ, Matrix.mul_apply, transpose_apply, Matrix.map_apply, map_sum, map_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := S.hσσ _ (hUO 0 k w)
    rw [hSσ] at h
    rw [h]
    ring
  have hidem : Γ * Γ = Γ := by
    calc Γ * Γ = Zbᵀ * H₀ * (Z * (Zbᵀ * H₀)) * Z := by simp only [hΓ, Matrix.mul_assoc]
      _ = Γ := by rw [hZZ, Matrix.mul_one, hΓ]
  have hΓUM : S.UM Γ := by
    intro x hx hNU
    choose y hyO hy using hNU
    refine ⟨y, hyO, ?_⟩
    have hΓx : Γ *ᵥ x = S.p • y := funext fun i => by rw [hy i]; rfl
    have h2 : Γ *ᵥ (Γ *ᵥ x) = Γ *ᵥ x := by rw [mulVec_mulVec, hidem]
    rw [hΓx, mulVec_smul] at h2
    rw [hΓx, h2]
  obtain ⟨k, v, hvI, hvo, hvs⟩ := S.jac Γ hΓI hΓH hΓUM
  clear_value Z Zb H₀ M Mb

  set A : Matrix (Fin 4 × n) (Fin k) (MaximalUnramifiedExtension l) := Matrix.of fun w c => v c w with hA
  have hAO : ∀ w c, A w c ∈ S.O := fun w c => hvI c w
  have hAo : (A.map σ)ᵀ * Γ * A = 1 := by
    refine Matrix.ext fun c c' => ?_
    rw [Matrix.one_apply, ← hvo c c']
    simp only [JSetup.hf, JSetup.cv, hSσ, dotProduct, mulVec, Matrix.mul_apply, transpose_apply,
      Matrix.map_apply, hA, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hAs : Γ * A * ((A.map σ)ᵀ * Γ) = Γ := by
    conv_rhs => rw [← hvs]
    refine Matrix.ext fun w w' => ?_
    rw [Matrix.mul_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [vecMulVec_apply, Matrix.mul_apply, mulVec, dotProduct, vecMul, JSetup.cv, hSσ, transpose_apply,
      Matrix.map_apply, hA, Matrix.of_apply]
  obtain ⟨V, hV⟩ : ∃ V : Matrix n (Fin k) (MaximalUnramifiedExtension l), V = Z * A := ⟨_, rfl⟩
  obtain ⟨Ti₀, hTi₀⟩ : ∃ Ti₀ : Matrix (Fin k) n (MaximalUnramifiedExtension l), Ti₀ = (V.map σ)ᵀ * H₀ := ⟨_, rfl⟩
  have hVσ : V.map σ = Zb * A.map σ := by rw [hV, Matrix.map_mul, hZb]
  have hTZ : Ti₀ * Z = (A.map σ)ᵀ * Γ := by
    rw [hTi₀, hVσ, transpose_mul, hΓ]; simp only [Matrix.mul_assoc]
  have hTV : Ti₀ * V = 1 := by
    rw [hV, ← Matrix.mul_assoc, hTZ, hAo]
  have hZΓ : Z * Γ = Z := by
    calc Z * Γ = Z * (Zbᵀ * H₀) * Z := by simp only [hΓ, Matrix.mul_assoc]
      _ = Z := by rw [hZZ, Matrix.one_mul]
  have hGZ : Zbᵀ * H₀ = Γ * (Zbᵀ * H₀) := by
    calc Zbᵀ * H₀ = Zbᵀ * H₀ * (Z * (Zbᵀ * H₀)) := by rw [hZZ, Matrix.mul_one]
      _ = Γ * (Zbᵀ * H₀) := by simp only [hΓ, Matrix.mul_assoc]
  have hTi₀' : Ti₀ = (A.map σ)ᵀ * (Zbᵀ * H₀) := by rw [hTi₀, hVσ, transpose_mul, Matrix.mul_assoc]
  have hVT : V * Ti₀ = 1 := by
    have s1 : V * Ti₀ = Z * A * ((A.map σ)ᵀ * (Zbᵀ * H₀)) := by rw [hV, hTi₀']
    have s2 : Z * A * ((A.map σ)ᵀ * (Zbᵀ * H₀)) = Z * Γ * A * ((A.map σ)ᵀ * (Γ * (Zbᵀ * H₀))) :=
      (congrArg (fun X => Z * A * ((A.map σ)ᵀ * X)) hGZ).trans
        (congrArg (fun X => X * A * ((A.map σ)ᵀ * (Γ * (Zbᵀ * H₀)))) hZΓ.symm)
    have s3 : Z * Γ * A * ((A.map σ)ᵀ * (Γ * (Zbᵀ * H₀))) = Z * (Γ * A * ((A.map σ)ᵀ * Γ)) * (Zbᵀ * H₀) := by
      simp only [Matrix.mul_assoc]
    have s4 : Z * (Γ * A * ((A.map σ)ᵀ * Γ)) * (Zbᵀ * H₀) = 1 := by rw [hAs, hZΓ, hZZ]
    exact s1.trans (s2.trans (s3.trans s4))

  have hk : Fintype.card n = k := card_eq_of_mul_eq_one V Ti₀ hVT hTV
  set e : Fin k ≃ n := (Fintype.equivFinOfCardEq hk).symm with he
  set T : Matrix n n (MaximalUnramifiedExtension l) := V.submatrix id e.symm with hT
  set Ti : Matrix n n (MaximalUnramifiedExtension l) := Ti₀.submatrix e.symm id with hTi
  have hTTi : T * Ti = 1 := by
    refine Matrix.ext fun i j => ?_
    have h1 := congrFun (congrFun hVT i) j
    rw [Matrix.mul_apply] at h1
    rw [← h1, Matrix.mul_apply]
    simp only [hT, hTi, submatrix_apply, id_eq]
    exact Equiv.sum_comp e.symm (fun c => V i c * Ti₀ c j)

  have hAσσ : (A.map σ).map σ = A := Matrix.ext fun w c => by
    have h := S.hσσ _ (hAO w c)
    rw [hSσ] at h
    simpa using h
  have hVσσ : (V.map σ).map σ = V := by rw [hVσ, Matrix.map_mul, hZbσ, hAσσ, hV]
  have hTi₀σ : (Ti₀.map σ)ᵀ * Ti₀ = (H₀.map σ)ᵀ := by
    have h1 : (Ti₀.map σ)ᵀ = (H₀.map σ)ᵀ * V := by
      rw [hTi₀, Matrix.map_mul, transpose_mul, transpose_map, transpose_transpose, hVσσ]
    rw [h1, Matrix.mul_assoc, hVT, Matrix.mul_one]
  have hTiσ : (Ti.map σ)ᵀ * Ti = (H₀.map σ)ᵀ := by
    rw [← hTi₀σ]
    refine Matrix.ext fun i j => ?_
    simp only [hTi, Matrix.mul_apply, transpose_apply, Matrix.map_apply, submatrix_apply, id_eq]
    exact Equiv.sum_comp e.symm (fun c => σ (Ti₀ c i) * Ti₀ c j)
  have hU1 : ((bd4 Ti * M).map σ)ᵀ * (bd4 Ti * M) = 1 := by
    rw [Matrix.map_mul, blockDiag_map', hMσ, transpose_mul, bd4_transpose]
    calc Mbᵀ * bd4 (Ti.map σ)ᵀ * (bd4 Ti * M) = Mbᵀ * (bd4 (Ti.map σ)ᵀ * bd4 Ti) * M := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [blockDiag_mul', hTiσ]; exact hE2

  have hγ : ∀ b i w, (bd4 Ti * M) (b, i) w = ((A.map σ)ᵀ * Γ * U b) (e.symm i) w := by
    intro b i w
    rw [blockDiag_mul_apply']
    have h1 : (Ti * what₂ M b) i w = ∑ j, Ti i j * M (b, j) w := rfl
    rw [← h1, hZc b, ← Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun w' _ => ?_
    congr 1
    show (Ti₀ * Z) (e.symm i) w' = _
    rw [hTZ]
  have hγO : ∀ x y, (bd4 Ti * M) x y ∈ S.O := by
    rintro ⟨b, i⟩ w
    rw [hγ, Matrix.mul_apply]
    refine S.O.sum_mem fun w' _ => S.O.mul_mem ?_ (hUO b w' w)
    rw [Matrix.mul_apply]
    refine S.O.sum_mem fun x _ => S.O.mul_mem ?_ (hΓI x w')
    have h := S.hσO _ (hAO x (e.symm i))
    rw [hSσ] at h
    simpa using h
  refine ⟨T, Ti, hTTi, ?_⟩
  unfold IsUnitaryK
  refine ⟨fun a b => ⟨norm_le_one_of_mem (dK := dK) (hδ := hδ) (hγO a b), ?_⟩, fun a b => ?_⟩
  · have h := S.hσσ _ (hγO a b)
    rwa [hSσ] at h
  · have h := congrFun (congrFun hU1 a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simp only [transpose_apply, Matrix.map_apply] at h
    exact h

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
end
end

section
namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame



end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
end

section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

abbrev L7 : PeriodPair := cmL 1 1 7 (by norm_num) (by norm_num) 1 one_ne_zero




abbrev h7 : Matrix (Fin 1) (Fin 1) ℂ := (((area L7 : ℝ) : ℂ)⁻¹) • (1 : Matrix (Fin 1) (Fin 1) ℂ)












end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
end
end

section
namespace Formalism.L2.Th1.Top.FrP

theorem hermFrame_holds : HermFrame :=
  UnitaryGroupMassFormula.HermFrame.hermFrame_of_locCore UnitaryGroupMassFormula.HermFrame.Loc.local_core'

end Formalism.L2.Th1.Top.FrP
end
