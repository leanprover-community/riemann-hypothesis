module

import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramLocPfA
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.SpanPowerMembership.PlacesOverNcardOfSplitInj
import Mathlib.Tactic.Linter.Style
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Gaps.LevGap

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits Formalism.MainNotions.Gaps.LG
open scoped Pointwise

theorem int_dvd_of_mem_span {E : Type*} [Field E] [NumberField E] (N a : ℤ)
    (h : (a : 𝓞 E) ∈ Ideal.span {(N : 𝓞 E)}) : N ∣ a := by
  rwa [← Ideal.mem_span_singleton,
    ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := 𝓞 E) (Ideal.span {N}),
    Ideal.mem_comap, Ideal.map_span, Set.image_singleton]

theorem norm_congr_one {E : Type*} [Field E] [NumberField E] (c : E ≃ₐ[ℚ] E) (T M : ℕ) (pz : 𝓞 E)
    (hpz : (pz : E) * c (pz : E) = (T : E)) (hcong : (pz - 1) ∈ Ideal.span {(M : 𝓞 E)}) :
    (M : ℤ) ∣ (T : ℤ) - 1 := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hcong
  set c' : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (c : E ≃+* E) with hc'
  have hT : (T : 𝓞 E) = pz * c' pz := by
    apply RingOfIntegers.ext
    have : ((c' pz : 𝓞 E) : E) = c (pz : E) := rfl
    show ((T : 𝓞 E) : E) = (pz : E) * ((c' pz : 𝓞 E) : E)
    rw [this, hpz]; simp
  have hp : pz = 1 + y * M := by rw [hy]; ring
  have hcp : c' pz = 1 + c' y * M := by rw [hp]; simp
  apply int_dvd_of_mem_span (E := E)
  rw [Ideal.mem_span_singleton']
  refine ⟨y + c' y + y * c' y * M, ?_⟩
  push_cast
  rw [hT, hcp]
  linear_combination (-(1 + c' y * M)) * hp

section Gen

variable {E : Type} [Field E] [NumberField E]

end Gen

section HostInst

variable {R : Ranks} (H : Host R) (T : ℕ) (pz : 𝓞 H.E)
  (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
  (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})

include hpz hcong

theorem T_congr : ((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : ℤ) ∣ (T : ℤ) - 1 :=
  norm_congr_one H.conj T _ pz hpz hcong

theorem T_split_E (hT : T.Prime) :
    {v : HeightOneSpectrum (𝓞 H.E) | (T : 𝓞 H.E) ∈ v.asIdeal}.ncard = Module.finrank ℚ H.E := by
  have : Fact T.Prime := ⟨hT⟩
  have hm : T ≡ 1 [MOD H.condN] := by
    refine Nat.ModEq.symm (Nat.modEq_iff_dvd.2 ?_)
    exact (Int.natCast_dvd_natCast.2 (Dvd.intro _ rfl)).trans (T_congr H T pz hpz hcong)
  have h1 : H.condN ≠ 1 := by
    intro h
    have hq : H.q ∣ H.condN := ⟨H.QS * H.d, by show H.QS * H.q * H.d = _; ring⟩
    rw [h] at hq
    exact H.hypOdd.1.one_lt.ne' (Nat.dvd_one.1 hq)
  refine placesOver_ncard_of_split H T ?_
  rw [hm, Nat.one_mod_eq_one.2 h1]

end HostInst

section HostGal

variable {R : Ranks} (H : Host R)

theorem conj_eq_sigmaOf : H.conj = H.sigmaOf (R.cc) := rfl

theorem sigmaOf_mul (g h : R.GG) : H.sigmaOf (g * h) = H.sigmaOf g * H.sigmaOf h :=
  map_mul (H.gal).symm g h

theorem sigmaOf_injective : Function.Injective H.sigmaOf := (H.gal).symm.injective

end HostGal

section Deg

variable {K : Type} [Field K] [NumberField K]

theorem natCast_notMem_sq_of_split (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 K) | (p : 𝓞 K) ∈ v.asIdeal}.ncard = Module.finrank ℚ K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (p : 𝓞 K) ∈ v.asIdeal) : (p : 𝓞 K) ∉ v.asIdeal ^ 2 := by
  intro h
  have h1 := (v.intValuation_le_pow_iff_mem (p : 𝓞 K) 2).2 h
  rw [_root_.Formalism.L2.SG.Pf.SatGramLoc.intValuation_split p hp hs v hv, WithZero.exp_le_exp] at h1
  norm_num at h1

end Deg

end Formalism.MainNotions.Gaps.LevGap

end
