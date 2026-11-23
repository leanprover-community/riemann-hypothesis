module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsApproxModPowersStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitNotLocalKummerNormOfNotPowStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowCardLeIndexIInfOfPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsLocalPowersAtPlacesIndexLeStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsMappingToPowersLeUnitsLocalKummerNormsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem mem_kNorm_iff_map_mem_id (p : ℕ) {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F)
    (x : Fˣ) :
    x ∈ kNorm p φ δ ↔ Units.map (φ : F →* L) x ∈ kNorm p (RingHom.id L) (φ δ) := by
  rw [mem_kNorm, mem_kNorm]
  exact Iff.rfl

theorem pow_tNon_le_index_finNorm :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ δ : F)
      (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p →
      (finNorm p F δ S).index ≠ 0 ∧ p ^ tNon p F δ S ≤ (finNorm p F δ S).index := by
  intro p F _ _ _ ζ δ S hp hζ
  classical
  have hpow := (GlobalTheory.T.unitsMappingToPowers_le_unitsLocalKummerNorms p hp.pos).1
  have hPN : finPow p F S ≤ finNorm p F δ S := by
    unfold finPow finNorm
    exact iInf_mono fun v => iInf_mono fun _ => hpow _ _ _ _
  have h0 : (finNorm p F δ S).index ≠ 0 :=
    ne_zero_of_dvd_ne_zero (GlobalTheory.T.unitsLocalPowersAtPlaces_index_le p F S hp.pos).1 (Subgroup.index_dvd_of_le hPN)
  refine ⟨h0, ?_⟩
  set A : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | v ∈ S ∧ ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ} with hA
  have hAf : A.Finite := S.finite_toSet.subset fun v hv => hv.1
  letI : Fintype A := hAf.fintype
  let K : A → Subgroup Fˣ := fun v => kNorm p (algebraMap F (v.1.adicCompletion F)) δ
  have hle : finNorm p F δ S ≤ ⨅ i, K i := le_iInf fun v => iInf₂_le v.1 v.2.1
  have hdvd := Subgroup.index_dvd_of_le hle
  have hcard : Fintype.card A = tNon p F δ S := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [← hcard]
  refine le_trans (GlobalTheory.T.pow_card_le_index_iInf_of_prime' p Fˣ A K hp ?_ ?_ (ne_zero_of_dvd_ne_zero h0 hdvd))
    (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd)
  · intro v x
    exact hpow _ _ _ _ ⟨algebraMap F _ (x : F), by simp⟩
  · intro v
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_unit_not_localKummerNorm_of_not_pow p F ζ δ v.1 hp hζ v.2.2
    obtain ⟨x, hx0, hxv⟩ := GlobalTheory.T.exists_approx_mod_powers' p F S
      (Function.update (fun w : HeightOneSpectrum (𝓞 F) => (1 : w.adicCompletion F)) v.1
        (c : v.1.adicCompletion F)) hp.pos (by
        intro w
        by_cases hw : w = v.1
        · subst hw; simp
        · simp [Function.update_of_ne hw])
    refine ⟨Units.mk0 x hx0, ?_, ?_⟩
    · intro hm
      obtain ⟨r, hr⟩ := hxv v.1 v.2.1
      rw [Function.update_self] at hr
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [zero_pow hp.ne_zero, mul_zero] at hr
        exact hx0 (by simpa using hr)
      have hm' := (mem_kNorm_iff_map_mem_id p _ δ _).1 hm
      have hrm : (Units.mk0 r hr0) ^ p ∈ kNorm p (RingHom.id (v.1.adicCompletion F))
          (algebraMap F (v.1.adicCompletion F) δ) := hpow _ _ _ _ ⟨r, by simp⟩
      apply hc
      have hq := Subgroup.div_mem _ hm' hrm
      convert hq using 1
      rw [eq_div_iff_mul_eq']
      apply Units.ext
      simpa using hr.symm
    · intro w hj
      have hw : w.1 ≠ v.1 := fun h => hj (Subtype.ext h)
      obtain ⟨r, hr⟩ := hxv w.1 w.2.1
      rw [Function.update_of_ne hw, one_mul] at hr
      exact hpow _ _ _ _ ⟨r, hr.symm⟩

end GlobalTheory.CNorm
