module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CyclicKummerNormFixedHilbert90Statement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqPowMulPthPowAdicCompletionUnit
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsKum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlaceNotPowAdicCompletionStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRingHomAdicCompletionUnder
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSupersetMemSUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSet
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_place_pow_and_not_pow :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ δ u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → δ ≠ 0 → u ≠ 0 → (∀ r : F, r ^ p ≠ δ) → (∀ (k : ℕ) (r : F), u ≠ δ ^ k * r ^ p) → ∃ v, v ∉ S₀ ∧ (∃ r : v.adicCompletion F, r ^ p = algebraMap F (v.adicCompletion F) δ) ∧ ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) u := by
  classical
  intro p F _ _ _ ζ δ u S₀ hp hζ hδ hu hδs huδ
  obtain ⟨E, _, _, θ, σ, hq⟩ := exists_isKum p F ζ δ hp hζ hδs
  obtain ⟨hfd, -, -, -, -, hpow, -⟩ := GlobalTheory.T.cyclic_hilbert90_kummer_and_mem_kNorm_iff p F E ζ δ θ σ hq
  haveI : NumberField E := NumberField.of_module_finite F E
  haveI : IsTotallyComplex E := isTotallyComplex_of_algebra F E
  have huE : ∀ y : E, y ^ p ≠ algebraMap F E u := by
    intro y h
    obtain ⟨k, r, hr⟩ := hpow u y h
    exact huδ k r hr
  have h2 : (p : F) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨S, hS, hSu⟩ := exists_superset_mem_sUnits F
    {Units.mk0 (p : F) h2, Units.mk0 δ hδ, Units.mk0 u hu} S₀
  obtain ⟨SE, hSE⟩ := (places_over F E).1 S
  obtain ⟨w, hw, hwu⟩ := GlobalTheory.T.exists_place_not_pow_adicCompletion p E (algebraMap F E ζ) (algebraMap F E u) SE hp
    (hζ.map_of_injective (algebraMap F E).injective) (by simpa using hu) huE
  obtain ⟨φ, hφ⟩ := exists_ringHom_adicCompletion_under F E w
  have hv : w.under (𝓞 F) ∉ S := fun h => hw ((hSE w).2 h)
  have hval : ∀ x : F, Valued.v (algebraMap F ((w.under (𝓞 F)).adicCompletion F) x)
      = (w.under (𝓞 F)).valuation F x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' _ x
  have hv2 : (w.under (𝓞 F)).valuation F (p : F) = 1 :=
    (mem_sUnits F S _).1 (hSu S subset_rfl (Units.mk0 (p : F) h2) (by simp)) _ hv
  have hvδ : (w.under (𝓞 F)).valuation F δ = 1 :=
    (mem_sUnits F S _).1 (hSu S subset_rfl (Units.mk0 δ hδ) (by simp)) _ hv
  have hvu : (w.under (𝓞 F)).valuation F u = 1 :=
    (mem_sUnits F S _).1 (hSu S subset_rfl (Units.mk0 u hu) (by simp)) _ hv
  have hunsq : ∀ r : (w.under (𝓞 F)).adicCompletion F,
      r ^ p ≠ algebraMap F ((w.under (𝓞 F)).adicCompletion F) u := by
    intro r h
    apply hwu (φ r)
    rw [← hφ, ← h, map_pow]
  refine ⟨w.under (𝓞 F), fun h => hv (hS h), ?_, hunsq⟩
  by_contra hδn
  push Not at hδn
  obtain ⟨k, r, hr⟩ := exists_eq_pow_mul_pow_of_unit p F (w.under (𝓞 F)) _ _ hp hv2
    ((hval δ).trans hvδ) ((hval u).trans hvu) hδn
  apply hwu (algebraMap E (w.adicCompletion E) θ ^ k * φ r)
  rw [← hφ, hr, map_mul, map_pow, map_pow, hφ, ← hq.pow, map_pow, mul_pow, ← pow_mul, ← pow_mul,
    mul_comm k p]

end GlobalTheory.CNorm
