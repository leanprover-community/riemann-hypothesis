module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.WeilBound.ThetaLifts.WeilDomination.FacNeGauss
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace PositivityTheory.ThK.Close

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}

theorem continuous_chrW' {χ : Chr F E} (hχ : Continuous χ) (τ : E →ₐ[F] Fv F v) :
    Continuous fun x => (chrW χ τ x : ℂ) :=
  (continuous_locChar hχ (splitPrime τ)).comp
    (Continuous.units_map _ (SplitChart.continuous_complMap (splitPrime_under τ)))

theorem exists_unit_chrW_ne {χ : Chr F E} (τ : E →ₐ[F] Fv F v) (h : ¬ UnrAt χ (splitPrime τ)) :
    ∃ x : (Fv F v)ˣ, (x : Fv F v) ∈ v.adicCompletionIntegers F ∧
      ((x⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F ∧ chrW χ τ x ≠ 1 := by
  obtain ⟨ψ, h1, -, h3, -⟩ := SplitChart.exists_equiv_complMap τ (splitPrime_under τ)
  simp only [UnrAt, not_forall] at h
  obtain ⟨y, hy, hne⟩ := h
  have e : Units.map (complMap (splitPrime_under τ)).toMonoidHom (Units.map ψ.symm.toRingHom.toMonoidHom y) = y :=
    Units.ext ((h1 _).symm.trans (ψ.apply_symm_apply _))
  have hv : Valued.v ((Units.map ψ.symm.toRingHom.toMonoidHom y : (Fv F v)ˣ) : Fv F v) = 1 := by
    rw [← h3]
    exact (congrArg Valued.v (ψ.apply_symm_apply (y : _))).trans hy
  refine ⟨Units.map ψ.symm.toRingHom.toMonoidHom y, ?_, ?_, fun h0 => hne ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hv.le
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
  · rw [← e]
    exact h0

theorem eps_ne_zero {ψ : AddChar (AF F) ℂ} {ν : (Fv F v)ˣ →* ℂˣ} (h : gauss ψ ν ≠ 0) (z : ℤ) : eps ψ ν z ≠ 0 :=
  mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (Nat.cast_ne_zero.2 (one_lt_absNorm v).ne_bot)) h)
    (pow_ne_zero _ (Units.ne_zero _))

theorem facNe : GlobalTheory.ThK.FacNe := by
  classical
  intro F E _ _ _ _ _ σ B a a' G X om om' h e₁ e₂ s 𝔟 𝔠 z
  refine ⟨mul_ne_zero (Units.ne_zero _) (Finset.prod_ne_zero_iff.2 fun v hv => ?_), fun k hk => ?_⟩
  · have hv' : v.1 ∈ X.T := by simpa using hv
    have hc : Continuous X.ν := h.chars.heckeα.1.div' h.chars.heckeβ.1
    refine mul_ne_zero (Units.ne_zero _) (eps_ne_zero (GaussNe.gauss_ne_zero _ _ _ (h.base.psiP _ v.2)
      (continuous_chrW' hc _) (exists_unit_chrW_ne _ (h.chars.ram _ ?_))) z)
    rwa [splitPrime_under]
  · refine (converges_charFam _ X.ν ?_).ne_zero
    rw [Complex.natCast_re]
    exact_mod_cast hk

end PositivityTheory.ThK.Close
