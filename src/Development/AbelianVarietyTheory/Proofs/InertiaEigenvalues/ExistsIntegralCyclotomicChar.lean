module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Cyc

theorem exists_integral_cyclotomicChar : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∃ χ : GQ l →* ℤ_[l]ˣ, (∀ g, (((χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = (P.χQ g : ℚ_[l])) ∧ Continuous χ ∧ ∀ (K : FinExt l) (s : ℕ), K.1 ≤ Ks K s → ∀ u : ℤ_[l]ˣ, (l : ℤ_[l]) ^ s ∣ (u : ℤ_[l]) - 1 → ∃ g ∈ GK K, χ g = u := by
  intro l _ P
  have hχ : IsCyc P.χQ := P.χQ_cyc
  obtain ⟨hn, hc, hK⟩ := cyc_basic l P.χQ hχ
  let f : GQ l →* ℤ_[l] :=
    { toFun := fun g => ⟨(P.χQ g : ℚ_[l]), (hn g).le⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change (P.χQ (a * b) : ℚ_[l]) = (P.χQ a : ℚ_[l]) * (P.χQ b : ℚ_[l])
        rw [map_mul, Units.val_mul]) }
  have hf : Continuous f := hc.subtype_mk _
  refine ⟨f.toHomUnits, fun g => rfl, ?_, ?_⟩
  · rw [Units.continuous_iff]
    exact ⟨hf, hf.comp continuous_inv⟩
  · intro K s hs u hu
    have hu1 : ‖((u : ℤ_[l]) : ℚ_[l])‖ = 1 := PadicInt.norm_units u
    obtain ⟨g, hg, hgu⟩ := exists_chi_eq K P.χQ hχ _ hu1
    have hG : g ∈ Gj K s := ((hK K g hg).1 s).2 (by
      rw [hgu]
      have := (PadicInt.norm_le_pow_iff_mem_span_pow ((u : ℤ_[l]) - 1) s).2
        (Ideal.mem_span_singleton.2 hu)
      rwa [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one] at this)
    refine ⟨g, IntermediateField.fixingSubgroup_antitone hs hG, ?_⟩
    exact Units.ext (Subtype.ext hgu)

end GlobalTheory.Cyc
