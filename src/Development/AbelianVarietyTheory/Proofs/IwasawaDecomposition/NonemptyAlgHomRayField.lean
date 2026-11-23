module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsModulusTopOfIsTotallyComplex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem.Fld

namespace GlobalTheory.UnramInRay

theorem isModulus_of_top {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {χ : (L ≃ₐ[K] L) →* ℂˣ} (h : IsModulus L χ ⊤) {𝔪 : Ideal (𝓞 K)} (hm : 𝔪 ≠ ⊥) : IsModulus L χ 𝔪 := by
  refine ⟨hm, fun 𝔭 _ => h.2.1 𝔭 fun hd => 𝔭.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd hd)), ?_⟩
  rintro α β ⟨ha, hb, -, -, -, hpos⟩
  have hc : ∀ I : Ideal (𝓞 K), IsCoprime I ⊤ := fun I => Ideal.isCoprime_iff_sup_eq.2 (sup_top_eq I)
  exact h.2.2 α β ⟨ha, hb, hc _, hc _, Submodule.mem_top, hpos⟩

theorem nonempty_algHom_rayField : GlobalArtinReciprocity → ∀ (K L R : Type) [Field K] [NumberField K]
    [_root_.NumberField.IsTotallyComplex K] [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] [Field R] [NumberField R]
    [Algebra K R] (𝔪 : Ideal (𝓞 K)), 𝔪 ≠ ⊥ → IsRayField K R 𝔪 →
    (∀ 𝔭 : HeightOneSpectrum (𝓞 K), UnramIn L 𝔭) → Nonempty (L →ₐ[K] R) := by
  intro H K L R _ _ _ _ _ _ _ _ _ _ 𝔪 hm hR hL
  have := hR.1
  exact rayClassFieldMaximalSt_holds K R L 𝔪 hm hR.2 fun χ =>
    isModulus_of_top (GlobalTheory.UnramModulus.isModulus_top H K L hL χ) hm

end GlobalTheory.UnramInRay

end
