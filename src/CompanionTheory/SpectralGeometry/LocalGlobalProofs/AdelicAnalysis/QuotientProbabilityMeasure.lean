module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArithmeticUnitaryGroupDiscreteStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteCovolumeUnimodular
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolumeStatement
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.BB

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem isProbabilityMeasure_prH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsProbabilityMeasure (prH μ 𝓕) := by
  intro F E _ _ _ _ _ σ hσ M J hJ μ 𝓕 hμ h𝓕
  have hfin : μ 𝓕 < ⊤ := ((GlobalTheory.T.unitary_group_finite_volume F E σ hσ M J hJ).2 μ hμ).2 𝓕 h𝓕
  obtain ⟨hlc, hsc, ht2⟩ := (GlobalTheory.CompanionTheory.AdeleTop.adele_top F).1
  obtain ⟨htg, hlcH, hscH, ht2H, hbor, -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  have hcount : Countable (HFinIn (AF F) σ J) := (GlobalTheory.T.arithmetic_unitary_group_discrete F E σ hσ M J hJ).1
  have hne : μ 𝓕 ≠ 0 :=
    (@GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain (HA (AF F) σ J) _ _ htg ht2H hlcH hscH _ hbor
      (HFinIn (AF F) σ J) hcount μ hμ 𝓕 h𝓕 hfin).1
  refine ⟨?_⟩
  simp only [prH, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hne hfin.ne

end GlobalTheory.CompanionTheory.SW.BB
