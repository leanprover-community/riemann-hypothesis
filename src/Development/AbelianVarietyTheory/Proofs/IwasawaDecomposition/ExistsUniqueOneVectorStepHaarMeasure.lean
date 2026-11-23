module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueStdHermitianFibreProductOfRankGeThreStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdHermitianFibreMeasureInvariantOrbitFiniteNonzStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemenStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilFormulaHaarOrbitStabilizerStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem exists_unique_stepRel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (μ' : Measure (HA (AF F) σ J')), 2 ≤ M → StepData σ J x a B J' → μ'.IsHaarMeasure → (∃ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure ∧ StepRel s σ J x a B J' μ μ') ∧ ∀ μ₁ μ₂ : Measure (HA (AF F) σ J), StepRel s σ J x a B J' μ₁ μ' → StepRel s σ J x a B J' μ₂ μ' → μ₁ = μ₂ := by
  intro F E _ _ _ _ _ σ hcm d b s M J x a B J' μ' hM hsd hμ'
  have : FiniteDimensional F E := Module.Finite.of_basis b
  obtain ⟨ν, hν, hνu⟩ := GlobalTheory.T.existsUnique_stdHermitianFibreProduct_of_rank_ge_three F E σ hcm d b s (M + 1) J a (by omega) hsd.1 hsd.2.1
  obtain ⟨-, ⟨e, he, heu⟩, hcont⟩ := GlobalTheory.T.unitary_stabilizer_anisotropic_vector_equiv_complement F E σ hcm (AF F) M J x a B J' hsd
  obtain ⟨-, hinv, horb, hfin, hne⟩ :=
    GlobalTheory.T.stdHermitianFibreMeasure_invariant_orbit_finite_nonzero F E σ hcm d b s (M + 1) J x a ν hsd.1 hsd.2.1 hsd.2.2.1 hν
  obtain ⟨hc1, hc2⟩ := hcont e he
  constructor
  · have : (μ'.map e.symm).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ' e.symm hc2 hc1
    obtain ⟨μ, hμ, hint⟩ := GlobalTheory.T.weil_formula_haar_orbit_stabilizer (HA (AF F) σ J) (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)
      (ratTup (F := F) (AF F) x) (μ'.map e.symm) ν this hfin hne hinv horb
    refine ⟨μ, hμ, fun ν' hν' e' he' => ?_⟩
    obtain rfl := hνu ν' hν'
    obtain rfl := heu e' he'
    exact hint
  · intro μ₁ μ₂ h₁ h₂
    have k₁ := h₁ ν hν e he
    have k₂ := h₂ ν hν e he
    classical
    let t : (Fin 1 → Fin (M + 1) → AF F ⊗[F] E) → HA (AF F) σ J := fun y =>
      if h : ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y then h.choose else 1
    have ht : ∀ y, (∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y) →
        t y • ratTup (F := F) (AF F) x = y := fun y hy => by
      simp only [t, dif_pos hy]
      exact hy.choose_spec
    exact Measure.ext_of_lintegral _ fun f hf => (k₁ f hf t ht).trans (k₂ f hf t ht).symm

end GlobalTheory.GaugeEx
