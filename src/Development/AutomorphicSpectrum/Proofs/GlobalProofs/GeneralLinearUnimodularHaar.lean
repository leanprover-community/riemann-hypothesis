module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeneralLinearIntegralCompactOpenStatement
public import GroundTheory.AutomorphicForms.MeasuresGL
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
import Mathlib.Tactic.Linter.HaveILetI
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

open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.HaarGL

theorem exists_haar_unimodular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n : ℕ, (∃ κ : Measure (GL (Fin n) F), κ.IsMulLeftInvariant ∧ κ (GLint O n : Set (GL (Fin n) F)) = 1) ∧ ∀ μ : Measure (GL (Fin n) F), μ.IsHaarMeasure → μ.IsMulRightInvariant ∧ μ.IsInvInvariant := by
  intro F _ _ _ _ O ϖ nrm q hLF n
  obtain ⟨hKo, hKc, hlc, _hsc, ht2, -, -⟩ := GlobalTheory.T.generalLinear_integral_compact_open hLF n
  haveI := hlc
  haveI := ht2
  haveI : BorelSpace (GL (Fin n) F) := GlobalTheory.CompanionTheory.QL.instBorelGL n
  refine ⟨?_, fun μ hμ => ?_⟩
  · let μ₀ : Measure (GL (Fin n) F) := Measure.haar
    have hpos : μ₀ (GLint O n : Set (GL (Fin n) F)) ≠ 0 :=
      hKo.measure_ne_zero μ₀ ⟨1, (GLint O n).one_mem⟩
    have hfin : μ₀ (GLint O n : Set (GL (Fin n) F)) ≠ ⊤ := hKc.measure_lt_top.ne
    refine ⟨(μ₀ (GLint O n : Set (GL (Fin n) F)))⁻¹ • μ₀, inferInstance, ?_⟩
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin]
  · haveI := hμ
    exact ⟨GroundTheory.Automorphic.Measures.isMulRightInvariant_GL F n μ,
      ⟨GroundTheory.Automorphic.Measures.inv_eq_self_GL F n μ⟩⟩

end GlobalTheory.CompanionTheory.QL.HaarGL
