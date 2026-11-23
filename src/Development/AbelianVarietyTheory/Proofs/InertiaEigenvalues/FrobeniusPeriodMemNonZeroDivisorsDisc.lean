module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisinStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinAinfDiscIsDomainNormBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinNormEisensteinLeRadiusStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopBasisDiscRegularStatement
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem per_ne_zero {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) {τ : Ainf l} (h : bk.IsPer τ) : τ ≠ 0 := by
  rintro rfl
  obtain ⟨-, ε, η, hε, hφ⟩ := h
  rw [map_zero] at hφ
  have h1 : WittVector.teichmuller l ε - 1 = 0 := (Units.mul_right_eq_zero η).1 hφ.symm
  have h2 : ε = 1 := by
    have := congrArg (fun w => WittVector.coeff w 0) (sub_eq_zero.1 h1)
    simpa using this
  subst h2
  exact hε.2 (by simp)

theorem iA_per_mem_nonZeroDivisors : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l),
    bk.IsPer τ → bk.iA τ ∈ nonZeroDivisors (bk.DA bk.ρ₀) := by
  intro l _ K bk τ hτ
  obtain ⟨h0, h1, -, -⟩ := GlobalTheory.T.breuilKisin_norm_eisenstein_le_radius l K bk (Ainf l) bk.ev
  haveI : IsDomain (bk.DA bk.ρ₀) := (discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ι tb).1
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rw [← map_zero bk.iA]
  exact fun h => per_ne_zero bk hτ (hinj h)

end GlobalTheory.BSP
