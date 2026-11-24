module

public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPadicEmbeddingLeOneOfMemInverseHalfDifferent
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Classical

namespace GlobalTheory.EigenGenerator

theorem norm_dgen_eq_one : ∀ (D : D7) (cD : D.what₂.Tau → ℂ), Formalism.L2.Ker.IsDgen D cD → ∀ (p : ℕ) [Fact p.Prime] (lm : Qbar →+* ℂ_[p]), p = D.host.d → ∀ τ, ‖lamC lm (cD τ)‖ = 1 := by
  intro D cD hD p _ lm hp τ
  obtain ⟨M, hMnf, hM, hs⟩ := hD
  obtain ⟨s, hsc, hsp⟩ := hs τ
  have hh := D.host.hyp
  unfold Formalism.FrobeniusOrbits.HostHyp at hh
  have h2 : p ∉ D.host.small := hp ▸ UpperTheory.Small.d_not_mem D.host
  have hq : p ≠ D.host.q := by omega
  rw [← hsc]
  exact norm_generator_eq_one D p lm h2 hq M hM τ s hsp

end GlobalTheory.EigenGenerator
