module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLatticesFormSelfDualTriples
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

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

theorem _root_.GlobalTheory.T.kernelLattices_form_selfDual_triples : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ A : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A → Nice D (tor0 D cc δ) A) ∧ (∀ A₁ A₂ : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → ∀ e ∈ ThSp D (tor0 D cc δ) A₁, e ≠ 0 → (A₁.addSubgroupOf A₂).index ≠ 0) ∧ (∀ A : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A → ∀ e ∈ ThSp D (tor0 D cc δ) A, Iop D (tor0 D cc δ) A A e = e) ∧ ∀ A₁ A₂ A₃ : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → KLat D (tor0 D cc δ) A₃ → ∀ e ∈ ThSp D (tor0 D cc δ) A₁, e ≠ 0 → ∃ μ, Trip D (tor0 D cc δ) A₁ A₂ A₃ e μ := by
  first | exact @GlobalTheory.ThetaTriple.klat_triples | exact GlobalTheory.ThetaTriple.klat_triples | (intros; apply GlobalTheory.ThetaTriple.klat_triples <;> assumption)
