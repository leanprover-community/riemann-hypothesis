module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice
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

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaLattice_image_rationalHomLattice : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), δ ≠ 0 → ∀ (N N' : ℕ), Function.Injective (pt D (tor0 D cc δ) δ : Matrix (Fin N') (Fin N) D.host.E → VC D N N') ∧ (∀ (L : Lat D N) (L' : Lat D N') (x : VC D N N'), x ∈ La D (tor0 D cc δ) L L' ↔ ∃ z ∈ RL D cc L L', x = pt D (tor0 D cc δ) δ z) ∧ (∀ (L' : Lat D N') (z : Matrix (Fin N') (Fin N) D.host.E), z ∈ RL D cc (stdL D N) L' ↔ ∀ j, (fun i => z i j) ∈ Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L', v = t • y}) ∧ ∀ (L : Lat D N), SD D L → ∀ (z : Matrix (Fin N') (Fin N) D.host.E), z ∈ RL D cc L (stdL D N') ↔ ∀ i, z i ∈ Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L, v = t • fun j => D.host.conj (y j)} := by
  first | exact @GlobalTheory.ThetaLatImage.theta_lattice_image | exact GlobalTheory.ThetaLatImage.theta_lattice_image | (intros; apply GlobalTheory.ThetaLatImage.theta_lattice_image <;> assumption)
