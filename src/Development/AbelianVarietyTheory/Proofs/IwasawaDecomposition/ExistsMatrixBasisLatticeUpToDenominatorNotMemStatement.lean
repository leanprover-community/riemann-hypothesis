module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMatrixBasisLatticeUpToDenominatorNotMem
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

open NumberField IsDedekindDomain Matrix
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_matrix_basis_lattice_up_to_denominator_notMem : ∀ (K : Type) [Field K] [NumberField K] (n : Type) [Fintype n] [DecidableEq n] (L : Submodule (𝓞 K) (n → K)) (𝔭 : HeightOneSpectrum (𝓞 K)), L.FG → Submodule.span K (L : Set (n → K)) = ⊤ → ∃ g : Matrix n n K, IsUnit g.det ∧ ∃ t : 𝓞 K, t ∉ 𝔭.asIdeal ∧ (∀ x ∈ L, ∀ i, (t : K) * (g⁻¹ *ᵥ x) i ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ j, (t : K) • (fun i => g i j) ∈ L := by
  first | exact @GlobalTheory.LatticeLocBasis.exists_matrix_up_to_notMem | exact GlobalTheory.LatticeLocBasis.exists_matrix_up_to_notMem | (intros; apply GlobalTheory.LatticeLocBasis.exists_matrix_up_to_notMem <;> assumption)
