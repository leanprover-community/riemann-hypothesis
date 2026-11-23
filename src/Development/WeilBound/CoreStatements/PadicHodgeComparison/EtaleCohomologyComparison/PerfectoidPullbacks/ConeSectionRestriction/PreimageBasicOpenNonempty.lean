module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpenNonemptyOfNeZeroStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealComponentMemStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealNeTopStatement
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N)

theorem homIdeal_homog : ∀ f ∈ homIdeal i, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ homIdeal i := by
  first
    | exact GlobalTheory.T.homogeneous_ideal_component_mem ..
    | (intros; apply GlobalTheory.T.homogeneous_ideal_component_mem <;> assumption)

theorem homIdeal_ne_top [Nonempty X] : homIdeal i ≠ ⊤ := by
  first
    | exact GlobalTheory.T.homogeneous_ideal_ne_top ..
    | (intros; apply GlobalTheory.T.homogeneous_ideal_ne_top <;> assumption)

theorem preimage_basicOpen_nonempty [IsIntegral X] {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (he : 0 < e)
    (hg : g ∈ grK K N e) (hg0 : Ideal.Quotient.mk (homIdeal i) g ≠ 0) :
    ((i ⁻¹ᵁ Proj.basicOpen (grK K N) g : X.Opens) : Set X).Nonempty := by
  first
    | exact GlobalTheory.T.basic_open_nonempty_of_ne_zero ..
    | (intros; apply GlobalTheory.T.basic_open_nonempty_of_ne_zero <;> assumption)

end CrystallineSemistableComparison.Pb
