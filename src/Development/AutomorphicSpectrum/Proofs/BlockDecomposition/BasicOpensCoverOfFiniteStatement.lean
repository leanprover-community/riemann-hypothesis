module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpensCoverOfFinite
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.basic_opens_cover_of_finite : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), ∀ {m e : ℕ}, 0 < e → ∀ (y : Fin m → MvPolynomial (Fin (N + 1)) K), (∀ k, (y k).IsHomogeneous e) → Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k))) (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i) → ⨆ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GeoCover.iSup_preimage_eq_top | exact GlobalTheory.CompanionTheory.GeoCover.iSup_preimage_eq_top | (intros; apply GlobalTheory.CompanionTheory.GeoCover.iSup_preimage_eq_top <;> assumption)
