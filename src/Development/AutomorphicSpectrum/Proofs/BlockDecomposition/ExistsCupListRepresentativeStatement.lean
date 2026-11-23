module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCupListRepresentative
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

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.exists_cup_list_representative : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A),
    IsFil Φ Fil → ∀ {m : ℕ} (ℓ : Fin m → CH.Cn (CH.modF Φ.A) 1), (∀ k, CH.d _ 1 (ℓ k) = 0) → (∀ k σ, ℓ k σ ∈ (Fil 1).S _) →
    ∃ c : CH.H (sq (Fil m) (Fil ((m : ℤ) + 1))) m, Rep (Fil m) (Fil ((m : ℤ) + 1)) (cupListC Φ.A ℓ) c := by
  first | exact @GlobalTheory.CompanionTheory.ConeRepCup.exists_rep | exact GlobalTheory.CompanionTheory.ConeRepCup.exists_rep | (intros; apply GlobalTheory.CompanionTheory.ConeRepCup.exists_rep <;> assumption)
