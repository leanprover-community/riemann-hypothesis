module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
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
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.cech_refinement_cohomology_bijective : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : Used Q₀)
    (𝒱 𝒲 : Set X.Opens) (h : St Q₀ 𝒱 ≤ St Q₀ 𝒲) (hc : ∀ W ∈ 𝒲, W ≤ sSup 𝒱) (j : ℕ),
    (∀ r r' : ℤ, Function.Bijective (((incl h).sq (incl_fil h r) (incl_fil h r')).pull j)) ∧
    (∀ (r r' : Option ℤ) (c c' : R), Function.Bijective (((incl h).sq (incl_std h r c) (incl_std h r' c')).pull j)) ∧
    Function.Bijective ((incl h).o.pull j) := by
  first | exact @GlobalTheory.CompanionTheory.NlZar.zariski_descent | exact GlobalTheory.CompanionTheory.NlZar.zariski_descent | (intros; apply GlobalTheory.CompanionTheory.NlZar.zariski_descent <;> assumption)
