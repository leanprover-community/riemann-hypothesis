module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapAcrFromBase
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GalOCOkToOC
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.JEqPdPow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowersOnFiltration
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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.Pb

theorem redIn_ex : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {A : Type} [CommRing A] [Algebra (OK l K) A]
    {I : Ideal A} (γ : DividedPowers I) (s : ℕ) (lam : Acris l →+* A), TFBase γ l s →
    lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ I →
    (∀ (a : OK l K) (w : Ainf l), theta0 l w = okToOC l K a → algebraMap (OK l K) A a - lam (algebraMap (Ainf l) (Acris l) w) ∈ I) →
    ∀ n : ℕ, ∃ d : RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) γ l n,
      ∀ c, d.ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (lam c) := @GlobalTheory.CompanionTheory.RedInEx.redIn_ex

end CrystallineSemistableComparison.Pb
