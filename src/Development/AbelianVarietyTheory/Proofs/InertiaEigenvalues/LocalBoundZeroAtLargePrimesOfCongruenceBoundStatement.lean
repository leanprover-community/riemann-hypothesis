module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.JumpDictionary
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundZeroAtLargePrimesOfCongruenceBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.localBoundZeroAtLargePrimes_of_congruenceBound : ∀ (D : D7) (L : SizeData₂ D) (r : FamilyRepresentationConstants.RFam D) (ρ : FamilyRepresentationConstants.RhoFam D) (exc : Finset ℕ), GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.CongBound_at D L → GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D → GlobalTheory.PtCore.PtFam D r ρ → KillingConditions.KillAt ρ → TwistedPlaces.ShaFinOdd D → 3 ≤ TwistedPlaces.lStar L → (exc : Set ℕ) = GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc L → StarE L ρ exc := by
  first | exact @GlobalTheory.NLink.RowE.main | exact GlobalTheory.NLink.RowE.main | (intros; apply GlobalTheory.NLink.RowE.main <;> assumption)
