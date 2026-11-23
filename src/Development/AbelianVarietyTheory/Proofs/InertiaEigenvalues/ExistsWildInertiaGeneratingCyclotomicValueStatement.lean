module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWildInertiaGeneratingCyclotomicValue
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

theorem _root_.GlobalTheory.T.exists_wildInertia_generating_cyclotomicValue : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → ∃ g0 : GE D.nd, (∃ w ∈ placesOver D.host.E (D.nd.l i), g0 ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) ∧ (∃ u : ℤ_[D.nd.l i]ˣ, ((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g0 : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) = 1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ D.nd.s0 i * (u : ℤ_[D.nd.l i])) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), g0 ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) → g0 ∈ wildSet D.nd (D.nd.plOm.1 w) := by
  first | exact @GlobalTheory.WildCycGen.main | exact GlobalTheory.WildCycGen.main | (intros; apply GlobalTheory.WildCycGen.main <;> assumption)
