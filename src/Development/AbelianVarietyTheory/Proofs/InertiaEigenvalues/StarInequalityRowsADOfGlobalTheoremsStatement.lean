module

public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarInequalityRowsADOfGlobalTheorems
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.starInequality_rowsAD_of_global_theorems : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK), KillingConditions.DataAD L HW X R → KillingConditions.StepAD L X → TruncatedSeriesCountingIdentities.IntegralityFromMetric D → (∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ep : Bool) (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ), EmbeddingTypes.admitted i r ρ π dc ep e' c0 cB → (D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π) → EmbeddingTypes.aux₃ i r ρ π dc ep e' c0 cB) → (∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.admG2 i (X.r i) (X.ρ i) π) → KillingConditions.KillAt X.ρ → TwistedPlaces.ShaFinOdd D → KillingConditions.StarAD L X := by
  first | exact @GlobalTheory.NLink.starAD_of_global | exact GlobalTheory.NLink.starAD_of_global | (intros; apply GlobalTheory.NLink.starAD_of_global <;> assumption)
