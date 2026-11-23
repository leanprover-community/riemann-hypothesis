module

public import Formalism.SharpRestriction.LevelLetterCocycles.SmallTwists.RowSmall
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace UpperTheory.N

def costC {D : D7} (L : SizeData₂ D) (A B : ℝ) (l : ℕ) : ℝ :=
  A * D.R.f * D.R.m * RowSmall.hB L * (RowSmall.sl D l : ℝ) +
    B * (D.R.f : ℝ) ^ 2 * (D.R.t : ℝ) ^ 2 * D.R.nV * RowSmall.abelian₂ L l

def RowAt {D : D7} (L : SizeData₂ D) (ρ : FamilyRepresentationConstants.RhoFam D) (A B : ℝ) : Prop :=
  ∀ k, TwistedPlaces.TwLoc D k → D.nd.l k ∈ D.host.small → D.nd.l k ≠ 2 → ∀ π ∈ D.nd.Zgood k, Bd ρ k π (costC L A B (D.nd.l k))

end UpperTheory.N

end
