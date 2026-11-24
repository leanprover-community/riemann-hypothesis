module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.PushforwardPreservesSelmerCocycles
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.CardKerRangeAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.UnrLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.arUr :
    CohP → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 V : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (u : (locOf r).St), UrAx l ((locOf r).Ju u) := by
  intro _ l _ L Ω _ _ _ _ _ _ s V0 _ O _ _ _ _ _ n r u
  exact UpperTheory.V.Pa.B2.urOf l _ _ (UpperTheory.V.Pa.unrLoc l L Ω s V0 O n r u)
