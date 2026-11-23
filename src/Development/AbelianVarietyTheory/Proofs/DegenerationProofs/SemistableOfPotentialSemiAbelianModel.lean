module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.PlusConditionToZeroCondition
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianTorusExtensionOfPotentialModelStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyTorusExtOfSplit
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem semistable_of_potModel_semiAbelian : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G)) → SemistableReductionZero ∧ SemistableCompleteSplit := by
  intro h
  refine ⟨?_, ?_⟩
  · intro V _ _ _ _ K _ _ _ _ A _ hA
    obtain ⟨K', i1, i2, i3, V', i4, i5, i6, i7, i8, i9, i10, h1, h2, h3, G, i11, hG, he, hT⟩ :=
      GlobalTheory.T.exists_semiAbelian_torusExtension_of_potentialModel V K A (h V K A hA)
    exact ⟨K', i1, i2, i3, V', i4, i5, i6, i8, i9, i10, h1, h2, h3, G, i11,
      hG.comm, hG.smooth, hG.separated, hG.quasiCompact, he, GlobalTheory.SplitExtTorus.nonempty_torusExt_of_split _ _ hT⟩
  · intro V _ _ _ _ K _ _ _ _ A _ hA
    obtain ⟨K', i1, i2, i3, V', i4, i5, i6, i7, i8, i9, i10, h1, h2, h3, G, i11, hG, he, hT⟩ :=
      GlobalTheory.T.exists_semiAbelian_torusExtension_of_potentialModel V K A (h V K A hA)
    exact ⟨K', i1, i2, i3, V', i4, i5, i6, i7, i8, i9, i10, inferInstance, h3, G, i11, hG, he, hT⟩

end GlobalTheory.SS
