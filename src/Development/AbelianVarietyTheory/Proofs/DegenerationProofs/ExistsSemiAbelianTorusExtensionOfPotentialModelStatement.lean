module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableReductionPlusSplit
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianTorusExtensionOfPotentialModel
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

theorem _root_.GlobalTheory.T.exists_semiAbelian_torusExtension_of_potentialModel : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G) → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : IsAdicComplete (IsLocalRing.maximalIdeal V') V') (_ : Algebra V V') (_ : Algebra V' K') (_ : IsFractionRing V' K'), Module.Finite V V' ∧ Function.Injective (algebraMap V V') ∧ (algebraMap V' K').comp (algebraMap V V') = (algebraMap K K').comp (algebraMap V K) ∧ ∃ (G : Over (Spec (CommRingCat.of V'))) (_ : GrpObj G), IsSemiAbelian G ∧ (∃ e : baseChange V' K' G ≅ baseChange K K' A, IsMonHom e.hom) ∧ Nonempty (TorusExtension (specialFibre V' G)) := by
  first | exact @GlobalTheory.SS.exists_semiAbelian_model_torusExtension_of_potModel | exact GlobalTheory.SS.exists_semiAbelian_model_torusExtension_of_potModel | (intros; apply GlobalTheory.SS.exists_semiAbelian_model_torusExtension_of_potModel <;> assumption)
