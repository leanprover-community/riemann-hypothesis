module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableReductionPlusSplit
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteDvrTorusExtensionSpecialFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupSchemeModelFiniteRingExtensionStatement
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem exists_semiAbelian_model_torusExtension_of_potModel : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G) → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : IsAdicComplete (IsLocalRing.maximalIdeal V') V') (_ : Algebra V V') (_ : Algebra V' K') (_ : IsFractionRing V' K'), Module.Finite V V' ∧ Function.Injective (algebraMap V V') ∧ (algebraMap V' K').comp (algebraMap V V') = (algebraMap K K').comp (algebraMap V K) ∧ ∃ (G : Over (Spec (CommRingCat.of V'))) (_ : GrpObj G), IsSemiAbelian G ∧ (∃ e : baseChange V' K' G ≅ baseChange K K' A, IsMonHom e.hom) ∧ Nonempty (TorusExtension (specialFibre V' G)) := by
  intro V _ _ _ _ K _ _ _ _ A _ hP
  obtain ⟨W, L, _, _, _, _, _, _, _, _, e, hfin, -, hW, G, _, hmod, hG⟩ := hP
  have hinj : Function.Injective (algebraMap V W) := by
    have h : Function.Injective ((algebraMap W L).comp (algebraMap V W)) := by
      rw [e]; exact (algebraMap K L).injective.comp (IsFractionRing.injective V K)
    exact Function.Injective.of_comp (f := algebraMap W L) h
  haveI hKL : FiniteDimensional K L := by
    letI : Algebra V L := ((algebraMap W L).comp (algebraMap V W)).toAlgebra
    haveI : IsScalarTower V W L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq' e
    haveI : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 hinj
    exact Module.Finite.of_isLocalization V W (nonZeroDivisors V)
  obtain ⟨W', _, _, _, hW', _, hfin', hinj', -, hG', hT⟩ := GlobalTheory.T.exists_finite_dvr_torusExtension_specialFibre' W G hG
  obtain ⟨_, hK', e', hmod'⟩ := GlobalTheory.T.groupScheme_model_finite_ring_extension V K A L W e G hmod W' hfin' hinj'
  letI : Algebra V W' := ((algebraMap W W').comp (algebraMap V W)).toAlgebra
  haveI : IsScalarTower V W W' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨FractionRing W', inferInstance, inferInstance, hK', W', inferInstance, inferInstance, inferInstance, hW',
    inferInstance, inferInstance, inferInstance, Module.Finite.trans W W', hinj'.comp hinj, e',
    baseChange W W' G, inferInstance, hG', hmod', hT⟩

end GlobalTheory.SS
