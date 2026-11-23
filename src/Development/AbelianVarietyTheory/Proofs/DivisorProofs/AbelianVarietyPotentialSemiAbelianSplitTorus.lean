module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteDvrTorusExtensionSpecialFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupSchemeModelFiniteRingExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLocalHomAndIsAdicCompleteOfFiniteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NumberFieldStandardFacts
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableReductionZero
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.SS

theorem potModel_semiAbelian_torusExtension : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G ∧ Nonempty (TorusExtension (GlobalTheory.SS.spFibre G))) := by
  intro V K _ _ _ _ _ _ _ _ A _ hA
  obtain ⟨K', _, _, _, V', _, _, _, _, _, _, hfin, hinj, hcomm, G, _, hc, hsm, hsep, hqc, he, hT⟩ :=
    GlobalTheory.SS.semistableReduction_zero V K A hA
  obtain ⟨hloc, hcpl⟩ := GlobalTheory.isLocalHom_and_isAdicComplete_of_finite_dvr V V' hfin hinj
  haveI := hcpl
  have hA' : IsAbelianScheme (baseChange K K' A) := Out.TLinPf.isAb_pullback _ A hA
  have hG : IsSemiAbelian G :=
    GlobalTheory.SS.isSemiAbelian_of_abelian_generic_of_torusExt V' K' (baseChange K K' A) hA' G hc hsm hsep hqc he hT
  obtain ⟨V'', _, _, _, hcpl', _, hfin', hinj', hloc', hG', hT'⟩ :=
    GlobalTheory.exists_finite_dvr_torusExtension_specialFibre V' G hG
  obtain ⟨alg, hfd, hcomm', he'⟩ := GlobalTheory.SS.model_finite_ext V K A K' V' hcomm G he V'' hfin' hinj'
  let : Algebra V V'' := ((algebraMap V' V'').comp (algebraMap V V')).toAlgebra
  have : IsScalarTower V V' V'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfinV : Module.Finite V V'' := Module.Finite.trans V' V''
  have hlocV : IsLocalHom (algebraMap V V'') := by
    haveI := hloc; haveI := hloc'
    exact (inferInstance : IsLocalHom ((algebraMap V' V'').comp (algebraMap V V')))
  exact ⟨V'', FractionRing V'', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, alg, inferInstance, hcomm', hfinV, hlocV, hcpl', baseChange V' V'' G, inferInstance, he', hG', hT'⟩

end GlobalTheory.SS
