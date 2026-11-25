module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilTransportAdelicSchwartzCmExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffOfHeisenbergDerivativeClosedClassStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLinearCoordinatesContinuousKeepPartsStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySchroedingerOpenFiniteSubgr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAdelicThetaTransformSymplecticOfDecay
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtHeisenbergOperatorThetaTransformRealLi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtInverseThetaTransformHeisenbergOnePara
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseAdelicThetaTransformRapidDecay
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseThetaTransformHasLevelCompactFiniteSuppor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicSchwartzSpaceOfLevelCompactSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzInverseThetaTransformOnRealTranslates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformInverseTransformEqQuasiPeriodic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOfThetaHeisenbergTranslates
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CtxExists
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RapidDecayAdelicIntegrablePeriodisationContinuou
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOne
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Mathlib.Tactic.ReduceModChar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCoordinatesRationalMatricesOntoRational, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCoordinatesRationalMatricesOntoRational =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCoordinatesRationalMatricesOntoRational", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf\npublic import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels\nimport Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt\nimport Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Coalgebra.IsFrobenius\nimport Mathlib.RingTheory.PicardGroup\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.TotallySplit\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (incM)
open GlobalTheory.ThetaTransform

theorem GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps : ∀ (D : D7) (m n N : ℕ) (e : Matrix (Fin m) (Fin n) (AE D) ≃ₗ[AF D.host.F] VA D.host.F N), (∀ x : Matrix (Fin m) (Fin n) D.host.E, ∃ y z : Fin N → D.host.F, e (incM D.host.F x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) → ∀ y z : Fin N → D.host.F, ∃ x : Matrix (Fin m) (Fin n) D.host.E, e (incM D.host.F x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := by
  intro D m n N e hrat y z
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  let I : Matrix (Fin m) (Fin n) D.host.E →ₗ[D.host.F] Matrix (Fin m) (Fin n) (AE D) :=
    (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).toLinearMap.mapMatrix
  have hI : ∀ x, I x = incM D.host.F x := fun x => rfl
  let L : Matrix (Fin m) (Fin n) D.host.E →ₗ[D.host.F] VA D.host.F N := (e.toLinearMap.restrictScalars D.host.F).comp I
  have hL : ∀ x, L x = e (incM D.host.F x) := fun x => rfl
  let r : (Fin N → D.host.F) →ₗ[D.host.F] (Fin N → AF D.host.F) :=
    LinearMap.pi fun i => (Algebra.linearMap D.host.F (AF D.host.F)).comp (LinearMap.proj i)
  let R : ((Fin N → D.host.F) × (Fin N → D.host.F)) →ₗ[D.host.F] VA D.host.F N := LinearMap.prodMap r r
  have hR : ∀ y z, R (y, z) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := fun _ _ => rfl
  have hAinj : Function.Injective (algebraMap D.host.F (AF D.host.F)) := AdeleRing.algebraMap_injective _ _
  have hrinj : Function.Injective r := fun a b h => funext fun i => hAinj (congrFun h i)
  have hRinj : Function.Injective R := fun a b h => Prod.ext (hrinj (congrArg Prod.fst h)) (hrinj (congrArg Prod.snd h))
  have hIinj : Function.Injective I := fun a b h => Matrix.ext fun i j =>
    Algebra.TensorProduct.includeRight_injective hAinj (congrFun (congrFun h i) j)
  have hLinj : Function.Injective L := e.injective.comp hIinj
  have hle : LinearMap.range L ≤ LinearMap.range R := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y', z', h⟩ := hrat x
    exact ⟨(y', z'), by rw [hR, hL, h]⟩
  have hdim : Fintype.card (Fin m) * Fintype.card (Fin n) * Module.finrank D.host.F D.host.E = N + N := by
    have h1 := e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fin_fun] at h1
    exact h1
  have hfin : Module.finrank D.host.F (LinearMap.range L) = Module.finrank D.host.F (LinearMap.range R) := by
    rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hRinj, Module.finrank_matrix,
      Module.finrank_prod, Module.finrank_fin_fun, hdim]
  have heq := Submodule.eq_of_le_of_finrank_eq hle hfin
  obtain ⟨x, hx⟩ : (R (y, z)) ∈ LinearMap.range L := heq ▸ ⟨(y, z), rfl⟩
  exact ⟨x, by rw [← hL, hx, hR]⟩
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCoordinatesRationalMatricesOntoRational =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf\npublic import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero\npublic import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffOfHeisenbergDerivativeClosedClassStatement\npublic import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCoordinatesRationalMatricesOntoRational\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLinearCoordinatesContinuousKeepPartsStatement\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff\npublic import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySchroedingerOpenFiniteSubgr\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAdelicThetaTransformSymplecticOfDecay\npublic import Mathlib.Analysis.LocallyConvex.AbsConvexOpen\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtHeisenbergOperatorThetaTransformRealLi\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtInverseThetaTransformHeisenbergOnePara\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseAdelicThetaTransformRapidDecay\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseThetaTransformHasLevelCompactFiniteSuppor\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicSchwartzSpaceOfLevelCompactSchwartz\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzInverseThetaTransformOnRealTranslates\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformInverseTransformEqQuasiPeriodic\npublic import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOfThetaHeisenbergTranslates\nimport Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CtxExists\nimport Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RapidDecayAdelicIntegrablePeriodisationContinuou\nimport Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOne\nimport Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero\nimport Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators\nimport Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (incM)
open GlobalTheory.ThetaTransform GlobalTheory.SWQ Formalism.IndefR.Datum

noncomputable section

namespace GlobalTheory.ThetaTransform

section Coord

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {N : ℕ}
  {e : WO S T ≃ₗ[AF D.host.F] VA D.host.F N}

theorem heisO_comp (he : ∀ w w', symplO S T w w' = symV (e w) (e w')) (u : WO S T) (f : VA D.host.F N → ℂ) :
    heisO ψ S T u (f ∘ e) = heisV ψ (e u) f ∘ e := by
  funext w
  simp only [heisO, heisV, Function.comp_apply, symplOH, he, map_add (f := _), invOf_two_eq]

theorem heisV_comp_symm (he : ∀ w w', symplO S T w w' = symV (e w) (e w')) (u : VA D.host.F N) (f : WO S T → ℂ) :
    heisV ψ u (f ∘ e.symm) = heisO ψ S T (e.symm u) f ∘ e.symm := by
  funext w
  simp only [heisO, heisV, Function.comp_apply, symplOH, he, map_add (f := _), invOf_two_eq, LinearEquiv.apply_symm_apply]

theorem isThetaFunO_thV (hψ : IsStdChar D ψ (-1)) (he : ∀ w w', symplO S T w w' = symV (e w) (e w'))
    (hrat : ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : Fin N → D.host.F,
      e (incM D.host.F x) = (rat y, rat z))
    {Φ : (Fin N → AF D.host.F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin N)) :
    IsThetaFunO ψ S T (thV ψ Φ ∘ e) := by
  have hR : IsTotallyReal D.host.F := inferInstance
  obtain ⟨hc, -, hfin, hinf⟩ := GlobalTheory.T.adelicLinearCoordinates_continuous_keep_parts D T.rank S.rank N e
  have hcont : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin N), Continuous (thV ψ Φ ∘ e) := fun Φ hΦ =>
    (_root_.GlobalTheory.ThetaTransform.continuous_thV D.host.F N ψ hR hψ.1 Φ (_root_.GlobalTheory.SchwartzDecay.decay_of_mem_schA D.host.F N Φ hΦ)).comp hc
  refine ⟨fun γ w => ?_, ?_, hcont Φ hΦ, ?_⟩
  · obtain ⟨y, z, h⟩ := hrat γ
    have h' : e (ratW T S γ) = (rat y, rat z) := h
    simp only [Function.comp_apply, map_add (f := _), symplOH, he, h', ← invOf_two_eq]
    exact quasiV_thV ψ hψ.1.2.2.1 Φ y z (e w)
  · obtain ⟨U, hUo, hU⟩ := _root_.GlobalTheory.WeilLevel.schA_level D.host.F N ψ hR hψ.1 Φ hΦ
    refine ⟨U.comap e.toLinearMap.toAddMonoidHom, hUo.preimage hc, fun u hu h0 => ?_⟩
    rw [heisO_comp he, ← thV_schr, hU (e u) hu ((hinf u).1 h0).1 ((hinf u).1 h0).2]
  · refine GlobalTheory.T.contDiff_of_heisenbergDerivativeClosedClass D ψ hψ S T {f | ∃ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin N), f = thV ψ Φ ∘ e} ?_ ?_ _ ⟨Φ, hΦ, rfl⟩
    · rintro _ ⟨Φ, hΦ, rfl⟩
      apply hcont Φ hΦ
    · rintro _ ⟨Φ, hΦ, rfl⟩ M hM hM0
      obtain ⟨Φ', hΦ', hd⟩ := _root_.GlobalTheory.ThetaTransform.hasDerivAt_heisV_line D.host.F N ψ hR hψ.1 Φ hΦ (e.toLinearMap.toAddMonoidHom.comp M)
        ⟨hc.comp hM, fun t => (hfin _).1 (hM0 t)⟩
      refine ⟨_, ⟨Φ', hΦ', rfl⟩, fun w => ?_⟩
      simp only [heisO_comp he]
      exact hd (e w)

theorem exists_thV_eq (hψ : IsStdChar D ψ (-1)) (he : ∀ w w', symplO S T w w' = symV (e w) (e w'))
    (hrat : ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : Fin N → D.host.F,
      e (incM D.host.F x) = (rat y, rat z))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∃ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin N), thV ψ Φ ∘ e = f := by
  have hR : IsTotallyReal D.host.F := inferInstance
  obtain ⟨-, hc, hfin, hinf⟩ := GlobalTheory.T.adelicLinearCoordinates_continuous_keep_parts D T.rank S.rank N e
  obtain ⟨lam, ν, hC⟩ := GlobalTheory.SWQ.ctx_exists D.host.F hR ψ hψ.1 N (half D.host.F N) half_ne_zero
  obtain ⟨-, -, -, -, 𝓓, -, hD, h1⟩ := GlobalTheory.SWQ.rat_lattice_fundamentalDomain D.host.F N ν hC.2.2.2.1
  let 𝒱 : Set (VA D.host.F N → ℂ) := {g | ∃ f, IsThetaFunO ψ S T f ∧ g = f ∘ e.symm}
  have hV : ∀ g ∈ 𝒱, Continuous g ∧ QuasiV ψ g ∧ ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C := by
    rintro _ ⟨f, hf, rfl⟩
    refine ⟨hf.cont.comp hc, fun a b w => ?_, ?_⟩
    · obtain ⟨x, hx⟩ := _root_.GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps D T.rank S.rank N e hrat a b
      have hx' : e.symm (rat a, rat b) = ratW T S x := by rw [← hx]; exact e.symm_apply_apply _
      have hx'' : e (ratW T S x) = (rat a, rat b) := hx
      simp only [Function.comp_apply, map_add (f := _), hx', hf.quasi, symplOH, he, hx'', invOf_two_eq,
        LinearEquiv.apply_symm_apply]
    · obtain ⟨C, hC⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf
      exact ⟨C, fun w => hC _⟩
  have hder : ∀ g ∈ 𝒱, ∀ M : ℝ →+ VA D.host.F N, IsRealLine M → ∃ g' ∈ 𝒱, ∀ x,
      HasDerivAt (fun t : ℝ => invV ψ ν 𝓓 (heisV ψ (M t) g) x) (invV ψ ν 𝓓 g' x) 0 := by
    rintro _ ⟨f, hf, rfl⟩ M hM
    let L : ℝ →+ WO S T := e.symm.toLinearMap.toAddMonoidHom.comp M
    have hL : Continuous L := hc.comp hM.1
    have hL0 : ∀ t, (L t).map (finPart D) = 0 := fun t => (hfin _).2 (by
      have : e (L t) = M t := e.apply_symm_apply _
      rw [this]; exact hM.2 t)
    have hf' := (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ hL hL0 hf).2
    refine ⟨_, ⟨_, hf', rfl⟩, ?_⟩
    obtain ⟨c1, -, C₁, hC₁⟩ := hV _ ⟨f, hf, rfl⟩
    obtain ⟨c2, -, C₂, hC₂⟩ := hV _ ⟨_, hf', rfl⟩
    refine _root_.GlobalTheory.ThetaTransform.hasDerivAt_invV_heisV D.host.F N ψ lam ν hC 𝓓 hD h1 _ _ (max C₁ C₂) c1 c2 (fun w => (hC₁ w).trans (le_max_left _ _))
      (fun w => (hC₂ w).trans (le_max_right _ _)) M hM.1 fun w s => ?_
    simp only [heisV_comp_symm he]
    exact GlobalTheory.WeilVacMove.hasDerivAt_line hψ hL hL0 hf (e.symm w) s
  have hmem : f ∘ e.symm ∈ 𝒱 := ⟨f, hf, rfl⟩
  have hlev : LevelV ψ (f ∘ e.symm) := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U.comap e.symm.toLinearMap.toAddMonoidHom, hUo.preimage hc, fun u hu h0 h0' => ?_⟩
    rw [heisV_comp_symm he, hU (e.symm u) hu ((hinf _).2 (by rw [e.apply_symm_apply]; exact ⟨h0, h0'⟩))]
  obtain ⟨hl, hs⟩ := _root_.GlobalTheory.ThetaTransform.invV_level_support D.host.F N ψ lam ν hC 𝓓 hD h1 _ (hV _ hmem).2.1 hlev
  have hS : invV ψ ν 𝓓 (f ∘ e.symm) ∈ GlobalTheory.WeilM.schA D.host.F (Fin N) :=
    _root_.GlobalTheory.LevelSchwartz.mem_schA_of_level D.host.F N _ hl hs (_root_.GlobalTheory.ThetaTransform.schwartz_invV_realTranslate D.host.F N ψ lam ν hC 𝓓 hD h1 𝒱 hV hder
      (_root_.GlobalTheory.InvDecay.invV_decay D.host.F N ψ lam ν hC 𝓓 hD h1 𝒱 (fun g hg => (hV g hg).2) hder) _ hmem)
  refine ⟨_, hS, ?_⟩
  rw [_root_.GlobalTheory.ThetaTransform.thV_invV_eq D.host.F N ψ lam ν hC 𝓓 hD h1 _ (hV _ hmem).1 (hV _ hmem).2.1 (_root_.GlobalTheory.SchwartzDecay.decay_of_mem_schA D.host.F N _ hS)]
  funext w
  simp

end Coord

section Pair

variable {D : D7} {S T : HSp D} {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
  {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E} {ξ : AE D}

theorem symplO_eq_symp (hA : JA = T.gramᵀ) (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹))
    (x y : WO S T) : symplO S T x y =
      GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB) x y :=
  GlobalTheory.TransportF.symplOF_eq_symp hA hB x y

theorem mem_GA_target (hA : JA = T.gramᵀ) (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA)) :
    a.1 ∈ HR (AF D.host.F) D.sp.cm.sig T.gram :=
  GlobalTheory.TransportF.mem_HR_target hA a

variable {ψ : AddChar (AF D.host.F) ℂ} {κ : Type} [Fintype κ]
  (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)

theorem thetaTr_bij (hψ : IsStdChar D ψ (-1)) (hA : JA = T.gramᵀ)
    (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹))
    (hrat : ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      co.e (incM D.host.F x) =
        (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) :
    (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F κ,
      GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (Φ + Φ') =
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ + GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ') ∧
    (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F κ,
      GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ = GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ' → Φ = Φ') ∧
    ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f ↔
      ∃ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ = f := by
  have hR : IsTotallyReal D.host.F := inferInstance
  let σ := Fintype.equivFin κ
  have he : ∀ w w', symplO S T w w' = symV (GlobalTheory.TransportF.numCoordF co σ w) (GlobalTheory.TransportF.numCoordF co σ w') := fun w w' => by
    rw [symplO_eq_symp hA hB, co.form]
    simp only [symV, GlobalTheory.TransportF.numCoordF_apply, comp_equiv_dotProduct_comp_equiv]
  have hr : ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : Fin (Fintype.card κ) → D.host.F,
      GlobalTheory.TransportF.numCoordF co σ (incM D.host.F x) = (rat y, rat z) := fun x => by
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨y ∘ σ.symm, z ∘ σ.symm, by rw [GlobalTheory.TransportF.numCoordF_apply, h]; rfl⟩
  refine ⟨fun Φ hΦ Φ' hΦ' => ?_, fun Φ hΦ Φ' hΦ' h => ?_, fun f => ⟨fun hf => ?_, ?_⟩⟩
  · simp only [GlobalTheory.TransportF.thetaTr_eqF co σ]
    exact congrArg (· ∘ GlobalTheory.TransportF.numCoordF co σ) (GlobalTheory.TransportF.thV_add hR hψ.1 (_root_.GlobalTheory.SchwartzDecay.decay_of_mem_schA _ _ _ (GlobalTheory.TransportF.comp_mem_schA σ hΦ))
      (_root_.GlobalTheory.SchwartzDecay.decay_of_mem_schA _ _ _ (GlobalTheory.TransportF.comp_mem_schA σ hΦ')))
  · simp only [GlobalTheory.TransportF.thetaTr_eqF co σ] at h
    have h2 := GlobalTheory.TransportF.thV_injOn hR hψ.1 (GlobalTheory.TransportF.comp_mem_schA σ hΦ) (GlobalTheory.TransportF.comp_mem_schA σ hΦ')
      ((GlobalTheory.TransportF.numCoordF co σ).surjective.injective_comp_right h)
    funext x
    simpa [Function.comp_def] using congrFun h2 (x ∘ σ.symm)
  · obtain ⟨Φ, hΦ, h⟩ := exists_thV_eq hψ he hr hf
    refine ⟨_, GlobalTheory.TransportF.comp_mem_schA σ.symm hΦ, ?_⟩
    rw [GlobalTheory.TransportF.thetaTr_eqF co σ, ← h]
    congr 2
    funext x
    simp [Function.comp_def]
  · rintro ⟨Φ, hΦ, rfl⟩
    rw [GlobalTheory.TransportF.thetaTr_eqF co σ]
    exact isThetaFunO_thV hψ he hr (GlobalTheory.TransportF.comp_mem_schA σ hΦ)

theorem thetaTr_smul (c : ℂ) (Φ : (κ → AF D.host.F) → ℂ) :
    GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (c • Φ) = c • GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ :=
  GlobalTheory.TransportF.thetaTr_smulF co c Φ

end Pair

theorem exists_isTransport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∃ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om := by
  intro D ψ hψ S T χS χT _ _ _ _ JA JB ξ hA hB κ _ co hrat ω hω
  have hS : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND D.sp.cm.sig S.gram :=
    ⟨fun i j => S.herm.eq (S.frame j) (S.frame i), Formalism.L2.Theta.gram_det_ne S⟩
  have hξ0 : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  obtain ⟨hadd, hinj, hon⟩ := thetaTr_bij co hψ hA hB hrat
  obtain ⟨om, hom⟩ := GlobalTheory.TransportF.exists_transport' _ _ _ hadd (thetaTr_smul co) hinj hon
    (ω.comp (GlobalTheory.TransportF.pairHomF hS hξ0 hA hB)) fun p f hf => hω.om_pres _ f hf
  refine ⟨om, ?_⟩
  unfold GlobalTheory.WeilSchrodinger.IsTransport
  intro a b g h hh hg Φ hΦ
  have e : (ω.comp (GlobalTheory.TransportF.pairHomF hS hξ0 hA hB)) (a, b) = ω (g, h) :=
    congrArg ω (GlobalTheory.TransportF.pairHomF_eq hS hξ0 hA hB a b g h hh hg)
  have h2 := hom (a, b) Φ hΦ
  exact ⟨h2.1, h2.2.trans (LinearMap.congr_fun e _)⟩

end GlobalTheory.ThetaTransform

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans =====
