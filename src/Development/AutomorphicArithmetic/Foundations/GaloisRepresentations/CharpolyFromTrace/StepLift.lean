module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.NumberField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.ComplexBaseChangeOfLiterature
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.NotRealComplex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.LimitEig
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.HasTypeVecIff

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong UpperTheory.Gal.NearKilling

theorem UpperTheory.Gal.NearKilling.stepLift :
    UpperTheory.V.Z.Bc.CBCc → UpperTheory.Gal.UnramifiedFromSplittingCriterion.NoSelfTwist → PolBC → WeakRes → StepLift := by
  intro hC hN hP hW K M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp l a _ ha π χ hs A v hv hτ hsat
  obtain ⟨hreg, hpol, -⟩ := hs
  have hK : IsTotallyComplex K := inferInstance
  have hM : IsTotallyComplex M := inferInstance
  rcases (hC K M hp hK a ha).1 (.cx π) with ⟨η, hη, hi⟩ | ⟨Q, hw, hinf, hsplit⟩
  · exfalso
    obtain ⟨B, hB⟩ := hsat
    refine hN K M Ω hp A v hv hτ a ha (CG.mk π) B hB η hη ?_
    rw [CG.twist_mk]
    exact Quotient.sound hi
  · cases Q with
    | re Q => exact (PositivityTheory.Pf1.CLGD.K.LKW.not_real_complex M inferInstance hM).elim
    | cx P =>
      have hw' : UpperTheory.V.Published.WeakBC (CG.mk π).HasSat (CG.mk P).HasSat := hw
      obtain ⟨⟨χ', hχ'⟩, hq⟩ := hP K M a ha π P χ hpol hw'
      refine ⟨P, χ', hw, hsplit, ⟨?_, hχ', trivial⟩, hq, fun ι r hr => hW K M Ω l ι a π P hw' r hr⟩
      refine (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_
      have h1 := GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) (τ.comp (algebraMap K M))
      have h2 : P.HasInfChar τ ((CG.mk π).infChar (τ.comp (algebraMap K M))) := hinf τ _ h1
      have h3 : (CG.mk P).infChar τ = (CG.mk π).infChar (τ.comp (algebraMap K M)) :=
        CG.HasInfChar.infChar_eq h2
      rw [h3]
      exact hreg _
