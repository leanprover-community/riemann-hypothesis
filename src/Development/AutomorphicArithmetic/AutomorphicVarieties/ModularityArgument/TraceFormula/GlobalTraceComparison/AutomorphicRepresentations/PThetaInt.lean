module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapInvolutionEq
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.AdmissibleLeHolds
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
import Mathlib.Tactic.TypeStar

@[expose] public section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open MeasureTheory

private theorem twist_general {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] {F : Set G}
    (fd : IsFundamentalDomain Γ F μ) (θ : G →* G) (hc : Continuous θ) (hi : ∀ x, θ (θ x) = x)
    (hΓ : ∀ γ ∈ Γ, θ γ ∈ Γ) (f : G → ℂ) (hf : ∀ (γ : Γ) x, f ((γ : G) * x) = f x)
    (hI : Integrable f (μ.restrict F)) :
    Integrable (fun x => f (θ x)) (μ.restrict F) ∧
      ∫ x, f (θ x) ∂(μ.restrict F) = ∫ x, f x ∂(μ.restrict F) :=
  _root_.UpperTheory.Reformulated.B.Qh1.twist_general μ Γ fd θ hc hi hΓ f hf hI

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.thetaInt_pf :
    Basic → ThetaInt := by
  intro _ E _ _ _ n D f hf hI
  have hb := PositivityTheory.Rg.BcB.E1.thetaBasic_holds E
  let θ : PositivityTheory.Rg.BcB.E.H E n 0 →* PositivityTheory.Rg.BcB.E.H E n 0 :=
    (PositivityTheory.Rg.BcB.thetaA E n).prodMap (PositivityTheory.Rg.BcB.thetaA E 0)
  have hc : Continuous θ :=
    ((hb n).1.comp continuous_fst).prodMk ((hb 0).1.comp continuous_snd)
  have hi : ∀ x, θ (θ x) = x := fun x => Prod.ext ((hb n).2.1 x.1) ((hb 0).2.1 x.2)
  have hΓ : ∀ γ ∈ PositivityTheory.Rg.BcB.E.ratH E n 0, θ γ ∈ PositivityTheory.Rg.BcB.E.ratH E n 0 := by
    rintro _ ⟨g, rfl⟩
    exact ⟨(PositivityTheory.Rg.BcB.thetaE E n g.1, PositivityTheory.Rg.BcB.thetaE E 0 g.2),
      Prod.ext ((hb n).2.2 g.1).symm ((hb 0).2.2 g.2).symm⟩
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E 0
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E 0
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E 0
  haveI := (PositivityTheory.Rg.BcB.E1.ratProper_holds E n).2.1
  haveI := (PositivityTheory.Rg.BcB.E1.ratProper_holds E 0).2.1
  letI := PositivityTheory.Rg.BcB.E.borelH E n 0
  haveI : BorelSpace (PositivityTheory.Rg.BcB.E.H E n 0) := ⟨rfl⟩
  haveI : D.μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts :=
        @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure _ _ _ D.μ D.haar.2.2.2
      toIsMulLeftInvariant := D.haar.1
      toIsOpenPosMeasure := D.haar.2.2.1 }
  haveI : Countable (PositivityTheory.Rg.BcB.E.ratH E n 0) :=
    (((GlobalTheory.CuspRep.ratGL E n).prodMap (GlobalTheory.CuspRep.ratGL E 0)).rangeRestrict_surjective).countable
  exact twist_general D.μ _ D.fd θ hc hi hΓ f hf hI
