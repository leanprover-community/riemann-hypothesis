module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.QuotientMetricDivisors.Statement
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.PieriBlockIdeals.LatticeInclusionRealSettingAlt
import Formalism.PieriBlockIdeals.MertensReciprocalElementary

@[expose] public section

open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameLab

variable {D : D7}

theorem cO_cO (x : 𝓞 D.host.E) : Formalism.DivisionValues.cO D.host.E (Formalism.DivisionValues.cO D.host.E x) = x :=
  RingOfIntegers.ext (star_star (x : D.host.E))

theorem mem_conjPl_of_fixed (P : HeightOneSpectrum (𝓞 D.host.E)) {x : 𝓞 D.host.E} (hx : Formalism.DivisionValues.cO D.host.E x = x) :
    x ∈ (Formalism.DivisionValues.conjPl P).asIdeal ↔ x ∈ P.asIdeal := by
  change x ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) ↔ _
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨y, hy, e⟩
    have : y = x := by rw [← cO_cO y, e, hx]
    rwa [← this]
  · exact fun h => ⟨x, h, hx⟩

theorem under_conjPl (P : HeightOneSpectrum (𝓞 D.host.E)) :
    (Formalism.DivisionValues.conjPl P).under (𝓞 (maximalRealSubfield D.host.E)) = P.under (𝓞 (maximalRealSubfield D.host.E)) := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  exact mem_conjPl_of_fixed P (x := algebraMap _ (𝓞 D.host.E) x)
    (RingOfIntegers.ext (IsCMField.complexConj_apply_eq_self D.host.E (x : maximalRealSubfield D.host.E)))

theorem absNorm_conjPl (P : HeightOneSpectrum (𝓞 D.host.E)) :
    Ideal.absNorm (Formalism.DivisionValues.conjPl P).asIdeal = Ideal.absNorm P.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal _ (Formalism.DivisionValues.cO D.host.E) rfl).toEquiv).symm

end GlobalTheory.FrameLab
