module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiedOfFaithfullyFlatStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesCompleteNoetherianLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectPullbackLevelPowerCalculus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
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
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelFamLocal

theorem exists_point_of_principal : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp R ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F R _ _ _ β c hc
  haveI : IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  haveI : Module.Flat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) := AdicCompletion.flat_of_isNoetherian _
  haveI : Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine GlobalTheory.T.siegelFamily_classified_of_faithfullyFlat g n hg hn hodd F R (AdicCompletion (IsLocalRing.maximalIdeal R) R) β c hc ?_
  intro c' hc'
  have hp : c'.Principal := GlobalTheory.SiegLevCalc.sRel_principal ((sRel_one_one_iff c' c _).2 hc') hc
  exact GlobalTheory.T.siegelFamily_classifies_complete_noetherian_local g n hg hn hodd F (AdicCompletion (IsLocalRing.maximalIdeal R) R) inferInstance
    ((algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)).comp β) c' hp

end GlobalTheory.SiegelFamLocal
