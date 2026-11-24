module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ThreeApartOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsValuationEqOfIneFixes
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
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem unramifiedAt_of_dec_fixes (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 L)) (hA : IsPlaceOver A w)
    (hfix : ∀ g ∈ Dec (F := maximalRealSubfield L) A, Fixes L g) :
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal := by
  haveI : IsAlgClosure (maximalRealSubfield L) Ω :=
    ⟨IsAlgClosure.isAlgClosed L, Algebra.IsAlgebraic.trans _ L Ω⟩
  have hAv : IsPlaceOver A (w.under (𝓞 (maximalRealSubfield L))) := fun x => by
    rw [IsScalarTower.algebraMap_apply (maximalRealSubfield L) L Ω]
    exact hA (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) x)
  obtain ⟨-, he⟩ := GlobalTheory.InertFixVal.ramificationIdx_eq_one A (w.under (𝓞 (maximalRealSubfield L))) w hAv hA
    fun σ hσ => hfix σ (Ine_le_Dec A hσ)
  exact Ideal.ramificationIdx_eq_one_iff.1 he

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.allUnr :
    SplitIff → AllUnr := by
  intro hS Y Ω _ _ _ _ _ T Q hQ w
  by_cases hw : IsSplitAt w
  · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    exact unramifiedAt_of_dec_fixes ↥Q.K Ω A w hA ((hS ↥Q.K Ω A w hA).1 hw)
  · exact (hQ.2.2.2.1 w hw).2.1
