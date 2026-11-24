module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ProperCentre

theorem exists_regAt_centre : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] [IsProper s]
    (V : ValuationSubring Y.functionField) (x : X), (∀ f, RegAt x f → functionFieldMap s f ∈ V) →
    ∃ y : Y, s y ⤳ x ∧ ∀ f, RegAt y f → f ∈ V := by
  intro X Y _ _ s _ _ V x h
  let ψ : X.presheaf.stalk x →+* V :=
    ((GlobalTheory.functionFieldMap s).comp (algebraMap (X.presheaf.stalk x) X.functionField)).codRestrict
      V.toSubring (fun a => h _ ⟨a, rfl⟩)
  let r : Spec (.of V) ⟶ X := Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x
  have hc : GlobalTheory.genericFieldPoint Y ≫ s = GlobalTheory.specAlgebraMap V Y.functionField ≫ r := by
    rw [← GlobalTheory.specMap_functionFieldMap, ← GlobalTheory.specAlgebraMap_fromSpecStalk x]
    simp only [r, GlobalTheory.specAlgebraMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  refine ⟨GlobalTheory.valCentre s r (GlobalTheory.genericFieldPoint Y) hc, ?_, ?_⟩
  · rw [GlobalTheory.apply_valCentre_base]
    have := (IsLocalRing.specializes_closedPoint (R := X.presheaf.stalk x)
      (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint V))).map
      (X.fromSpecStalk x).continuous
    rw [Scheme.fromSpecStalk_closedPoint] at this
    exact this
  · have hd : GlobalTheory.DominatesStalk V (GlobalTheory.valCentre s r (GlobalTheory.genericFieldPoint Y) hc) :=
      GlobalTheory.dominatesStalk_iff_exists_hom.mpr
        ⟨_, GlobalTheory.specAlgebraMap_valExt s r (GlobalTheory.genericFieldPoint Y) hc, rfl⟩
    rintro f ⟨a, rfl⟩
    exact hd.1 a

end GlobalTheory.ProperCentre
