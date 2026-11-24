module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ValuativeCriterion
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.valPtsX_of :
    ValPtsX := by
  intro S K h hp V _ _ _ z
  have : IsProper h := hp
  constructor
  · intro g g' hg hg' e
    have c : CommSq (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫ g)
        (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) h z :=
      ⟨by rw [Category.assoc, hg]⟩
    let Q : ValuativeCommSq h := ⟨V, FractionRing V, _, z, c⟩
    have hs : Subsingleton Q.commSq.LiftStruct := IsSeparated.valuativeCriterion h Q
    let l₁ : Q.commSq.LiftStruct := ⟨g, rfl, hg⟩
    let l₂ : Q.commSq.LiftStruct := ⟨g', e.symm, hg'⟩
    exact congrArg CommSq.LiftStruct.l (Subsingleton.elim l₁ l₂)
  · intro g hg
    have c : CommSq g (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) h z := ⟨hg⟩
    let Q : ValuativeCommSq h := ⟨V, FractionRing V, g, z, c⟩
    have hu : (ValuativeCriterion.Existence ⊓ @QuasiCompact) h := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    obtain ⟨l, h₁, h₂⟩ := (hu.1 Q).exists_lift
    exact ⟨l, h₂, h₁⟩
