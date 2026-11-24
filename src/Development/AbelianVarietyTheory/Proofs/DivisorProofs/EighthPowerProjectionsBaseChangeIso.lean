module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsE8WeightedBundle
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.E8Fibration

theorem isProd_pullback_iso : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) {A B : Over S} [GrpObj A] [GrpObj B] (pr : Fin 8 → (A ⟶ B)), E8Fibration.IsProd pr → ∀ (P : Over S') [GrpObj P] (i : (Over.pullback f).obj A ≅ P), IsMonHom i.hom → E8Fibration.IsProd (fun a => i.inv ≫ (Over.pullback f).map (pr a)) := by
  intro S S' f A B _ _ pr hpr P _ i hi
  obtain ⟨hmon, huniv⟩ := hpr
  refine ⟨fun a => ?_, fun T y => ?_⟩
  · haveI := hmon a
    infer_instance
  · let adj := Over.mapPullbackAdj f
    obtain ⟨x', hx', hu⟩ := huniv ((Over.map f).obj T) (fun a => (adj.homEquiv T B).symm (y a))
    refine ⟨adj.homEquiv T A x' ≫ i.hom, fun a => ?_, fun x hx => ?_⟩
    · simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Adjunction.homEquiv_naturality_right, hx' a, Equiv.apply_symm_apply]
    · have h1 : (adj.homEquiv T A).symm (x ≫ i.inv) = x' := by
        apply hu
        intro a
        rw [← Adjunction.homEquiv_naturality_right_symm, Category.assoc, hx a]
      rw [← h1, Equiv.apply_symm_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end GlobalTheory.Poinc.Sep.E8Fibration

end
