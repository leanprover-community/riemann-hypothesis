module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceFromLefschetzAndGroupSide
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open UpperTheory.Gal.LocalSmoothExtension

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh

theorem UpperTheory.Gal.LocalSmoothExtension.hodgeFin_of :
    HolomorphicLefschetzFormula → HodgeFin := by
  intro hW Z s d hsm hproj a b
  haveI := hsm
  have hF : ∀ y : CxPts (Scheme.emptyTo Z ≫ s) (RingHom.id ℂ),
      y ∈ (∅ : Finset (CxPts (Scheme.emptyTo Z ≫ s) (RingHom.id ℂ))) ↔
        y.1 ≫ Scheme.emptyTo Z = y.1 ≫ Scheme.emptyTo Z :=
    fun y => (isEmptyElim (y.1.base (Classical.arbitrary _)) : False).elim
  have key := hW Z s d hproj ∅ (Scheme.emptyTo Z ≫ s) (Scheme.emptyTo Z) (Scheme.emptyTo Z) rfl rfl
    inferInstance inferInstance ∅ hF (fun _ => 0) (fun y hy => by simp at hy) a
  exact key.1 b
