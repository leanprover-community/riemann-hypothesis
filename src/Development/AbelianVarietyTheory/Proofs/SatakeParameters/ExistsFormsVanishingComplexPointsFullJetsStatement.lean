module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFormsVanishingComplexPointsFullJets
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

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

theorem _root_.GlobalTheory.T.exists_forms_vanishing_complexPoints_fullJets : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] (N : ℕ)
    (ι : X ⟶ PSpace ℂ N), IsClosedImmersion ι → ι ≫ PSpace.str ℂ N = p → ∀ S : Finset (CxPts p (RingHom.id ℂ)),
    ∃ (n : ℕ) (h : MvPolynomial (Fin (N + 1)) ℂ) (g : Fin d → MvPolynomial (Fin (N + 1)) ℂ)
      (hh : h ∈ GlobalTheory.ProjSpace.grading ℂ N n) (hg : ∀ j, g j ∈ GlobalTheory.ProjSpace.grading ℂ N n), 0 < n ∧
      (∀ j, genericPoint X ∈ GlobalTheory.EtProj.fOpen ι (g j)) ∧
      (∀ y ∈ S, ∀ j, y ∉ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι (g j))) ∧
      (∀ z : CxPts p (RingHom.id ℂ), z ∉ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι h) →
        (∀ j, z ∉ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι (g j))) → z ∈ S) ∧
      ∀ y ∈ S, ∀ (f₀ : MvPolynomial (Fin (N + 1)) ℂ) (hf₀ : f₀ ∈ GlobalTheory.ProjSpace.grading ℂ N n)
        (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι f₀)),
        GlobalTheory.EtProj.fRatio ι h f₀ hh hf₀ ∈ RingHom.ker (CxPts.evHom hy) ^ 2 ∧
        RingHom.ker (CxPts.evHom hy) ≤ Ideal.span (Set.range fun j => GlobalTheory.EtProj.fRatio ι (g j) f₀ (hg j) hf₀) ⊔
          RingHom.ker (CxPts.evHom hy) ^ 2 := by
  first | (exact @GlobalTheory.EtProj.Jets.exists_jet_forms) | (exact GlobalTheory.EtProj.Jets.exists_jet_forms) | (intros; apply GlobalTheory.EtProj.Jets.exists_jet_forms  <;> assumption)
