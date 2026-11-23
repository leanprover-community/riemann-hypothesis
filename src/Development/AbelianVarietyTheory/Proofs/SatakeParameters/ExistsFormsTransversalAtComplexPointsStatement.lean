module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFormsTransversalAtComplexPoints
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

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
theorem _root_.GlobalTheory.T.exists_forms_transversal_at_complexPoints : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] (N : ℕ)
    (ι : X ⟶ PSpace ℂ N), IsClosedImmersion ι → ι ≫ PSpace.str ℂ N = p → ∀ S : Finset (CxPts p (RingHom.id ℂ)),
    ∃ (n : ℕ) (f : Fin (d + 1) → MvPolynomial (Fin (N + 1)) ℂ) (hf : ∀ i, f i ∈ GlobalTheory.ProjSpace.grading ℂ N n), 0 < n ∧
      (⨆ i, GlobalTheory.EtProj.fOpen ι (f i) = ⊤) ∧ (∀ i, genericPoint X ∈ GlobalTheory.EtProj.fOpen ι (f i)) ∧
      (∀ y ∈ S, y ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι (f 0)) ∧ ∀ j : Fin d,
        CxPts.ev p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι (f 0)) (GlobalTheory.EtProj.fRatio ι (f j.succ) (f 0) (hf j.succ) (hf 0)) y = 0) ∧
      ∀ (y : CxPts p (RingHom.id ℂ)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι (f 0))),
        (∀ j : Fin d, CxPts.evHom hy (GlobalTheory.EtProj.fRatio ι (f j.succ) (f 0) (hf j.succ) (hf 0)) = 0) →
        RingHom.ker (CxPts.evHom hy) ≤ Ideal.span (Set.range fun j : Fin d => GlobalTheory.EtProj.fRatio ι (f j.succ) (f 0) (hf j.succ) (hf 0)) ⊔
          RingHom.ker (CxPts.evHom hy) ^ 2 := by
  first | exact @GlobalTheory.EtProj.Transv.exists_forms_transversal | exact GlobalTheory.EtProj.Transv.exists_forms_transversal | exact @GlobalTheory.EtProj.Transv.exists_transversal_forms_first_separate | exact GlobalTheory.EtProj.Transv.exists_transversal_forms_first_separate
