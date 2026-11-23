module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualTangentVectorsGenericFibreDetEqDetOmegaTrans
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.dualTangentVectors_genericFibre_det_eq_detOmegaTrans : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsSemiAbelian G →
    SmoothOfRelativeDimension g G.hom → ∀ (c c' : VB.Chart (LieVB.omega G) g)
    (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
    (y y' : Fin g → (epsR (KeyVals.FF S) ⟶ KeyVals.bG G (KeyVals.genPt S))),
    KeyVals.IsDual c (KeyVals.genPt S) y → KeyVals.IsDual c' (KeyVals.genPt S) y' →
    ∃ M : Matrix (Fin g) (Fin g) (KeyVals.FF S), (∀ j, IsLieComb (M j) y' (y j)) ∧
      M.det = S.presheaf.germ _ (genericPoint S) h1
        ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) := by
  first | exact @GlobalTheory.KeyVals.LieRel.lieRel | exact GlobalTheory.KeyVals.LieRel.lieRel | (intros; apply GlobalTheory.KeyVals.LieRel.lieRel <;> assumption)
