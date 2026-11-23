module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueConstPointsTangentEqDualFibreValue
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.cubeValue_constPoints_tangent_eq_dualFibreValue : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
    (ν : NumOf D ℂ N) (d : AB N.toNumB g) (gm : GtPt D (TE R ℂ)),
    (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) →
    ∀ (χ χ' : D.X) (x y : Fin g → ℂ),
    ν.eA (d.ex x) = DegPre.cF D ℂ χ → ν.eA (d.ex y) = DegPre.cF D ℂ χ' →
    ∃ (U : (DegPre.BF D ℂ).left.Opens) (f : Γ((DegPre.BF D ℂ).left, U)),
      vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
        valR (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) gm.b).left U f ∧
      ⊤ ≤ ptB ν d 0 ⁻¹ᵁ U ∧
      ∀ z, ⊤ ≤ ptB ν d z ⁻¹ᵁ U →
        (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ
          D.P.L.U (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)) ∧
        valF (ptB ν d z) U f =
          valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left
            (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) (fun I : thK.{0} => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left))
            (D.cub.t.s (fun I : thK.{0} => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)).val := by
  first | exact @GlobalTheory.MBLow.JetGeo.jet_geo | exact GlobalTheory.MBLow.JetGeo.jet_geo | (intros; apply GlobalTheory.MBLow.JetGeo.jet_geo <;> assumption)
