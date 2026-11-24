module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigValD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSectionValueTangentEqAdicExpansionSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

theorem _root_.GlobalTheory.T.integralSectionValue_tangent_eq_adicExpansionSum : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (y : epsR V ⟶ G) (gm₀ : GtPt D.toPre (epsR V)), IsTangent y → TanRel U.toUnifPre y gm₀ → ∀ (k : ℕ) (jG : U.LG.L.ι) (J : (Sp (DualNumber V) ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U jG → (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.toPre.P.L.U (J ψ)) → ∃ W : (DualNumber V)ˣ, (W : DualNumber V).fst * GlobalTheory.MBLow.TanExp.rigVal U.LG jG = GlobalTheory.MBLow.TanExp.rigValD D.toPre (J gm₀.b.left) ∧ ∀ (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.toUnifPre.ExpandsAt e k σ f) → GlobalTheory.UT.SumI (IsLocalRing.maximalIdeal V) (fun α => GlobalTheory.MBLow.TanExp.termV J gm₀ (f α)) ((W : DualNumber V) ^ k * valR y.left (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => jG) (σ.f fun _ => jG)) := by
  first | exact @GlobalTheory.MBLow.TanExp.value_mul_sumI | exact GlobalTheory.MBLow.TanExp.value_mul_sumI | (intros; apply GlobalTheory.MBLow.TanExp.value_mul_sumI <;> assumption)
