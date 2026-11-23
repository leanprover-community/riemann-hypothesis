module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.BaseOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliGeometricPointEqOfSameFibreActionLevel
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.moduli_geometric_point_eq_of_same_fibre_action_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (x x' : Sp K ⟶ Xo.X) (α α' : P.A.left ⟶ Xo.univ.t.G.left), x ≫ Xo.s = x' ≫ Xo.s → IsGrpPullback P.A Xo.univ.t.G x α → IsGrpPullback P.A Xo.univ.t.G x' α' → LBIso P.L (Xo.univ.t.PP.L.pull α) → LBIso P.L (Xo.univ.t.PP.L.pull α') → (∀ a, ∃ h : P.A ⟶ P.A, h.left ≫ α = α ≫ (Xo.univ.t.act.act a).left ∧ h.left ≫ α' = α' ≫ (Xo.univ.t.act.act a).left) → (∀ a, ∃ z : baseOver (Sp K) ⟶ P.A, z.left ≫ α = x ≫ (Xo.univ.eta a).left ∧ z.left ≫ α' = x' ≫ (Xo.univ.eta a).left) → (∀ a, ∃ z : baseOver (Sp K) ⟶ P.A, z.left ≫ α = x ≫ (Xo.univ.etaA a).left ∧ z.left ≫ α' = x' ≫ (Xo.univ.etaA a).left) → x = x' := by
  first | exact @GlobalTheory.UMin.moduli_point_eq_of_same_fibre | exact GlobalTheory.UMin.moduli_point_eq_of_same_fibre | (intros; apply GlobalTheory.UMin.moduli_point_eq_of_same_fibre <;> assumption)
