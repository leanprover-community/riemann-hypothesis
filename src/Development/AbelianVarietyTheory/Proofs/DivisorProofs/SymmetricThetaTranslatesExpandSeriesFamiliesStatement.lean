module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricThetaTranslatesExpandSeriesFamilies
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.symmetricThetaTranslates_expand_seriesFamilies : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre) (ρ : LB.Gen (A.L.pull (eSec A.A))), GlobalTheory.UT.NormW U.toUnifPre w₀ ρ → ∀ (th : GlobalTheory.UT.SecA A C 1) (ϑ : Fam D.toPre C 1) (c : C), U.ExpandsF C 1 w₀ th ϑ → ν.FamV ϑ (c • N.vth) → ∀ m : ℕ, Odd m → ∀ (p : QkPt D.toPre C (m ^ 2)) (q : N.QT (m ^ 2)) (z : TFK (R := V) C ⟶ A.A), ν.QPt p q → QkToAkU U.toUnifPre C (m ^ 2) p z → ∃ (Θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := V) C)) (t : GlobalTheory.UT.SecA A C (m ^ 2)) (s : Fam D.toPre C (m ^ 2)) (f : N.X → N.A → C), SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) z Θ ∧ Tr A ρ m th Θ t ∧ U.ExpandsF C (m ^ 2) w₀ t s ∧ IsEvFam N m q f ∧ ν.FamV s (c • f) := by
  first | exact @GlobalTheory.MBLow.symTranslate_expandsF | exact GlobalTheory.MBLow.symTranslate_expandsF | (intros; apply GlobalTheory.MBLow.symTranslate_expandsF <;> assumption)
