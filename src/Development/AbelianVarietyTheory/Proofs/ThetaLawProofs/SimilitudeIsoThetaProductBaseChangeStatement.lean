module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SimilitudeIsoThetaProductBaseChange
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.similitudeIso_thetaProduct_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R') φ u (m N : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin N → RR x m) (b' : Fin N → RR x' m) (ξ : Fin 4 → Pt x) (ξ' : Fin 4 → Pt x') (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))) (q : (Fin 4 → Fin N) → R), KeyVia x' x f φ u → (∀ k, SecVia x' x φ u (b' k) (b k)) → (∀ r, (ξ' r).left ≫ φ = spMap f ≫ (ξ r).left) → w.IsGen → (∀ (Z : Scheme.{0}) (ρ : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) J, Good x.P.L z J → ∏ r, gs (ρ ≫ (alMap x al r (ξ r)).left) z (x.P.L.U (J (ρ ≫ (alMap x al r (ξ r)).left))) (x.th.f (J (ρ ≫ (alMap x al r (ξ r)).left))) = (val w ρ z J).val * ∑ I' : Fin 4 → Fin N, gs ρ z ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ (q I')) * ∏ c, gs (ρ ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (ρ ≫ (Out.powPr x.P.A c).left))) ((b (I' c)).f (J (ρ ≫ (Out.powPr x.P.A c).left)))) → ∃ w' : LB.Gen (LB.LinComb x'.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x' al r (ξ' r)).left) (fun c => (Out.powPr x'.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ)))), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (Out.powObj x'.P.A 4).left) (z : Z) J, Good x'.P.L z J → ∏ r, gs (ρ ≫ (alMap x' al r (ξ' r)).left) z (x'.P.L.U (J (ρ ≫ (alMap x' al r (ξ' r)).left))) (x'.th.f (J (ρ ≫ (alMap x' al r (ξ' r)).left))) = (val w' ρ z J).val * ∑ I' : Fin 4 → Fin N, gs ρ z ⊤ (cst (Out.powObj x'.P.A 4).hom ⊤ (f (q I'))) * ∏ c, gs (ρ ≫ (Out.powPr x'.P.A c).left) z (x'.P.L.U (J (ρ ≫ (Out.powPr x'.P.A c).left))) ((b' (I' c)).f (J (ρ ≫ (Out.powPr x'.P.A c).left))) := by
  first | exact @GlobalTheory.KeyRow.main | exact GlobalTheory.KeyRow.main | (intros; apply GlobalTheory.KeyRow.main <;> assumption)
