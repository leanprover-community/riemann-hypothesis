module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormalisedRosatiGeneratorValuesMoveAlongIso
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

theorem _root_.GlobalTheory.T.normalisedRosatiGenerator_values_move_along_iso : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (D : DegPre R) (D' : DegPre R') (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (O : Type) [CommRing O] [StarRing O] (oa : D.P.OAct O) (oa' : D'.P.OAct O) (Φ : (TF (R := R) F ⊗ D.P.A).left ⟶ D'.P.A.left) (w : LB.Iso (D.P.L.pull (snd (TF (R := R) F) D.P.A).left) (D'.P.L.pull Φ)) (φ : N.A →* N'.A) (wv : N.A → F), w.IsGen → Φ ≫ D'.P.A.hom = (fst (TF (R := R) F) D.P.A).left ≫ (TF (R := R') F).hom → (∀ x, (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ Φ = (ν'.eA (φ x)).left) → (∀ x, wv x = valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left _ (w.s (fun _ => ν'.J (ν'.eA (φ x)).left, fun _ => ν.J (ν.eA x).left)).val) → (∀ y b, φ (actV ν oa y b) = actV ν' oa' y (φ b)) → ∀ (a : O) ρ ρ', RosV ν oa a ρ → RosV ν' oa' a ρ' → ∀ b b', ρ' (φ b) (φ b') * (wv (actV ν oa (star a) b) * wv b' * wv (b * actV ν oa a b')) = ρ b b' * (wv (actV ν oa (star a) b * b') * wv b * wv (actV ν oa a b')) := by
  first | exact @GlobalTheory.RosMove.rosV_move | exact GlobalTheory.RosMove.rosV_move | (intros; apply GlobalTheory.RosMove.rosV_move <;> assumption)
