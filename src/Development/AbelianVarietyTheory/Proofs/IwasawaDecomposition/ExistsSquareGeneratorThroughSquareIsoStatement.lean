module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSquareGeneratorThroughSquareIso
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

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_square_generator_through_squareIso : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}, L.IsLB → L'.IsLB →
    ∀ (w : LB.Iso (LB.LinComb L' (K := Fin 1) (fun _ => 𝟙 X') (fun _ => 2))
      ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).pull F)), w.IsGen →
    ∀ {K : Type} [Fintype K] (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε)), a.IsGen →
    ∃ t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) (fun k => 2 * ε k)), t.IsGen ∧
      ∃ W : ∀ (Z : Scheme.{0}) (z : Z), (K → (Z ⟶ X')) → ((Z ⟶ X) → L.ι) → ((Z ⟶ X') → L'.ι) →
          (Z.presheaf.stalk z)ˣ,
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι),
          Good L z J → Good L' z J' → val t r z J = W Z z (fun k => r ≫ φ' k) J J' * val a r z J' ^ 2 := by
  first | exact @GlobalTheory.SqLB.exists_sq_gen | exact GlobalTheory.SqLB.exists_sq_gen | (intros; apply GlobalTheory.SqLB.exists_sq_gen <;> assumption)
