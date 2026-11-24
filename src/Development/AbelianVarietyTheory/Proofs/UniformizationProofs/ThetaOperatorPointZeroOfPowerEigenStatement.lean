module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaOperatorPointZeroOfPowerEigen
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.thetaOperator_point_zero_of_power_eigen : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (l : ℕ), 1 ≤ l → ∀ (th : EA P p 1) (t : EA P p l) (θ : ThetaGrp P.A P.L (l : ℤ) (Over.mk p)) (c : Fˣ), th ≠ 0 → (∀ z J, Good P.L z J → sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((l : ℕ) : ℤ)) t.sec (𝟙 _) z J = sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) th.sec (𝟙 _) z J ^ l) → IsActOf P.A P.L (l : ℤ) θ t.sec (c.val • t).sec → θ.pt = 1 := by
  first | exact @GlobalTheory.ThetaEigen.main | exact GlobalTheory.ThetaEigen.main | (intros; apply GlobalTheory.ThetaEigen.main <;> assumption)
