module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPreDataCubicalStructureEqProdPulledBack
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.tensorPreData_cubicalStructure_eq_prod_pulled_back : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (S : Over (Spec (CommRingCat.of R))) (z : S.left) (J : (S.left ⟶ D.P.A.left) → D.P.L.ι) (J' : (S.left ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → ∀ x x' y : S ⟶ D'.P.A, (let om := fun p : S ⟶ D'.P.A => gm p.left z _ (T.w.s (fun k => J (p.left ≫ tensφ T.pr k), J' p.left)); cubV D'.cub z J' x x' y * (om (x * x' * y) * (om (x * x'))⁻¹ * (om (x * y))⁻¹ * (om (x' * y))⁻¹ * om x * om x' * om y * (om 1)⁻¹) = ∏ k : (Fin r × Fin r) × Fin 4, cubV D.cub z J (x ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2) (x' ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2) (y ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2) ^ tensε W k) := by
  first | exact @GlobalTheory.TensCub.cubV_tens | exact GlobalTheory.TensCub.cubV_tens | (intros; apply GlobalTheory.TensCub.cubV_tens <;> assumption)
