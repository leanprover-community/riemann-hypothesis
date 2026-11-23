module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatGaugeCoverOpenLeHeatOperatorOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugedLocalHeatOperatorPowerMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.gauged_local_heat_operator_power_mul : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (X : Scheme.{0}) (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D) (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])), (∀ a, IsField ⊤ (dd a)) → ∀ (c : R), 2 * c = 1 → ∀ (p : h₁.J × (Fin 2 → L.ι)) (k : ℕ) (O : G.left.Opens), O ≤ GlobalTheory.Heat.Gauge.W m h₁ p → ∀ (f : Γ(G.left, O)), op G dd h₁.Θ h₁.u (GlobalTheory.Heat.Gauge.gD m h₁ e p) (GlobalTheory.Heat.Gauge.gP m h₁ e c p) (GlobalTheory.Heat.Gauge.gP' m h₁ e c p) k O (rsT (GlobalTheory.Heat.Gauge.gU m h₁ e p).val O ^ k * f) = rsT (GlobalTheory.Heat.Gauge.gU m h₁ e p).val O ^ k * op G dd h₁.Θ h₁.u (h₁.d p.1) (h₁.p p.1) (h₁.p' p.1) k O f := by
  first | exact @GlobalTheory.Heat.Gauge.op_gauged | exact GlobalTheory.Heat.Gauge.op_gauged | (intros; apply GlobalTheory.Heat.Gauge.op_gauged <;> assumption)
