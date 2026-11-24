module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeCechCocycleInvariantVectorFieldIsCobou
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.derivative_cechCocycle_invariantVectorField_isCoboundary : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (J : Type) (V : J → A.left.Opens), ⨆ a, V a = ⊤ → ∀ φ : ∀ a b, Γ(A.left, V a ⊓ V b), (∀ (a b c : J) (P : GPt A), P.In (V a) → P.In (V b) → P.In (V c) → valR P.x _ (φ a b) + valR P.x _ (φ b c) = valR P.x _ (φ a c)) → ∀ v : epsR K ⟶ A, IsTangent v → ∃ ψ : J → PtFn (A.hom ≫ 𝟙 (Sp K)), (∀ a, IsNat (V a) (ψ a)) ∧ ∀ (a b : J) (P : GPt A), P.In (V a) → P.In (V b) → (valR (P.trx v) _ (φ a b)).snd = ψ a P - ψ b P := by
  first | exact @GlobalTheory.CechInv.deriv_cocycle_isCoboundary | exact GlobalTheory.CechInv.deriv_cocycle_isCoboundary | (intros; apply GlobalTheory.CechInv.deriv_cocycle_isCoboundary <;> assumption)
