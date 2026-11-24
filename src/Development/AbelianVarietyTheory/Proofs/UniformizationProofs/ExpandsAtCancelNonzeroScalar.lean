module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MemSpanCstOfCstMulEqZero
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem expandsAt_cancel_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) [QuasiCompact G.hom] (r : R), r ≠ 0 → ∀ (σ₀ σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f₀ f : ∀ α, D.toPre.SecB k α), (∀ α, (∀ j, (f₀ α).f j = resTop _ (scal D.toPre.P.A.hom r) * (f α).f j)) → (∀ j, (σ₀).f j = resTop _ (scal G.hom r) * (σ).f j) → (∀ e, U.ExpandsAt e k σ₀ f₀) → ∀ e, U.ExpandsAt e k σ f := by
  intro R _ _ I hR D A G _ _ _ U k _ r hr σ₀ σ f₀ f hf hσ hE
  have := hR.1
  exact expandsAt_cancel_of_ne_zero R I D A G U k r hr σ σ₀ f f₀ hσ hf hE

end GlobalTheory
