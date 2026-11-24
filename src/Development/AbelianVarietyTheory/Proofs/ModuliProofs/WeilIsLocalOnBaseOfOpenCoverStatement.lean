module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.BaseOver
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsLocalOnBaseOfOpenCover
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.weilIs_local_on_base_of_openCover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → ∀ (k : ℤ) (x y : Out.baseOver S ⟶ A) (x' y' : ∀ i, Out.baseOver (U i).toScheme ⟶ G i) (c : Γ(S, ⊤)ˣ), (∀ i, (x' i).left ≫ ψ i = (U i).ι ≫ x.left) → (∀ i, (y' i).left ≫ ψ i = (U i).ι ≫ y.left) → (∀ i, Out.WeilIs (G i) (M i) k (x' i) (y' i) (Units.map (U i).ι.appTop.hom.toMonoidHom c)) → Out.WeilIs A L k x y c := by
  first | exact @GlobalTheory.weilIs_of_openCover | exact GlobalTheory.weilIs_of_openCover | (intros; apply GlobalTheory.weilIs_of_openCover <;> assumption)
