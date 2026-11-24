module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacter
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleFiniteCommGroupSchemeCobounda
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.CharKer

theorem _root_.GlobalTheory.T.symmetricTwoCocycle_finiteCommGroupScheme_coboundary : ∀ (K : Type) [Field K] [IsAlgClosed K] (N : Over (Sp K)) [GrpObj N] [IsCommMonObj N], IsFinite N.hom → ∀ c : Γ((N ⊗ N).left, ⊤)ˣ, (∀ (T : Over (Sp K)) (x y z : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c * GlobalTheory.CharKer.pullTop (lift (x * y) z).left c = GlobalTheory.CharKer.pullTop (lift y z).left c * GlobalTheory.CharKer.pullTop (lift x (y * z)).left c) → (∀ (T : Over (Sp K)) (x y : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c = GlobalTheory.CharKer.pullTop (lift y x).left c) → ∃ u : Γ(N.left, ⊤)ˣ, ∀ (T : Over (Sp K)) (x y : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c * GlobalTheory.CharKer.pullTop (x * y).left u = GlobalTheory.CharKer.pullTop x.left u * GlobalTheory.CharKer.pullTop y.left u := by
  first | exact @GlobalTheory.SymCob.exists_coboundary | exact GlobalTheory.SymCob.exists_coboundary | (intros; apply GlobalTheory.SymCob.exists_coboundary <;> assumption)
