module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SplitTorusExtensionTorsion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.split_torus_extension_torsion : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Gt B : Over S) [GrpObj Gt] [IsCommMonObj Gt] [GrpObj B] [IsCommMonObj B] (u : splitTorus S X ⟶ Gt) (q : Gt ⟶ B) [IsMonHom u] [IsMonHom q], Flat q.left → Surjective q.left → QuasiCompact q.left → IsPullback u (toUnit _) q η[B] → ∀ (N : ℕ), 1 ≤ N → ∀ (TN GN BN : Over S) (jT : TN ⟶ splitTorus S X) (jG : GN ⟶ Gt) (jB : BN ⟶ B) (eB : 𝟙_ _ ⟶ BN), IsPullback jT (toUnit _) ((𝟙 _) ^ N) η[splitTorus S X] → IsPullback jG (toUnit _) ((𝟙 _) ^ N) η[Gt] → IsPullback jB (toUnit _) ((𝟙 _) ^ N) η[B] → eB ≫ jB = η[B] → ∀ (a : TN ⟶ GN) (b : GN ⟶ BN), a ≫ jG = jT ≫ u → b ≫ jB = jG ≫ q → Flat b.left ∧ Surjective b.left ∧ IsPullback a (toUnit TN) b eB := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.Tors.Ext.torsion_exact | exact GlobalTheory.CompanionTheory.Ar.BT.Tors.Ext.torsion_exact | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.Tors.Ext.torsion_exact <;> assumption)
