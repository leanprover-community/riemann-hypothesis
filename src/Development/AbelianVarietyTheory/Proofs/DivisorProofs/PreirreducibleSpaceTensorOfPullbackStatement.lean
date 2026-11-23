module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleSpaceTensorOfPullback
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.preirreducibleSpace_tensor_of_pullback' : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (V : S.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ V) (hV : IsAffineOpen V) (hW : IsAffineOpen W) (k : Type) [Field k] [Algebra Γ(S, V) k] [Algebra Γ(S, V) Γ(X, W)], algebraMap Γ(S, V) Γ(X, W) = (f.appLE V W h).hom → PreirreducibleSpace ↥(pullback (W.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) k)) ≫ hV.fromSpec)) → PreirreducibleSpace (PrimeSpectrum (k ⊗[Γ(S, V)] Γ(X, W))) := by
  first | exact @GlobalTheory.preirreducibleSpace_tensor_of_pullback | exact GlobalTheory.preirreducibleSpace_tensor_of_pullback | (intros; apply GlobalTheory.preirreducibleSpace_tensor_of_pullback <;> assumption)
