module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyFreeSubsheafDetIso
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

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

theorem _root_.GlobalTheory.T.exists_locallyFree_subsheaf_det_iso : ∀ (X : Scheme.{0}) (F : X.Modules) (r : ℕ) (L : LB X), L.IsLB → ∀ (s : ∀ k : L.ι, Fin r → Γ(F, L.U k)) (A : ∀ k k' : L.ι, Matrix (Fin r) (Fin r) Γ(X, L.U k ⊓ L.U k')), (∀ (k : L.ι) (V : X.Opens) (h : V ≤ L.U k), LinearIndependent Γ(X, V) fun i => GlobalTheory.Twist.resM F h (s k i)) → (∀ (k k' : L.ι) (i : Fin r), GlobalTheory.Twist.resM F (inf_le_right : L.U k ⊓ L.U k' ≤ L.U k') (s k' i) = ∑ j, A k k' j i • GlobalTheory.Twist.resM F (inf_le_left : L.U k ⊓ L.U k' ≤ L.U k) (s k j)) → (∀ k k' : L.ι, (L.g k k').val = (A k k').det) → ∃ (W : X.Modules) (ι : W ⟶ F), Mono ι ∧ GlobalTheory.VB.IsVB W r ∧ LBIso L (GlobalTheory.VB.det W r) := by
  first | exact @GlobalTheory.SubGlue.exists_sub_isVB_lbIso_det | exact GlobalTheory.SubGlue.exists_sub_isVB_lbIso_det | (intros; apply GlobalTheory.SubGlue.exists_sub_isVB_lbIso_det <;> assumption)
