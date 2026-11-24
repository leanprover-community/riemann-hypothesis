module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedKthRootPullbackBundle
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

open scoped CategoryTheory.Obj


theorem _root_.GlobalTheory.T.exists_birigidified_kth_root_pullback_bundle : ∀ (Y : Scheme.{0}) (A D : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj D] (Q : LB (A ⊗ D).left) (h : A ⟶ D) (k : ℕ) (X : Scheme.{0}) (M : LB X) (c : (A ⊗ A).left ⟶ X), IsAbelianScheme A → IsAbelianScheme D → GlobalTheory.AbDual.IsDual A D Q → GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) → IsMonHom h → 0 < k → IsUnit (k : Γ(Y, ⊤)) → M.IsLB → LBIso (M.pull c) (Q.pull (lift (fst A A) (snd A A ≫ h)).left) → ∀ (U : Scheme.{0}) (t : U ⟶ Y) (AU : Over U) [GrpObj AU] [IsCommMonObj AU] (φ : AU.left ⟶ A.left) (φ₂ : (G2 AU).left ⟶ (G2 A).left), IsGrpPullback AU A t φ → IsSquare φ φ₂ → (∀ (T : Over Y) (s : T.left ⟶ U), s ≫ t = T.hom → ∀ a : T ⟶ A, a ^ k = 1 → a ≫ h = 1) → ∃ P : LB (G2 AU).left, P.IsLB ∧ (∃ t : (P.pull (lift (1 : AU ⟶ AU) (𝟙 AU)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 AU) (1 : AU ⟶ AU)).left).Gen, t.IsGen) ∧ LBIso (M.pull (φ₂ ≫ c)) (lbPow P k) := by
  first | (exact @GlobalTheory.KthRoot.exists_birigid_kth_root) | (exact GlobalTheory.KthRoot.exists_birigid_kth_root) | (intros; apply GlobalTheory.KthRoot.exists_birigid_kth_root <;> assumption)
