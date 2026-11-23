module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionPowerCalculusGeometricFibre
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.sectionPower_calculus_geometric_fibre : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (R : Type) [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ Z) (A : PolAV (Sp (FractionRing R))) (φ : A.A.left ⟶ G₀.left) (w : LB.Iso A.L (L₀.pull φ)), IsGrpPullback A.A G₀ x φ → w.IsGen → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), (∀ (T : Over Z) (p : Sp F ⟶ T.left), p ≫ T.hom = jFK (R := R) F ≫ x → ∀ s : LB.Sec (LPow G₀ L₀ (k : ℤ) T), ∃! t : SecA A F k, Thru w k (T' := TFK (R := R) F) p s t) ∧ (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Z) (T : Over Z) (h : Over.mk y ⟶ T) (ga : R' →+* F), spMap ga ≫ y = jFK (R := R) F ≫ x → ∀ (n : ℕ) (b : Fin n → LB.Sec (LPow G₀ L₀ (k : ℤ) T)) (c : Fin n → R') (s : LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk y))) (bF : Fin n → SecA A F k) (t : SecA A F k), Lin G₀ L₀ k h b (fun i => fnR (c i)) s → (∀ i, Thru w k (T' := TFK (R := R) F) (spMap ga ≫ h.left) (b i) (bF i)) → Thru w k (T' := TFK (R := R) F) (T := Over.mk y) (spMap ga) s t → Cmb bF (fun i => ga (c i)) t) ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ Z) (ga : K →+* F), spMap ga ≫ y = jFK (R := R) F ≫ x → ∀ (n : ℕ) (τ : Fin n → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk y))) (τF : Fin n → SecA A F k), AllBasis G₀ L₀ k y τ → (∀ i, Thru w k (T' := TFK (R := R) F) (T := Over.mk y) (spMap ga) (τ i) (τF i)) → ∀ t : SecA A F k, ∃! a : Fin n → F, Cmb τF a t := by
  first | exact @GlobalTheory.OneBasis.Calc.main | exact GlobalTheory.OneBasis.Calc.main | (intros; apply GlobalTheory.OneBasis.Calc.main <;> assumption)
