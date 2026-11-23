module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisAtTraitVsGenericBasis
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

theorem _root_.GlobalTheory.T.exists_adaptedBasis_at_trait_vs_generic_basis : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (ρ₀ : LB.Gen (L₀.pull (eSec G₀))), ∀ (χ : Sp V ⟶ Z) (Φ : G.left ⟶ G₀.left) (ω : LB.Iso U.LG.L (L₀.pull Φ)), RigPull G G₀ χ Φ ω U.LG.rig ρ₀ → ∀ (K : Type) [Field K] (x : Sp K ⟶ Z) (gam : K →+* FractionRing V) (h : spMap gam ≫ x = jK V ≫ χ) (θ : LB.Sec (LPow G₀ L₀ ((1 : ℕ) : ℤ) (Over.mk x))), FrameAt G₀ L₀ 1 x gam χ h (fun _ : Fin 1 => θ) → ∀ (k r : ℕ) (τ : Fin r → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk x))), 1 ≤ k → AllBasis G₀ L₀ k x τ → ∃ (φ : A.A.left ⟶ G₀.left) (w : LB.Iso A.L (L₀.pull φ)) (ρ : LB.Gen (A.L.pull (eSec A.A))) (w₀ : W0 U.toUnifPre) (th : SecA A F 1) (ϑ : Fam D.toPre F 1) (cls : Fin r → D.toPre.X) (mu : ℕ) (b τF : Fin r → SecA A F k) (s : Fin r → Fam D.toPre F k) (B : Matrix (Fin r) (Fin r) (FractionRing V)), RigPull A.A G₀ (jK V ≫ χ) φ w ρ ρ₀ ∧ NormW U.toUnifPre w₀ ρ ∧ U.ExpandsF F 1 w₀ th ϑ ∧ Prim D Q v ϑ ∧ Thru w 1 (T' := TFK (R := V) F) (T := Over.mk x) (jFK (R := V) F ≫ spMap gam) θ th ∧ (∀ i, Thru w k (T' := TFK (R := V) F) (T := Over.mk x) (jFK (R := V) F ≫ spMap gam) (τ i) (τF i)) ∧ Adapted k Q cls mu ∧ Norms D Q v k cls s ∧ (∀ i, U.ExpandsF F k w₀ (b i) (s i)) ∧ (∀ t, ∃! a, Cmb τF a t) ∧ (∀ i, Cmb τF (B.map (algebraMap (FractionRing V) F) i) (b i)) ∧ BasisBy G₀ L₀ k x gam χ h τ B := by
  first | exact @GlobalTheory.GBasis.main | exact GlobalTheory.GBasis.main | (intros; apply GlobalTheory.GBasis.main <;> assumption)
