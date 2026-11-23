module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationExtensionLocalDomain
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.degeneration_extension_local_domain : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ ψ : A.A.left ⟶ G.left, IsGrpPullback A.A G (jK V) ψ → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (io : V →+* W) (em : W →+* AlgebraicClosure (FractionRing V)) (D : DegData W (maximalIdeal W)) (Q : PolAV (Sp (FractionRing W))) (H : Over (Sp W)) (_ : GrpObj H) (_ : IsCommMonObj H) (U : Unif (maximalIdeal W) D Q H) (i : (Over.pullback (spMap io)).obj G ⟶ H) (r : Fin 8 → (H ⟶ (Over.pullback (spMap io)).obj G)), GlobalTheory.LN.CDvr W ∧ io.Finite ∧ Function.Injective io ∧ Function.Injective em ∧ (∀ v, em (io v) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ IsSemiAbelian H ∧ GlobalTheory.LN.ToATotal U.toUnifPre ∧ (∀ k, IsMonHom (r k)) ∧ i ≫ r 0 = 𝟙 _ ∧ ∀ (T : Over (Sp W)) (x y : T ⟶ H), (∀ k, x ≫ r k = y ≫ r k) → x = y := by
  first | exact @GlobalTheory.SplitPowEight.exists_unif_pow8 | exact GlobalTheory.SplitPowEight.exists_unif_pow8 | (intros; apply GlobalTheory.SplitPowEight.exists_unif_pow8 <;> assumption)
