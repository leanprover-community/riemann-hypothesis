module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
public import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromTautBaseOfRescaledPullbackMonomial
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.comesFromTautBase_of_rescaled_pullback_monomial : ∀ {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (n : ℕ) (D₀ : DegPre W), D₀.PsiEven → D₀.TauBimult → (∀ y, PsiUnitOn D₀ y Set.univ) → ∀ (ib : D₀.X ≃+ (Fin T.r → ℤ)) (β : D₀.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ T.B T.M.L).pull ββ)), From T (RingHom.id W) (fun _ : Empty => (1 : W)) (fun _ => 0) n D₀ ib β ββ w → ∀ (V : Type) [CommRing V] [IsDomain V] (iw : W →+* V), Function.Injective iw → ∀ (Q : DegPre V) (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg iw D₀ (rescale Q g)) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (e : Q.X ≃+ (Fin T.r → ℤ)), (∀ y : Q.X, e y = ib (hD.xe y)) → (∀ a a' : Q.X, (((g (a + a'))⁻¹ * g a * g a' : (FractionRing V)ˣ) : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i (e a) (e a'))) → ∃ (β' : Q.P.A.left ⟶ T.B.left) (ββ' : (G2 Q.P.A).left ⟶ (G2 T.B).left) (w' : LB.Iso (abelian₂ Q.P.A Q.P.L) ((abelian₂ T.B T.M.L).pull ββ')), From T iw s ε n Q e β' ββ' w' := by
  first | exact @GlobalTheory.TInj.from_rescale_pull | exact GlobalTheory.TInj.from_rescale_pull | (intros; apply GlobalTheory.TInj.from_rescale_pull <;> assumption)
