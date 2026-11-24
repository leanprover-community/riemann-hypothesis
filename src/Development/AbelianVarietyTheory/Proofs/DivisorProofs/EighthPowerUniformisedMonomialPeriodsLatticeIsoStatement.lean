module

public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerUniformisedMonomialPeriodsLatticeIso
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.eighthPower_uniformised_monomialPeriods_latticeIso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (ϖ : R) (β : LinearMap.BilinForm ℤ D.toPre.X), (∀ a b, β a b = β b a) → (∀ a, 0 ≤ β a a) → (∀ a b' (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D.toPre a b' x → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * algebraMap R (FractionRing R) ϖ ^ (β a b')) → ∃ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y r, PsiCoord D'.toPre y r → 0 ≤ qW W β (e y) ∧ Associated r (ϖ ^ (qW W β (e y)).toNat)) ∧ ∀ (a b : Fin 8) (f : G' ⟶ G') (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f → MatEnd pr a b f₁ → (Over.pullback (jK R)).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m → ∀ y, MatRel W a b (e y) (e (m y)) := by
  first | exact @GlobalTheory.Poinc.EighthPow.main | exact GlobalTheory.Poinc.EighthPow.main | (intros; apply GlobalTheory.Poinc.EighthPow.main <;> assumption)
