module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitSectionIntegralExpansionMemRangeInverseExpa
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.traitSection_integralExpansion_mem_range_inverseExpansion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W)))), w₀.IsGen → ∀ E' : Fam T.D'.toPre F (C.n ^ j) → SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j), (∀ s', T.U.ExpandsF F (C.n ^ j) w₀ (E' s') s') → ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (s' : Fam T.D'.toPre F (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), (∀ f' : ∀ x, T.D'.toPre.SecB (C.n ^ j) x, (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → ∀ x, GeneratorPullback.SecScal T.D'.toPre.P.L (DegPre.famφ T.D'.toPre F x) (DegPre.famε (C.n ^ j)) ((s').s x) (T.D'.toPre.famφB x) (DegPre.famε (C.n ^ j)) (f' x) (DegPre.prB T.D'.toPre F).left 1) → T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), p ≫ T.β = q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JG Jt, Good C.P.L.L z JP → Good T.U.LG.L z JG → Good T.A.L z Jt → sval σ p z JP = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval (E' s') q z Jt := by
  first | exact @GlobalTheory.Mum.TraitValue.value | exact GlobalTheory.Mum.TraitValue.value | (intros; apply GlobalTheory.Mum.TraitValue.value <;> assumption)
