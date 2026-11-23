module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObstructionPullbackEqZeroOfNaturalLift
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

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.obstructionPullback_eq_zero_of_naturalLift_alt : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T) (C'' : Type) [Category.{0} C''] (F'' : C'' ⥤ CommAlgCat.{0} R₀) (L'' : Pre I π F'') (m : CoefMap (RingHom.id R₀) F' F'') (u : ∀ T : C'', L'.B (m.G.obj T) →ₐ[R] L''.B T) (v : ∀ T : C'', L.B (n.G.obj (m.G.obj T)) →ₐ[R] L''.B T), L.IsLift L' n l → L'.IsLift L'' m u → L'.IsNat L'' m u → (∀ T b, L''.p T (v T b) = m.α T (n.α _ (L.p _ b))) → (∀ (T T' : C'') (a : T ⟶ T') b, L''.ρ a (v T b) = v T' (L.ρ (n.G.map (m.G.map a)) b)) → ∀ (w : Glob1 F) (c : GlobalTheory.CatCoh.H1 (ext R₁ F')), L.IsOb1 L' n l α w c → (extMap R₁ m).pull1 c = 0 := by
  first | exact @GlobalTheory.Obs.obstructionPullback_eq_zero_of_naturalLift | exact GlobalTheory.Obs.obstructionPullback_eq_zero_of_naturalLift | (intros; apply GlobalTheory.Obs.obstructionPullback_eq_zero_of_naturalLift <;> assumption)
