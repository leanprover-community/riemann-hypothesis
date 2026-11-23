module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleFirstOrderTaylorSqZero
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.crystallineCocycle_firstOrder_taylor_sqZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (U V : AffOp X₀), (∃ Q : S.thickObj hI U ⟶ (redMor hI hk s₀).obj (Thick.triv (Sec s₀ U.unop.1) (affPt s₀ U.unop) (affPt_w s₀ U.unop)), ∀ b, Q.φ b = S.p U b) ∧ ∀ (Q : S.thickObj hI U ⟶ (redMor hI hk s₀).obj (Thick.triv (Sec s₀ U.unop.1) (affPt s₀ U.unop) (affPt_w s₀ U.unop))), (∀ b, Q.φ b = S.p U b) → ∀ (α β : S.thickObj hI U ⟶ S'.thickObj hI V) (θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), IsTheta I (S.p U) α.φ β.φ θ → ∀ f : Z1 (O (divided₂ hI) (s₀ ≫ spMap π)), ev f β - ev f α = θ (connForm ((redMor hI hk s₀).coef.pullbackOneCocycle f) (affPt s₀ U.unop) (affPt_w s₀ U.unop) - D R₀ (Sec s₀ U.unop.1) (ev f Q : Sec s₀ U.unop.1)) := by
  first | exact @GlobalTheory.LiftSys.Taylor.ev_sub_ev_eq | exact GlobalTheory.LiftSys.Taylor.ev_sub_ev_eq | (intros; apply GlobalTheory.LiftSys.Taylor.ev_sub_ev_eq <;> assumption)
