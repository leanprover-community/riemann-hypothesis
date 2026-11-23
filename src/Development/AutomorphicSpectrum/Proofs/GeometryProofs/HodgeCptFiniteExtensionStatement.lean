module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFiniteExtension
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_cpt_finite_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (A' : HodgeCpt Y S y') (h : A'.X ⟶ A.X) (j : A.Li →+ A'.Li) (m : SABMap A'.t A.t h) (κ : K → K') (v : (Σ k, J k) → (Σ k, J' k)) (Fl : A.Flag), AI.I1.IsBlockMap κ v → (∀ q, y' (v q) = i (y q)) → GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ h i → A'.f = h ≫ A.f → A'.m.φ = m.φ ≫ A.m.φ → A'.cst = i.comp A.cst → IsExtOver i j → (∀ w, (A'.M.pt (j w)).left ≫ m.φ = spMap (dualMap i) ≫ (A.M.pt w).left) → (∀ s, A'.V s = (A.V s).pull A'.ξ h j) → ∀ Fl' : A'.Flag, (∀ s k, Fl'.b s k = j (Fl.b s k)) → ∀ r (e₀ : Ω) (L : HermLine J) (L' : HermLine J'), Fl.IsHodgeLine r e₀ L → AI.I4.IsPullHerm κ v L L' → Fl'.IsHodgeLine r (i e₀) L' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgePull.hodgeLine_pull | exact GlobalTheory.CompanionTheory.Ar.HodgePull.hodgeLine_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgePull.hodgeLine_pull <;> assumption)
