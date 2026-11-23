module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPeriodProduct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.cm_pack_period_product : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (n : ℕ) (a : Fin n → PureType.lat hP (sgnRt H b)) (v : Vecs X.y n) (s : X.K →+* ℂ) (y' : Sp ℂ ⟶ Xo.XF c) (v' : Vecs y' n) (r : ℝ), τ (H.rt : E) = sgnRt H b → (∀ k, X.IsCMVec b τ (a k) (v k)) → y' = spMap s ≫ X.y → (∀ k, (v' k).left = spMap (dualMap s) ≫ (v k).left) → IsLieNormSq (Z b).C.P (Z b).C.v ((s.comp (IntermediateField.inclusion (X.hM b)).toRingHom).comp (algebraMap (𝓞 (Z b).M) (Z b).M)) r → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y') v' (Matrix.of fun k k' => r * ((X.ε b : ℤ) : ℂ) * s (X.β (tauE c τ ((H.rt : E) * sesq (FU.Di i) (a k) (a k'))))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.GInf.hodgeGram_cmVec | exact GlobalTheory.CompanionTheory.Ar.Fl.GInf.hodgeGram_cmVec | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.GInf.hodgeGram_cmVec <;> assumption)
