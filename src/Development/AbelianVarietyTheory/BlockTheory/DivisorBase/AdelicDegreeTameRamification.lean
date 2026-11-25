module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev quadField (H : Host E) : IntermediateField ℚ E := IntermediateField.adjoin ℚ {((H.rt : 𝓞 E) : E)}

instance (H : Host E) : Fact H.d.Prime := ⟨H.d_prime⟩

def quadChar (H : Host E) : DirichletCharacter ℂ H.d :=
  (quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ)

def logOmega (H : Host E) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (Real.pi / (rootDiscr E / 2)) -
    (deriv (quadChar H).LFunction 1 / (quadChar H).LFunction 1).re

def TameAtRamified (H : Host E) : Prop :=
  ∀ (l : ℕ) (w : Ideal (𝓞 E)), l.Prime → (l : ℤ) ∣ discr E → w.IsMaximal → (l : 𝓞 E) ∈ w →
    w.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ w ∧
    (l ≠ H.d → ∃ a ∈ Algebra.adjoin ℤ {H.w0}, a ∈ w ∧ H.bar a ∉ w) ∧
    (l = H.d → (l : 𝓞 E) ∉ w ^ 3)

section Degree

variable (k : Type) [Field k] [NumberField k]

def adelicDeg (a : HeightOneSpectrum (𝓞 k) → k) (r : (k →+* ℂ) → ℝ) : ℝ :=
  (-(∑ σ : k →+* ℂ, Real.log (r σ) / 2) + ∑ᶠ v, Real.log (FinitePlace.mk v (a v))) / Module.finrank ℚ k

end Degree

section Lie

variable {H : Host E} {k : Type} [Field k] [NumberField k]

def IsEigenVec (t : SAB H (Sp k)) (χ : 𝓞 E → k) (w : epsR k ⟶ t.G) : Prop :=
  IsTangent w ∧ ∀ a, (w ≫ t.act.act a).left = spMap (epsScaleR (χ a)) ≫ w.left

def IsEigenBasis (t : SAB H (Sp k)) (χ : 𝓞 E → k) {n : ℕ} (x : Fin n → (epsR k ⟶ t.G)) : Prop :=
  (∀ i, IsEigenVec t χ (x i)) ∧ ∀ w, IsEigenVec t χ w → ∃! c : Fin n → k, IsLieComb c x w

end Lie

end GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification
