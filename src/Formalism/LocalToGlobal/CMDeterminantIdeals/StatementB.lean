module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
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

@[expose] public section

noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors ComplexOrder

def KeyIntegral (R : Type) [CommRing R] {K' : Type} [Field K'] [Algebra R K'] (x : KeyIn K') (a d : K') : Prop :=
  ∃ (th' : x.P.L.Sec) (hth' : ∀ s : Sp K', ∃ y : x.P.A.left, x.P.A.hom y = s ∧ y ∈ Out.nonzeroLocus th')
    (v' : Fin x.P.g → (epsR K' ⟶ x.P.A)) (hv' : IsLieBasis v') (M : Matrix (Fin x.P.g) (Fin x.P.g) K') (xR : KeyIn R),
    (∀ i, LB.Sec.f th' i = constFn x.P.A.hom _ a * LB.Sec.f x.th i) ∧ (∀ i, IsLieComb (M i) x.v (v' i)) ∧ M.det = d ∧
    KeyPB ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', hth', v', hv'⟩ xR (algebraMap R K')

def KeyLocAt {K : Type} [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (p : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∃ (K' : Type) (_ : Field K') (_ : CharZero K') (R : Type) (_ : CommRing R) (_ : IsDomain R)
    (_ : IsDiscreteValuationRing R) (_ : Algebra R K') (_ : IsFractionRing R K') (f : K →+* K') (x' : KeyIn K')
    (a d : K') (ca cd : K) (ua ud : Rˣ),
    KeyPB x' x f ∧ KeyIntegral R x' a d ∧
    (∀ y : K, f y ∈ Set.range (algebraMap R K') ↔ p.valuation K y ≤ 1) ∧
    a = f ca * algebraMap R K' ua ∧ d = f cd * algebraMap R K' ud ∧ IsLocGen p ca T.I ∧ IsLocGen p cd abelian₂.I

def KeyArchAt {K : Type} [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (σ : K →+* ℂ) : Prop :=
  ∃ (xσ : KeyIn ℂ) (u : HolUnif xσ.P.A xσ.P.L xσ.P.g) (Hm W : Matrix (Fin xσ.P.g) (Fin xσ.P.g) ℂ) (χ : u.Λ → ℂ)
    (θ : (Fin xσ.P.g → ℂ) → ℂ) (Fd : Set (Fin xσ.P.g → ℂ)),
    KeyPB xσ x σ ∧ u.IsAH Hm χ ∧ u.IsRig xσ.rig ∧ u.IsFn xσ.th θ ∧ (∀ i, u.IsDiff (W i) (xσ.v i)) ∧
    IsAddFundamentalDomain u.Λ Fd volume ∧
    T.n σ ^ 2 = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (z ⬝ᵥ Hm.mulVec (star z)).re)) / (volume Fd).toReal ∧
    abelian₂.n σ ^ 2 = Real.pi ^ xσ.P.g * ‖W.det‖ ^ 2 / (volume Fd).toReal

def KeyDeg : Prop :=
  KeyFormula → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K), T.Good → abelian₂.Good →
    (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) →
    T.dual.deg = (1 / 2) * abelian₂.dual.deg + (x.P.g : ℝ) / 4 * (Module.finrank ℚ K : ℝ) * Real.log (2 * Real.pi)

end Formalism.L2.LamCM
