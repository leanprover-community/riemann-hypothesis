module

public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace PI.StrongApproxE

open Formalism.MainNotions.S.Loc

def IntSpan : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    ∃ (n : ℕ) (b : Fin n → E), (∀ i, IsIntegral ℤ (b i)) ∧ ∀ e : E, ∃ c : Fin n → F, e = ∑ i, c i • b i

def DedSA : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F))) (a c : HeightOneSpectrum (𝓞 F) → F),
    (∀ p ∈ T, c p ≠ 0) →
    ∃ t : F, (∀ p ∈ T, p.valuation F (t - a p) ≤ p.valuation F (c p)) ∧ ∀ p, p ∉ T → p.valuation F t ≤ 1

def LocSmall : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (sig : E →ₐ[F] E)
    (p : HeightOneSpectrum (𝓞 F)) (L : LocAt F E sig p) (V : AddSubgroup L.Fp), IsOpen (V : Set L.Fp) →
    ∃ c : F, c ≠ 0 ∧ ∀ z : F, p.valuation F z ≤ p.valuation F c → L.ιF z ∈ V

def LocDense : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (sig : E →ₐ[F] E)
    (p : HeightOneSpectrum (𝓞 F)) (L : LocAt F E sig p) (V : AddSubgroup L.Fp), IsOpen (V : Set L.Fp) →
    ∀ α : L.Fp, ∃ a : F, L.ιF a - α ∈ V

def LocInt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (sig : E →ₐ[F] E)
    (p : HeightOneSpectrum (𝓞 F)) (L : LocAt F E sig p) (z : F) (e : E), p.valuation F z ≤ 1 → IsIntegral ℤ e →
    L.ιF z • L.ιE e ∈ L.O

def LocSpan : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (sig : E →ₐ[F] E)
    (p : HeightOneSpectrum (𝓞 F)) (L : LocAt F E sig p) (n : ℕ) (b : Fin n → E),
    (∀ e : E, ∃ c : Fin n → F, e = ∑ i, c i • b i) → ∀ x : L.Ep, ∃ α : Fin n → L.Fp, x = ∑ i, α i • L.ιE (b i)

def LocLin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (sig : E →ₐ[F] E)
    (p : HeightOneSpectrum (𝓞 F)) (L : LocAt F E sig p) (a : F) (e : E), L.ιE (a • e) = L.ιF a • L.ιE e

end PI.StrongApproxE
