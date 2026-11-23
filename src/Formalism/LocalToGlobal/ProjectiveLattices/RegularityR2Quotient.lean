module

public import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def trivCls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop :=
  fun T ι _ => ∀ a : c.F, a ≠ 0 → ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = ι a

structure QPt where
  T : CDVR
  ι : c.F →+* T.Fr
  y : IntFr Xo c T ι
  triv : trivCls Xo c T ι y

def ordQ (q : QPt Xo c) (f : Rul Xo c) : EReal := nval q.T.V 1 (evI q.y f)

def RegularityR1Quotient (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ C a n,
    (∃ la : HeightOneSpectrum (𝓞 c.F), ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) →
      ∀ q : QPt Xo c, 0 ≤ ordQ Xo c q f

def RegularityR2Quotient (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (aL : (E →+* ℂ) × ℕ → ℕ) (nL : ℕ) (aE : (E →+* ℂ) × ℕ → ℕ) (nE k : ℕ) (ws : Fin k → Rul Xo c)
    (et : Rul Xo c) (c' : ℝ), 0 ≤ c' → (∀ i, ws i ∈ C aL nL) → et ∈ C aE nE →
    (∃ (la : HeightOneSpectrum (𝓞 c.F)) (nu : ℝ), ∀ v ∈ valSet Xo c (algCls Xo c) la,
      0 ≤ v et ∧ (∃ i, v (ws i) ≠ ⊤) ∧ (v et ≠ ⊤ → (⨅ i, v (ws i)) ≤ (nu : EReal) + (c' : EReal) * v et)) →
    ∀ q : QPt Xo c, 0 ≤ ordQ Xo c q et ∧
      (ordQ Xo c q et ≠ ⊤ → (⨅ i, ordQ Xo c q (ws i)) ≤ (c' : EReal) * ordQ Xo c q et)

end Formalism.L2.Pj
