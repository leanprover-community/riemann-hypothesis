module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CompInv
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

def ZMap : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [CharZero K] [Field L] [CharZero L] (φ : K →+* L)
    (W : WeierstrassCurve K),
    PowerSeries.map φ (logSer W) = logSer (W.map φ) ∧
    PowerSeries.map φ (expSer W) = expSer (W.map φ) ∧
    PowerSeries.map φ (wpReg W) = wpReg (W.map φ) ∧
    φ (g₂ W) = g₂ (W.map φ) ∧ φ (g₃ W) = g₃ (W.map φ)

def ConstOfD : Prop :=
  ∀ (R : Type u) [CommRing R] [IsAddTorsionFree R] (W : WeierstrassCurve R),
    (∀ f : R⟦X⟧, D W f = 0 → f = C (constantCoeff f)) ∧
    (∀ f : LaurentSeries R, dL f = 0 → f = HahnSeries.C (f.coeff 0)) ∧
    (∀ f : LaurentSeries R, DL W f = 0 → f = HahnSeries.C (f.coeff 0))

def JetZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (f : K⟦X⟧) (n : ℕ),
    (n.factorial : K) * coeff n (f.subst (expSer W)) = constantCoeff ((D W)^[n] f)

def JetMem : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (S : Subring K),
    W.a₁ ∈ S → W.a₂ ∈ S → W.a₃ ∈ S → W.a₄ ∈ S → W.a₆ ∈ S →
    (∀ f : K⟦X⟧, (∀ n, coeff n f ∈ S) → ∀ n, coeff n (D W f) ∈ S) ∧
    (∀ f : K⟦X⟧, (∀ n, coeff n f ∈ S) → ∀ n : ℕ,
      (n.factorial : K) * coeff n (f.subst (expSer W)) ∈ S) ∧
    ∀ n : ℕ, (n.factorial : K) * coeff n (expSer W) ∈ S

def WpPrimeShape : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    dL (wpL W) = -2 * uPow (-3) + toL (derivative (wpReg W)) ∧
    toL ((wSer W).subst (expSer W)) * yZ W = -1

end Formalism.L2.Th1.A
