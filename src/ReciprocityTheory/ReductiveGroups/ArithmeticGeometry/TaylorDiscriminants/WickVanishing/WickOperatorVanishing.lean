module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.G2

def ExpAddZeroConstant : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (n d : ℕ) (f g : PS k n d), constantCoeff f = 0 →
    constantCoeff g = 0 → FB.expS k (f + g) = FB.expS k f * FB.expS k g

def ConstantCoeffSubstitution : Prop :=
  ∀ (k : Type) [CommRing k] (d m n : ℕ) (a : Fin m → Pt k n d) (f : PS k m d),
    (∀ j i, constantCoeff (a j i) = 0) → constantCoeff (ev a f) = constantCoeff f

def IsBiadd {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O)
    (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (g : PS k 2 d) : Prop :=
  ev (n := 1) ![0, pt k d 0] g = 0 ∧ ev (n := 1) ![pt k d 0, 0] g = 0 ∧
    ev (n := 3) ![pt k d 0, pt k d 2] g + ev (n := 3) ![pt k d 1, pt k d 2] g =
      ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] g ∧
    ev (n := 3) ![pt k d 0, pt k d 1] g + ev (n := 3) ![pt k d 0, pt k d 2] g =
      ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] g ∧
    ∀ a : O, ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] g =
      ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] g

def CanonicalGaugeDiffBiadditive : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k]
    [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h h' : PS k 2 d),
    B.IsCanonGauge k h → B.IsCanonGauge k h' → IsBiadd B k (h' - h)

def QuadraticFormDerivatives : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k]
    [Algebra ℚ k] [Algebra R k] (B : FB R d O) (g : PS k 2 d), IsBiadd B k g → ∀ w0 : O,
    constantCoeff (ev (n := 1) ![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] g) = 0 ∧
    (∀ u, constantCoeff (Dof (B.FK k) u (ev (n := 1) ![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] g)) = 0) ∧
    ∀ u v, Dof (B.FK k) u (Dof (B.FK k) v (ev (n := 1) ![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] g)) =
      C (dotProduct u ((bilinPart k g).mulVec ((dAct k B w0).mulVec v)) +
        dotProduct v ((bilinPart k g).mulVec ((dAct k B w0).mulVec u)))

def WickOperatorVanishing : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (F : Fin d → PS k 2 d) (ι : Type) [Fintype ι]
    (u : ι → Fin d → k) (c : ι → ι → k) (P : MvPolynomial ι k) (q : PS k 1 d),
    (∀ l l', c l l' = c l' l) → constantCoeff q = 0 → (∀ l, constantCoeff (Dof F (u l) q) = 0) →
    (∀ l l', Dof F (u l) (Dof F (u l') q) = C (c l l')) → secondOrder k c P = 0 →
    ∀ (m : k) (G : PS k 1 d),
      constantCoeff (DpolyOf F u P (G * FB.expS k (m • q))) = constantCoeff (DpolyOf F u P G)

end ReciprocityTheory.ChartRestriction.G.TB.G2
