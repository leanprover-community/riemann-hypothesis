module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.DualSub
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf
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

@[expose] public section

open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl

def W1 : Prop := ∀ (R : Type) [CommRing R] (k M : ℕ) (a b : Fin k) (j : ℕ) (f f' : MvPolynomial (Fin k × Fin k) R),
  a ≠ b → Rel R k M f f' → Rel R k M (rowDiv R a b j f) ((-1) ^ j * rowDiv R b a j f')

def MHhw : Prop := ∀ (R : Type) [CommRing R] (k : ℕ) (ν : Fin k → ℕ), MH R (hw R (le_refl k) ν)

def MHdiv : Prop := ∀ (R : Type) [CommRing R] (k : ℕ) (a b : Fin k) (j : ℕ) (f : MvPolynomial (Fin k × Fin k) R),
  MH R f → MH R (rowDiv R a b j f)

def Diag : Prop := ∀ (R : Type) [CommRing R] (k : ℕ) (a : Fin k) (j d : ℕ) (f : MvPolynomial (Fin k × Fin k) R),
  IsWeightedHomogeneous (rowW a) f d → rowDiv R a a j f = (d.choose j : MvPolynomial (Fin k × Fin k) R) * f

def HomW : Prop := ∀ (R : Type) [CommRing R] (k : ℕ) (ν : Fin k → ℕ) (f : MvPolynomial (Fin k × Fin k) R),
  f ∈ weyl R k k (le_refl k) ν → IsHomogeneous f (degW ν)

def LowMem : Prop := ∀ (R : Type) [CommRing R] (k : ℕ) (ν : Fin k → ℕ), low R ν ∈ weyl R k k (le_refl k) ν

def JacId : Prop := ∀ (R : Type) [CommRing R] (k s : ℕ) (hs : s + 1 ≤ k), ∃ u : R, (u = 1 ∨ u = -1) ∧
  dualSub R k (pMinor R 1 (s + 1) hs) =
    C u * (genM R k).det ^ s * pMinor R Fin.revPerm (k - 1 - s) (by omega)

def JacRev : Prop := ∀ (R : Type) [CommRing R] (k s : ℕ) (hs : s + 1 ≤ k), ∃ u : R, (u = 1 ∨ u = -1) ∧
  dualSub R k (pMinor R Fin.revPerm (s + 1) hs) =
    C u * (genM R k).det ^ s * pMinor R 1 (k - 1 - s) (by omega)

def W4hw : Prop := ∀ (R : Type) [CommRing R] (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam →
  ∃ u : R, (u = 1 ∨ u = -1) ∧
    Rel R (m + 1) (expM lam) (hw R (le_refl _) (nuOf lam)) (C u * low R (nuOf (lamStar lam)))

def Bk : Prop := ∀ (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam →
  lam (Fin.last m) + lamStar lam (Fin.last m) + (degW (nuOf (lamStar lam)) : ℤ) = (expM lam : ℤ)

def EV : Prop := ∀ (K : Type) [Field K] (m : ℕ) (e e' : ℤ) (D M : ℕ)
  (F F' : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K),
  e + e' + (D : ℤ) = (M : ℤ) → Rel K (m + 1) M F F' → IsHomogeneous F' D →
  ∀ z : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit z.det →
    z.det ^ e * eval (fun x => z x.1 x.2) F =
      (revCol (z⁻¹)ᵀ).det ^ e' * eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) (C (sgnK K m ^ e') * F')

def Uniq : Prop := ∀ (K : Type) [Field K] (k d : ℕ) (G : MvPolynomial (Fin k × Fin k) K),
  IsHomogeneous G d → dualSub K k G = 0 → G = 0

def DualB : Prop := ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (m : ℕ)
  (g g' : Matrix (Fin (m + 1)) (Fin (m + 1)) K), IsUnit g.det → IsUnit g'.det →
  colSpan O g = colSpan O g' → colSpan O (g⁻¹)ᵀ = colSpan O (g'⁻¹)ᵀ

def SgnPM : Prop := ∀ (K : Type) [Field K] (m : ℕ), sgnK K m = 1 ∨ sgnK K m = -1

def GStep : Prop := ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ)
  (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K), IsUnit g.det →
  lam (Fin.last m) + lamStar lam (Fin.last m) + (degW (nuOf (lamStar lam)) : ℤ) = (expM lam : ℤ) →
  (∀ f' ∈ weyl O (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)), IsHomogeneous f' (degW (nuOf (lamStar lam)))) →
  (∀ f ∈ weyl O (m + 1) (m + 1) le_rfl (nuOf lam), ∃ f' ∈ weyl O (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
      Rel O (m + 1) (expM lam) f f') →
  ∀ F ∈ deltaLTw O K m lam g, ∃ F' ∈ deltaLTw O K m (lamStar lam) (g⁻¹)ᵀ,
    Rel K (m + 1) (expM lam) F F' ∧ IsHomogeneous F' (degW (nuOf (lamStar lam)))

end PI.OddDualWeyl
