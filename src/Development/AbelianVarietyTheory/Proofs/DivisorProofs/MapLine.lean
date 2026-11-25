module

public import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MvPolynomial GlobalTheory.HSChoice

namespace GlobalTheory.PencilDisc

def line {F R : Type} [CommRing F] [CommRing R] [Algebra F R] {D N : ℕ} (u : Fin D → Fin N → R) (a b : Fin N → R)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) : Polynomial R :=
  aeval (join (fun i j => Polynomial.C (u i j)) fun j => Polynomial.C (a j) + Polynomial.C (b j) * Polynomial.X) f

def disc {F R : Type} [CommRing F] [CommRing R] [Algebra F R] {D N : ℕ} (δ : ℕ) (u : Fin D → Fin N → R) (a b : Fin N → R)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) : R :=
  Polynomial.resultant (line u a b f) (Polynomial.derivative (line u a b f)) δ (δ - 1)

theorem map_line {F R S : Type} [CommRing F] [CommRing R] [CommRing S] [Algebra F R] [Algebra F S] {D N : ℕ}
    (φ : R →ₐ[F] S) (u : Fin D → Fin N → R) (a b : Fin N → R) (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    (line u a b f).map (φ : R →+* S) = line (fun i j => φ (u i j)) (fun j => φ (a j)) (fun j => φ (b j)) f := by
  have h : (Polynomial.mapAlgHom φ).comp
      (aeval (join (fun i j => Polynomial.C (u i j)) fun j => Polynomial.C (a j) + Polynomial.C (b j) * Polynomial.X)) =
      aeval (join (fun i j => Polynomial.C (φ (u i j))) fun j => Polynomial.C (φ (a j)) + Polynomial.C (φ (b j)) * Polynomial.X) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [join]
    · simp [join]
  exact congrArg (fun g : MvPolynomial (Fin (D + 1) × Fin N) F →ₐ[F] Polynomial S => g f) h

theorem map_disc {F R S : Type} [CommRing F] [CommRing R] [CommRing S] [Algebra F R] [Algebra F S] {D N : ℕ}
    (φ : R →ₐ[F] S) (δ : ℕ) (u : Fin D → Fin N → R) (a b : Fin N → R) (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    φ (disc δ u a b f) = disc δ (fun i j => φ (u i j)) (fun j => φ (a j)) (fun j => φ (b j)) f := by
  rw [disc, disc, ← map_line φ, Polynomial.derivative_map, ← AlgHom.coe_toRingHom, ← Polynomial.resultant_map_map]

end GlobalTheory.PencilDisc
