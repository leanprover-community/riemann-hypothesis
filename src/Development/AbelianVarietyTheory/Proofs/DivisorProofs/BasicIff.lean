module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.ENatToNat
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.HilbAff

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {r : ℕ} {T : Scheme.{0}}

abbrev subStr (y : (functor A B r).obj (op T)) : y.2.1.subscheme ⟶ T :=
  y.2.1.subschemeι ≫ pullback.snd _ y.1

def Sec (y : (functor A B r).obj (op T)) (U : T.Opens) : Type :=
  Γ(y.2.1.subscheme, subStr A B y ⁻¹ᵁ U)

instance (y : (functor A B r).obj (op T)) (U : T.Opens) : CommRing (Sec A B y U) :=
  inferInstanceAs (CommRing Γ(y.2.1.subscheme, subStr A B y ⁻¹ᵁ U))

instance (y : (functor A B r).obj (op T)) (U : T.Opens) : Algebra Γ(T, U) (Sec A B y U) :=
  ((subStr A B y).app U).hom.toAlgebra

def gen (y : (functor A B r).obj (op T)) (U : T.Opens) (b : B) : Sec A B y U :=
  ((y.2.1.subschemeι ≫ pullback.fst _ y.1).appLE ⊤ (subStr A B y ⁻¹ᵁ U) (by simp)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)

def coord {N : ℕ} (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N)
    (y : (functor A B r).obj (op T)) (U : T.Opens) : (Fin r → Γ(T, U)) →ₗ[Γ(T, U)] Sec A B y U :=
  Fintype.linearCombination Γ(T, U) (fun k => gen A B y U (e (σ k)))

theorem basic_iff {N : ℕ} (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N)
    (y : (functor A B r).obj (op T)) :
    Basic A B e σ y ↔ ∀ U : T.affineOpens, Function.Bijective (coord A B e σ y U) := Iff.rfl

end GlobalTheory.HilbAff
