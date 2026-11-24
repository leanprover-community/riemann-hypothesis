module

public import Formalism.SatakeDualWeyl.StatementF
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Algebra.Valued.ValuativeRel
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace

open Matrix Formalism.UG ValuativeRel
open scoped TensorProduct
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsUWeilPair)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.LFun (HasSatU)

def str (q : ℂˣ) (n : ℤ) : Multiset ℂˣ := (Multiset.range n.toNat).map fun j : ℕ => q ^ (2 * (j : ℤ) - (n - 1))

section Valued

variable (E : Type) [Field E] [Valued E (WithZero (Multiplicative ℤ))]

def nu (z : Circle) : Eˣ →* Circle :=
  (zpowersHom Circle z⁻¹).comp ((WithZero.unitsWithZeroEquiv (α := Multiplicative ℤ)).toMonoidHom.comp
    (Units.map (Valued.v : Valuation E (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom.toMonoidHom))

def chi (n : ℕ) : Eˣ →* Circle := nu E (Circle.exp Real.pi ^ n)

variable {E}

variable {n : ℕ}

def IsSelfDualLat (c : E →+* E) (S : Matrix (Fin n) (Fin n) E) (L : Submodule (intL E) (Fin n → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin n → E)) = ⊤ ∧
    ∀ x, x ∈ L ↔ ∀ y ∈ L, x ⬝ᵥ S *ᵥ (fun i => c (y i)) ∈ intL E

def IsHypFrame (c : E →+* E) (S : Matrix (Fin n) (Fin n) E) (L : Submodule (intL E) (Fin n → E)) (P : GL (Fin n) E) :
    Prop :=
  (∀ y : Fin n → E, P.1 *ᵥ y ∈ L ↔ ∀ i, y i ∈ intL E) ∧
    ∃ u : E, Valued.v u = 1 ∧ P.1ᵀ * S * P.1.map c = u • antiJ E n

end Valued

section Local

variable {F : Type} [Field F] {E : Type} [Field E] [Valued E (WithZero (Multiplicative ℤ))] [Algebra F E]
  (c : E →ₐ[F] E) {n : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]

end Local

section Res

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]


variable {F} in
def IsUnramAdd (ϖ : F) (ψ : AddChar F ℂ) : Prop :=
  (∀ x ∈ 𝒪[F], ψ x = 1) ∧ ∃ x ∈ 𝒪[F], ψ (ϖ⁻¹ * x) ≠ 1

end Res

end GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace

end
