module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.IsStrictDom
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.TwistedIndependenceLemma.TwistedIndependence
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
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.Eig

def EigInert : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), ¬ IsSplitAt w →
    ∀ (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (q : ℕ) (σ : SmIrr (UL n w)) (α : Fin (n / 2) → ℂˣ),
    IsWitt n w b → IsUnifAt ϖ → IsUnramInv (ϖ : w.adicCompletion E) (cj w) q → IsAdmissible σ.ρ →
    SatUL b (ϖ : w.adicCompletion E) q σ α →
    ∃ β : Fin (n / 2) → ℂˣ, GlobalTheory.LGrp.WeylConjU α β ∧ (∀ i j : Fin (n / 2), i ≤ j → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖) ∧
      (∀ i, 1 ≤ ‖(β i : ℂ)‖) ∧ ∃ y ∈ fixed σ.ρ (iwU n w b), y ≠ 0 ∧ ∀ l : Fin (n / 2) → ℤ, Cone l →
        levOp σ.ρ (KL n w) (iwU n w b) (fU n w b ϖ l) LinearMap.id y =
          ((((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)⁻¹ * dlt n w l * pw β l) • y

def AbsEig : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (α : Fin (n / 2) → ℂˣ),
    IsUnramInv ϖ σ q → IsAdmissible ρ → ρ.IsIrreducible → GlobalTheory.LFun.HasSatU ϖ q ρ α →
    ∃ β : Fin (n / 2) → ℂˣ, GlobalTheory.LGrp.WeylConjU α β ∧ (∀ i j : Fin (n / 2), i ≤ j → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖) ∧
      (∀ i, 1 ≤ ‖(β i : ℂ)‖) ∧ ∃ y : fixed ρ (PositivityTheory.SphericalProduct.IwU σ n), y ≠ 0 ∧
        ∀ t : GU σ n, PositivityTheory.SphericalProduct.IsDiagM (t : GL (Fin n) L) → PositivityTheory.SphericalProduct.IsStrictDom (t : GL (Fin n) L) →
          ∀ U : Module.End ℂ (fixed ρ (PositivityTheory.SphericalProduct.IwU σ n)), PositivityTheory.Lbc.IsHeckeOpG ρ (PositivityTheory.SphericalProduct.IwU σ n) (t : GU σ n) U →
            U y = chiDeltaU q (fun i => (β i : ℂ)) t • y

def HeckeSum : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V), IsSmooth ρ → ∀ (K J : Subgroup G), IsOpen (J : Set G) → IsCompact (K : Set G) → J ≤ K →
    ∀ (t : G) (U : Module.End ℂ (fixed ρ J)), PositivityTheory.Lbc.IsHeckeOpG ρ J t U → ∀ y : fixed ρ J,
      levOp ρ K J (fun g => if ∃ x ∈ J, ∃ z ∈ J, g = x * t * z then 1 else 0) LinearMap.id (y : V) =
        (((J.relIndex K : ℕ) : ℂ)⁻¹ * (((J.map (MulAut.conj t).toMonoidHom).relIndex J : ℕ) : ℂ)) • ((U y : fixed ρ J) : V)

def IndexU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ),
    IsUnramInv ϖ σ q → ∀ (l : Fin (n / 2) → ℤ), Cone l → ∀ t : GU σ n,
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => ϖ ^ wexp n l i) →
      (((PositivityTheory.SphericalProduct.IwU σ n).map (MulAut.conj t).toMonoidHom).relIndex (PositivityTheory.SphericalProduct.IwU σ n) : ℤ) =
        (q : ℤ) ^ (2 * ∑ i : Fin (n / 2), (((n : ℤ) - 1 - 2 * (i : ℕ)) * l i)).toNat

def EigInertOf : Prop := AbsEig → HeckeSum → IndexU → EigInert

end PositivityTheory.Rg.BcB.F.Eig

end
