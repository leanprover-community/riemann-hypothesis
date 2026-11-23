module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section Words

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def rWord (ε : Fin n → Bool) (D : List (Matrix (Fin n) (Fin n) ℂ)) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  D.foldr (fun Z F => EcV ε Z F) f

def hWord (D : List (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  D.foldr (fun Z G => Rhol Z G) F

def lWord (D : List (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  D.foldr (fun Z G => Lhol Z G) F

end Words

def adW (ε : Fin n → Bool) (k : KG ε) (D : List (Matrix (Fin n) (Fin n) ℂ)) :
    List (Matrix (Fin n) (Fin n) ℂ) :=
  D.map fun Z => toMK k⁻¹ * Z * toMK k

def PhiP (μ : Fin n → ℤ) (z : Matrix (Fin n) (Fin n) ℂ) : ℂ := PhiM μ z⁻¹

def OmegaP (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) := {z | z⁻¹ ∈ OmegaSet n}

def PsMWordInterface (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (Λ : Fin n → ℝ) (T : KType ε Λ) (μ : Fin n → ℤ),
    ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ posSet n ⊆ U ∧
      (∀ z ∈ U, ∀ k : KG ε, toMK k⁻¹ * z * toMK k ∈ OmegaSet n) ∧
      ∀ D : List (Matrix (Fin n) (Fin n) ℂ),
        DifferentiableOn ℂ (lWord D (psM T μ)) U ∧
        (∀ z ∈ U, Continuous fun k : KG ε => lWord (adW ε k D) (PhiM μ) (toMK k⁻¹ * z * toMK k)) ∧
        ∀ z ∈ U, lWord D (psM T μ) z =
          ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
            ∫ k, lWord (adW ε k D) (PhiM μ) (toMK k⁻¹ * z * toMK k) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε)

def TransferStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ),
    IsHCParam lam → IsMu lam μ →
    ∀ (N : ℕ) (D : Fin N → List (Matrix (Fin n) (Fin n) ℂ)) (v : Fin N → T.V),
      (∀ (k : KG ε) (z : Matrix (Fin n) (Fin n) ℂ), z ∈ OmegaP n →
          ∑ i, ⟪T.op k T.w, v i⟫_ℂ * hWord (adW ε k (D i)) (PhiP μ) z = 0) →
      ∀ g : Matrix (Fin n) (Fin n) ℂ, inUJ ε g → ∑ i, rWord ε (D i) (PsiM T μ) g (v i) = 0

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
