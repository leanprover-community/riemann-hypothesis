module

public import Formalism.MoebiusJetDuality.StatementU
public import Formalism.SatakeDualWeyl.Statement
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

@[expose] public section

noncomputable section

open Matrix MeasureTheory
open scoped ComplexOrder

namespace Formalism.DegreeFormula

open Formalism.MJ Formalism.UG

section One

variable {p q : ℕ}

def kapQ (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ :=
  (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₁ * z +
    (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₂

def hQ (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ := 1 - zᴴ * z

def hP (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p) (Fin p) ℂ := 1 - z * zᴴ

end One

section Two

variable {ι : Type} [Fintype ι] {p q r : ℕ}

def DomI (ι : Type) (p q : ℕ) : Set (ι → Matrix (Fin p) (Fin q) ℂ) := {z | ∀ i, z i ∈ hcDom p q}

def UpqI (ι : Type) (p q : ℕ) : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ) :=
  Subgroup.pi Set.univ (fun _ => Upq p q)

def moebI (g : ι → GL (Fin p ⊕ Fin q) ℂ) (z : ι → Matrix (Fin p) (Fin q) ℂ) :
    ι → Matrix (Fin p) (Fin q) ℂ :=
  fun i => moeb (g i : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (z i)

def unflat (v : ι × Fin p × Fin q → ℂ) : ι → Matrix (Fin p) (Fin q) ℂ :=
  fun i => Matrix.of (fun a b => v (i, a, b))

def flat (z : ι → Matrix (Fin p) (Fin q) ℂ) : ι × Fin p × Fin q → ℂ := fun x => z x.1 x.2.1 x.2.2

def DomFlat (ι : Type) (p q : ℕ) : Set (ι × Fin p × Fin q → ℂ) := {v | unflat v ∈ DomI ι p q}

end Two

section Three

variable {ι : Type} [Fintype ι] {p q r : ℕ}

end Three

section Four

variable {ι : Type} [Fintype ι] {p q r : ℕ}

def muD (ι : Type) [Fintype ι] (p q : ℕ) : Measure (ι × Fin p × Fin q → ℂ) :=
  (volume.restrict (DomFlat ι p q)).withDensity
    (fun v => ENNReal.ofReal (∏ i, ((hQ (unflat v i)).det.re) ^ (-((p + q : ℕ) : ℤ))))

def IsFD (Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)) (F : Set (ι × Fin p × Fin q → ℂ)) : Prop :=
  MeasurableSet F ∧ F ⊆ DomFlat ι p q ∧
    (∀ z ∈ DomI ι p q, ∃ γ ∈ Γ, flat (moebI γ z) ∈ F) ∧
    muD ι p q {v | v ∈ F ∧ ∃ γ ∈ Γ, flat (moebI γ (unflat v)) ∈ F ∧ moebI γ (unflat v) ≠ unflat v} = 0

end Four

section Five

variable {ι : Type} [Fintype ι] {p q r : ℕ} {G Gf : Type} [Group G] [Group Gf]

end Five

section CompanionTheory

variable {E : Type} [Field E] {n : Type} [Fintype n] [DecidableEq n] {ι : Type} {p q : ℕ}

def embI (τ : ι → E →+* ℂ) (e : ι → n ≃ Fin p ⊕ Fin q) (P : ι → GL (Fin p ⊕ Fin q) ℂ) :
    GL n E →* (ι → GL (Fin p ⊕ Fin q) ℂ) :=
  MonoidHom.pi (fun i => (MulAut.conj (P i)⁻¹).toMonoidHom.comp
    ((Matrix.GeneralLinearGroup.map (τ i)).comp
      (Units.map (Matrix.reindexAlgEquiv E E (e i)).toMonoidHom)))

end CompanionTheory

section LateralTheory

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

end LateralTheory

end Formalism.DegreeFormula
