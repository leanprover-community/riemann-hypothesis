module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGramClassRepsSelfDualLatticeGroup
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.exists_gramClass_reps_selfDualLattice_group : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    (Valued.v δ = 1 ∧ σ δ = -δ) → (∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1) →
    (∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∀ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a ∧
      (∀ y : Matrix (Fin n') (Fin n) L, GlobalTheory.Hk3.HoweG.HomA σ JS JT x y ↔
        ∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
      (∀ v : Fin n → L, (∀ i, v i ∈ Formalism.UG.intL L) →
        ((∃ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ u) ↔
          ∀ i, (x *ᵥ v) i ∈ Formalism.UG.intL L)) ∧
      (∀ w : Fin n → L, (∃ u v : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, v i ∈ Formalism.UG.intL L) ∧
          w = (a : Matrix (Fin n) (Fin n) L) *ᵥ u + v) ↔
        ∃ v : Fin n → L, ∃ w' : Fin n' → L, (∀ i, v i ∈ Formalism.UG.intL L) ∧ (∀ i, w' i ∈ Formalism.UG.intL L) ∧
          w = v + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w') →
    ∃ Y : Finset (Matrix (Fin n') (Fin n) L), x ∈ Y ∧ (∀ y ∈ Y, GlobalTheory.Hk3.HoweG.HomA σ JS JT x y) ∧
      (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n → y = y') ∧
      ∃ (B : Type) (_ : AddCommGroup B) (_ : Fintype B) (b0 : B → GL (Fin n) L)
        (l : B → Matrix (Fin n') (Fin n) L → Matrix (Fin n') (Fin n) L),
        (∀ b, GlobalTheory.Hk3.HoweG.SelfDual σ JS (b0 b)) ∧
        (∀ b, ∀ y ∈ Y, l b y ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n ∧
          ∃ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧
            y + l b y = u * (((b0 b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) ∧
        (∀ b, ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
          ∃ y ∈ Y, u * (((b0 b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - (y + l b y) ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n) ∧
        (∀ b b', ∀ y ∈ Y, ψ (-((GlobalTheory.Hk3.locH σ δ JS JT y (l (b + b') y) + σ (GlobalTheory.Hk3.locH σ δ JS JT y (l (b + b') y))) / 2)) = ψ (-((GlobalTheory.Hk3.locH σ δ JS JT y (l b y) + σ (GlobalTheory.Hk3.locH σ δ JS JT y (l b y))) / 2)) * ψ (-((GlobalTheory.Hk3.locH σ δ JS JT y (l b' y) + σ (GlobalTheory.Hk3.locH σ δ JS JT y (l b' y))) / 2))) ∧
        (∀ y ∈ Y, GlobalTheory.Hk3.HoweG.GramEq σ JT x y ↔ ∀ b, ψ (-((GlobalTheory.Hk3.locH σ δ JS JT y (l b y) + σ (GlobalTheory.Hk3.locH σ δ JS JT y (l b y))) / 2)) = ψ (-((GlobalTheory.Hk3.locH σ δ JS JT x (l b x) + σ (GlobalTheory.Hk3.locH σ δ JS JT x (l b x))) / 2))) := by
  first | exact @GlobalTheory.Hk3.GramSep.gram_class_family | exact GlobalTheory.Hk3.GramSep.gram_class_family | (intros; apply GlobalTheory.Hk3.GramSep.gram_class_family <;> assumption)
