module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsorModelFilteredColimit
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_torsor_model_filtered_colimit : ∀ (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Type) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j),
    (∀ i (h : i ≤ i), f i i h = RingHom.id (R i)) →
    (∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (f j k hjk).comp (f i j hij) = f i k (hij.trans hjk)) →
    ∀ (B : Type) [CommRing B] (g : ∀ i, R i →+* B),
    (∀ i j (h : i ≤ j), (g j).comp (f i j h) = g i) →
    (∀ b : B, ∃ i x, g i x = b) →
    (∀ i x, g i x = 0 → ∃ j, ∃ h : i ≤ j, f i j h x = 0) →
    ∀ (q : ℕ), 0 < q →
    ∀ (D : Type) [CommRing D] [Algebra B D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor B D q act →
    ∃ i, letI : Algebra (R i) B := (g i).toAlgebra
      ∃ (Di : Type) (_ : CommRing Di) (_ : Algebra (R i) Di)
        (acti : Multiplicative (ZMod q) →* (Di ≃ₐ[R i] Di)),
        GlobalTheory.KeyOriginCut.IsZTorsor (R i) Di q acti ∧ Nonempty (TensorProduct (R i) B Di ≃ₐ[B] D) := by
  first | (exact @GlobalTheory.TorsorColimElem.exists_torsor_model_of_elements) | (exact GlobalTheory.TorsorColimElem.exists_torsor_model_of_elements) | (intros; apply GlobalTheory.TorsorColimElem.exists_torsor_model_of_elements  <;> assumption)
