module

public import Formalism.LocalToGlobal.GlobalTheory.DivPassage
public import Formalism.LocalToGlobal.IndefiniteReal.TransferStatement
public import Formalism.LocalToGlobal.IndefiniteReal.AllPartsTransferHolds
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.IndefR.LatticeTransfer

open Formalism.IndefR.TransferLatticeStatement Formalism.HN Formalism.L2.GlobalTheoryTheory.DivPassage

theorem levelAmb_transfer
    {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] {D0 D1 : ℕ}
    (A : LevelAmb K D0 D1) {G : Type} [Group G] [Fintype G] {T : A.S → Type}
    [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)] [∀ s, FiniteDimensional K (T s)]
    (τ : ∀ s, Representation K G (T s)) (H₀ : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ) (H : Subgroup G)
    (χ : H →* (𝓞 K)ˣ) (ρ : Representation K G (Fin A.Dg → K))
    (hτ : IsGood τ) (hM : M1 τ H₀ χ₀)
    (h0 : A.ep0.mulVecLin = epP H₀ χ₀ ρ) (h1 : A.ep1.mulVecLin = epP H χ ρ)
    (hs : ∀ s, (A.es s).mulVecLin = eS (τ s) ρ) (hn : ∀ s, A.nS s = nS (τ s) H χ)
    (hG : A.G = Fintype.card G) (hgood : eGood τ ρ = LinearMap.id)
    (hX : A.FramesG) (hL : Submodule.IsFullLattice K A.Rg) (hst : ∀ g : G, ∀ a ∈ A.Rg, ρ g a ∈ A.Rg)
    (hU : IsUnitaryRep (Pi.basisFun K (Fin A.Dg)) A.Xg ρ) :
    A.Ranks ∧ A.Deg0 ∧ A.Deg1 ∧ (A.latticeAtSharpLevel ≠ ⊥ → A.MaxT) := by
  have h15 := all_parts_transfer_holds
  have hlat : IsGLat ρ A.Rg := by
    have : Submodule.IsFullLattice K A.Rg := hL
    exact ⟨Submodule.IsLattice.fg K A.Rg, Submodule.IsFullLattice.span_eq_top, hst⟩
  have p := h15 K G A.S T τ H₀ χ₀ H χ hτ hM _ _ (Pi.basisFun K (Fin A.Dg)) A.Xg ρ hX hU A.Rg hlat
  have q := h15 K G A.S T τ H₀ χ₀ H₀ χ₀ hτ hM _ _ (Pi.basisFun K (Fin A.Dg)) A.Xg ρ hX hU A.Rg hlat
  have e0 : A.latticeAtBaseLevel = cut A.Rg (epP H₀ χ₀ ρ ∘ₗ eGood τ ρ) := by
    rw [hgood, LinearMap.comp_id, ← h0]; rfl
  have e1 : A.latticeAtSharpLevel = cut A.Rg (epP H χ ρ ∘ₗ eGood τ ρ) := by
    rw [hgood, LinearMap.comp_id, ← h1]; rfl
  have es : ∀ s, A.Rs s = cut A.Rg (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ) := fun s => by
    rw [← h0, ← hs, ← Matrix.mulVecLin_mul]; rfl
  unfold TransferLatticeConditions at p q
  dsimp only at p q
  simp only [← e0, ← e1, ← es, ← hn, ← hG] at p
  have hM' : ∀ s, nS (τ s) H₀ χ₀ = 1 := hM
  simp only [← e0, ← es, hM', one_mul] at q
  obtain ⟨⟨-, r1⟩, ⟨-, -, -, -, -, -, d0⟩, -, ⟨d1, -⟩, m⟩ := p
  have r0 := q.1.2
  have h85 : (8.5 : ℝ) = 17 / 2 := by norm_num
  rw [h85] at d1 m
  refine ⟨⟨r0, r1⟩, ?_, ?_, fun h => (m h).1⟩
  · unfold LevelAmb.Deg0
    rw [r0, Nat.cast_sum]
    exact sub_le_iff_le_add'.1 d0
  · unfold LevelAmb.Deg1
    rw [r1]
    have := (abs_le.1 d1).1
    exact sub_le_iff_le_add.2 (by
      have h2 := neg_le_sub_iff_le_add.1 this
      exact h2)

end Formalism.IndefR.LatticeTransfer
