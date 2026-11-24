module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonListLength
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CategoryTheory Polynomial

namespace GlobalTheory.SerCmp

open Formalism.IrreducibleCountingLemmas.TYPES

theorem hasLabel_of_hasLabelO : ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod g)} (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) C), (∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple V → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V → GlobalTheory.GLq.IsCuspOf L (O.lab d V) (fun x => V.character x)) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b → ∀ x : GL (Fin r) (ZMod g), LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x) = GlobalTheory.GLq.hcL (GlobalTheory.SerCmp.canonList b lam) r x) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) (τ : FDRep ℂ (GL (Fin r) (ZMod g))), CategoryTheory.Simple τ → (Formalism.IrreducibleCountingLemmas.TYPES.IsConstituent τ (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam) ↔ GlobalTheory.GLq.ip (fun x => τ.character x) (fun x => LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x)) ≠ 0)) → ∀ (r : ℕ) (τ : FDRep ℂ (GL (Fin r) (ZMod g))) (f : (ZMod g)[X]), CategoryTheory.Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.HasLabelO O τ f → GlobalTheory.GLq.HasLabel L (fun x => τ.character x) f := by
  intro g _ L C O h1 h2 h3 r τ f hτ hL
  obtain ⟨s, b, lam, hb, hl, hcon, rfl⟩ := hL
  have hc : ∀ c, 1 ≤ Fintype.card {i // b i = c} := fun c => by
    obtain ⟨i, hi⟩ := hb c
    exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  let Q : List ((ZMod g)[X] × GlobalTheory.GLq.Pc g) := (List.finRange s).map fun c =>
    (labO O (lam c), ⟨Fintype.card {i // b i = c},
      fun x => (transp (Fintype.equivFin {i // b i = c}) (lam c)).character x⟩)
  have hQ : Q.map Prod.snd = canonList b lam := by
    simp only [Q, canonList, List.map_map]
    rfl
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [Q, List.mem_map] at hp
    obtain ⟨c, -, rfl⟩ := hp
    exact h1 _ _ (hc c) (Formalism.L2.PT.simple_transp _ (hl c).1) (Formalism.L2.PT.isCuspidal_transp _ (hl c).2)
  · rw [hQ]
    unfold GlobalTheory.GLq.degL canonList
    rw [List.map_map]
    have e : ((List.finRange s).map ((fun p : GlobalTheory.GLq.Pc g => p.1) ∘ fun c : Fin s =>
        (⟨Fintype.card {i // b i = c},
          fun x => (transp (Fintype.equivFin {i // b i = c}) (lam c)).character x⟩ : GlobalTheory.GLq.Pc g))).sum =
        ∑ c : Fin s, Fintype.card {i // b i = c} := by
      rw [Fin.sum_univ_def]
      rfl
    rw [e, ← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv b), Fintype.card_fin]
  · simp only [Q, List.map_map]
    rw [Fin.prod_univ_def]
    rfl
  · rw [hQ]
    have ht : (fun x => LinearMap.trace ℂ (hcSpace (ZMod g) b lam) (hcRep (ZMod g) b lam x)) =
        GlobalTheory.GLq.hcL (canonList b lam) r := funext (h2 r s b lam hb)
    have := (h3 r s b lam τ hτ).1 hcon
    rw [ht] at this
    exact this

end GlobalTheory.SerCmp
