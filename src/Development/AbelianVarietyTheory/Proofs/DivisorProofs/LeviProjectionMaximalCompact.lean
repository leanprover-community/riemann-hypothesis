module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UNInjective
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
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

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.LeviFubini

theorem levH_fst_entry {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ} (h : a + b = n) (w : Pl E)
    (p : parB h w) (i j : Fin a) :
    ((levH h w p).1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j =
      ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
        (GlobalTheory.SmGL.stdSum h (Sum.inl i)) (GlobalTheory.SmGL.stdSum h (Sum.inl j)) := rfl

theorem levH_snd_entry {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ} (h : a + b = n) (w : Pl E)
    (p : parB h w) (i j : Fin b) :
    ((levH h w p).2 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j =
      ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
        (GlobalTheory.SmGL.stdSum h (Sum.inr i)) (GlobalTheory.SmGL.stdSum h (Sum.inr j)) := rfl

theorem levH_mem_KGL_of_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (p : GlobalTheory.LeviFubini.parB h w), (p : GLw n w) ∈ GlobalTheory.LFun.KGL w (n := n) →
      (GlobalTheory.LeviFubini.levH h w p).1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ (GlobalTheory.LeviFubini.levH h w p).2 ∈ GlobalTheory.LFun.KGL w (n := b) := by
  intro E _ _ _ a b n h w p hp
  have hp' := GlobalTheory.AdelicU.mem_GLint_iff.1 hp
  have hinv1 : ((levH h w p).1)⁻¹ = (levH h w p⁻¹).1 := by rw [map_inv, Prod.fst_inv]
  have hinv2 : ((levH h w p).2)⁻¹ = (levH h w p⁻¹).2 := by rw [map_inv, Prod.snd_inv]
  refine ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩,
    GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · rw [levH_fst_entry]; exact hp'.1 _ _
  · rw [hinv1, levH_fst_entry]; exact hp'.2 _ _
  · rw [levH_snd_entry]; exact hp'.1 _ _
  · rw [hinv2, levH_snd_entry]; exact hp'.2 _ _

end GlobalTheory.LeviFubini
