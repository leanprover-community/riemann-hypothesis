module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionFormDegZeroCocycleClosed
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

theorem _root_.GlobalTheory.T.connectionForm_degZeroCocycle_closed : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (h : C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) → ∀ (k : K.K) (θ : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))), θ = h _ _ (jet0 k) - h _ _ (jet1 k) → θ.fst = 0 ∧ ∀ a b, dw a (θ.snd b) = dw b (θ.snd a) := by
  first | exact @GlobalTheory.AnPer.ClosedSq.connForm_closed | exact GlobalTheory.AnPer.ClosedSq.connForm_closed | (intros; apply GlobalTheory.AnPer.ClosedSq.connForm_closed <;> assumption)
