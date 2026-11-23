module

public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFunApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicFormFnInvIffTwistedSubstitutionMem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Formalism.L2.Forms GlobalTheory.IntegralityCompare

theorem _root_.GlobalTheory.T.automorphicFormFn_inv_iff_twistedSubstitution_mem : ∀ {E ι : Type} [Field E] [Fintype ι] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (s : ι → ℤ)
    (G : ι → Matrix (Fin n) (Fin n) ℂ) (P0 : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (S : AddSubgroup (MvPolynomial (ι × Fin n × Fin n) ℂ)) {Yt : Type} (e : Yt ≃ Frames G) (f : Yt → ℂ),
    (∀ z, f z = fnOf G s 1 P0 (e z)) →
    ((∃ P ∈ S, ∀ z, f z = fnOf G s (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) P (e z)) ↔
      twSub emb M s P0 ∈ S) := by
  first | exact @GlobalTheory.IntegralityCompare.fnOf_inv_iff_twSub_mem | exact GlobalTheory.IntegralityCompare.fnOf_inv_iff_twSub_mem | (intros; apply GlobalTheory.IntegralityCompare.fnOf_inv_iff_twSub_mem <;> assumption)
