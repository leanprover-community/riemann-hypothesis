module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.DimFormula
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.compDim :
    ∀ {R : Type} [CommRing R] [IsNoetherianRing R], CohenType R → ∀ (p q : Ideal R) (s : Finset R), p.IsPrime →
      q ∈ (p ⊔ Ideal.span (s : Set R)).minimalPrimes → ringKrullDim (R ⧸ p) ≤ ringKrullDim (R ⧸ q) + s.card := by
  classical
  intro R _ _ hC p q s hp hq
  have hpq : p ≤ q := le_sup_left.trans hq.1.2
  haveI := hp
  haveI := hq.1.1
  obtain ⟨-, hDF⟩ := dimFormula (hC p hp)
  set f := Ideal.Quotient.mk p
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f ≤ q := by rw [Ideal.mk_ker]; exact hpq
  haveI hQ : (q.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hker
  have hmin : q.map f ∈ (Ideal.span ((s.image f : Finset (R ⧸ p)) : Set (R ⧸ p))).minimalPrimes := by
    rw [Finset.coe_image, ← Ideal.map_span, Ideal.minimalPrimes_map_of_surjective hf]
    refine ⟨q, ?_, rfl⟩
    rw [Ideal.mk_ker, sup_comm]
    exact hq
  have hh : (q.map f).height ≤ s.card :=
    (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin).trans
      (by exact_mod_cast Finset.card_image_le)
  have e := hDF (q.map f)
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hpq)] at e
  rw [← e, add_comm]
  gcongr
  exact_mod_cast hh
