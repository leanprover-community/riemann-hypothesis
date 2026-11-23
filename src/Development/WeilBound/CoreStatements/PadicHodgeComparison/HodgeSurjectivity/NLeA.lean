module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveRes
public import Mathlib.RingTheory.RingHom.Etale
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

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CrystallineSemistableComparison.Onto

structure ChartRings (K : Type) [Field K] (A : Type) [CommRing A] [Algebra K A] (n d : ℕ) where
  x : Fin n → A
  t : Fin d → A
  etale : (MvPolynomial.aeval (R := K) (Sum.elim x t) : MvPolynomial (Fin n ⊕ Fin d) K →ₐ[K] A).toRingHom.Etale
  R : Finset (Fin d) → Type
  [cr : ∀ S, CommRing (R S)]
  [alg : ∀ S, Algebra K (R S)]
  res : ∀ {S T : Finset (Fin d)}, S ⊆ T → (R S →ₐ[K] R T)
  res_id : ∀ (S : Finset (Fin d)) (h : S ⊆ S) y, res h y = y
  res_comp : ∀ {S T U : Finset (Fin d)} (h : S ⊆ T) (h' : T ⊆ U) y, res h' (res h y) = res (h.trans h') y
  base : R ∅ ≃ₐ[K] A

  u : ∀ (S : Finset (Fin d)) (k : Fin d), k ∈ S → Fin d → R S
  t_eq : ∀ (S : Finset (Fin d)) (k : Fin d) (hk : k ∈ S) (j : Fin d),
    res (Finset.empty_subset S) (base.symm (t j)) = res (Finset.empty_subset S) (base.symm (t k)) * u S k hk j
  u_res : ∀ {S T : Finset (Fin d)} (h : S ⊆ T) (k : Fin d) (hk : k ∈ S) (j : Fin d), res h (u S k hk j) = u T k (h hk) j

  chart_surj : ∀ k : Fin d,
    letI : Algebra A (R {k}) := ((res (Finset.empty_subset {k})).toRingHom.comp base.symm.toRingHom).toAlgebra
    Function.Surjective (MvPolynomial.aeval (R := A) (S₁ := R {k}) (u {k} k (Finset.mem_singleton_self k)))
  chart_ker : ∀ k : Fin d,
    letI : Algebra A (R {k}) := ((res (Finset.empty_subset {k})).toRingHom.comp base.symm.toRingHom).toAlgebra
    RingHom.ker (MvPolynomial.aeval (R := A) (S₁ := R {k}) (u {k} k (Finset.mem_singleton_self k))).toRingHom =
      Ideal.span (insert (MvPolynomial.X k - 1) (Set.range fun j => MvPolynomial.C (t j) - MvPolynomial.C (t k) * MvPolynomial.X j))

  loc : ∀ (S : Finset (Fin d)) (k : Fin d) (hk : k ∈ S),
    letI : Algebra (R {k}) (R S) := (res (Finset.singleton_subset_iff.2 hk)).toRingHom.toAlgebra
    IsLocalization.Away (∏ j ∈ S, u {k} k (Finset.mem_singleton_self k) j) (R S)

attribute [instance] ChartRings.cr ChartRings.alg

variable {K : Type} [Field K] {A : Type} [CommRing A] [Algebra K A] {n d : ℕ}

def ChartRings.I (C : ChartRings K A n d) (S : Finset (Fin d)) : Ideal (C.R S) :=
  Ideal.span {y | ∃ k, (S = ∅ ∨ k ∈ S) ∧ y = C.res (Finset.empty_subset S) (C.base.symm (C.t k))}

def ChartFormsCechExact : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A : Type) [CommRing A] [Algebra K A] (n d : ℕ), 0 < d → ∀ (C : ChartRings K A n d)
    (a : ℕ) (P : PM.{0} K (Fin d)) (e : ∀ S, P.M S ≃ₗ[K] relOm K (C.I S) a),
    (∀ {S T : Finset (Fin d)} (h : S ⊆ T) (y : P.M S),
      ((e T (P.res h y) : relOm K (C.I T) a) : Om K (C.R T) a) = omMap (C.res h) a ((e S y : relOm K (C.I S) a) : Om K (C.R S) a)) →
    P.Ex

end CrystallineSemistableComparison.Onto
