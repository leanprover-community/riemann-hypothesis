module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

theorem exists_isPt_primitiveRoot {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P)
    {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)
    (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) :
    ∃ (ζ : ↥LL.1) (τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1), H.IsPt h i ζ τ ∧ IsPrimitiveRoot ζ (l ^ s) := by
  have hs : 1 ≤ s := h.1
  have hLL := h.2.2.2
  have hprim : IsPrimitiveRoot (P.ζQ s) (l ^ s) := by
    obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
    have hpow : ∀ k, P.ζQ (k + 1) ^ l ^ k = P.ζQ 1 := by
      intro k
      induction k with
      | zero => simp
      | succ j ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
    have h1 : ¬ P.ζQ (m + 1) ^ l ^ m = 1 := by rw [hpow]; exact P.ζQ_one
    have h2 : P.ζQ (m + 1) ^ l ^ (m + 1) = 1 := by
      rw [pow_succ, pow_mul, hpow, P.ζQ_succ, P.ζQ_zero]
    have h3 := orderOf_eq_prime_pow h1 h2
    rw [← h3]
    exact IsPrimitiveRoot.orderOf _
  have hmem : P.ζQ s ∈ Ks K s :=
    (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ l ^ s = 1} ≤ Ks K s)
      (IntermediateField.subset_adjoin _ _ hprim.pow_eq_one)
  let Φ : Om l →ₐ[ℚ_[l]] Om l := ((H.W K s LL h).emb i).liftNormal (Om l)
  have hΦ : ∀ x : ↥(K0 K), Φ (x : Om l) = (((H.W K s LL h).emb i x : ↥LL.1) : Om l) := fun x =>
    AlgHom.liftNormal_commutes ((H.W K s LL h).emb i) (Om l) x
  let τ₀ : ↥(Ks K s) →ₐ[ℚ_[l]] Om l := Φ.comp (Ks K s).val
  let τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1 := τ₀.codRestrict LL.1.toSubalgebra (hLL τ₀)
  have hτ : ∀ y : ↥(Ks K s), ((τ y : ↥LL.1) : Om l) = Φ (y : Om l) := fun _ => rfl
  refine ⟨τ ⟨P.ζQ s, hmem⟩, τ, ⟨?_, ?_⟩, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    rw [hτ, hxy, hΦ]
  · intro y hy
    congr 1
    exact Subtype.ext hy
  · have h1 : IsPrimitiveRoot (⟨P.ζQ s, hmem⟩ : ↥(Ks K s)) (l ^ s) :=
      IsPrimitiveRoot.of_map_of_injective (f := (Ks K s).val) hprim (Ks K s).val.injective
    exact h1.map_of_injective τ.injective

end GlobalTheory
