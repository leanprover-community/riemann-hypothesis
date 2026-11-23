module

import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.IsSemisimpleRing
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ZNClosed
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Trace

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Nil.Orb.Ofib

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem trace_ne_zero_of_idem [CharZero k] {e : Matrix (Fin n) (Fin n) k} (he : IsIdempotentElem e) (h0 : e ≠ 0) :
    trace e ≠ 0 := by
  have he' : IsIdempotentElem (Matrix.toLin' e) := by
    have h2 : Matrix.toLin' (e * e) = Matrix.toLin' e := by rw [he.eq]
    rw [Matrix.toLin'_mul] at h2
    exact h2
  intro h
  apply h0
  have ht : LinearMap.trace k (Fin n → k) (Matrix.toLin' e) = 0 := by
    rw [LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin n)), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin']
    exact h
  have h1 := (LinearMap.IsIdempotentElem.trace_eq_zero_iff (e := Matrix.toLin' e) he').1 ht
  exact Matrix.toLin'.injective (by rw [h1, map_zero])


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem exists_pow_eq {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) :
    ∃ (m : ℕ) (d : Matrix (Fin n) (Fin n) k), d ∈ Z ∧ c ^ m = c ^ (m + 1) * d := by
  let W : ℕ → Submodule k (Matrix (Fin n) (Fin n) k) := fun j =>
    (Subalgebra.toSubmodule Z).map (LinearMap.mulLeft k (c ^ j))
  have hmono : ∀ j, W (j + 1) ≤ W j := by
    intro j x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
    refine Submodule.mem_map.2 ⟨c * y, Z.mul_mem hc hy, ?_⟩
    simp [pow_succ, mul_assoc]
  have hex : ∃ j, W (j + 1) = W j := by
    by_contra hne
    push Not at hne
    have hlt : ∀ j, Module.finrank k (W (j + 1)) < Module.finrank k (W j) := fun j =>
      Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (hmono j) (hne j))
    have hb : ∀ j, Module.finrank k (W j) + j ≤ Module.finrank k (W 0) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => have := hlt j; omega
    have h1 := hb (Module.finrank k (Matrix (Fin n) (Fin n) k) + 1)
    have h2 := Submodule.finrank_le (W 0)
    omega
  obtain ⟨m, hm⟩ := hex
  have hcm : c ^ m ∈ W m := Submodule.mem_map.2 ⟨1, Z.one_mem, by simp⟩
  rw [← hm] at hcm
  obtain ⟨d, hd, e⟩ := Submodule.mem_map.1 hcm
  exact ⟨m, d, hd, by simpa using e.symm⟩


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem eq_zero_of_trace [CharZero k] {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z)
    {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) (h : ∀ b ∈ Z, trace (b * c) = 0) : c = 0 := by
  apply PositivityTheory.RgUd.T.Nil.Four.Alg.trZ_nondeg <;> assumption


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem qZ_add (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x y : Matrix (Fin n) (Fin n) k) :
    qZ Z (x + y) = qZ Z x + qZ Z y := by
  funext i
  simp [qZ, mul_add, trace_add]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem qZ_sub (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x y : Matrix (Fin n) (Fin n) k) :
    qZ Z (x - y) = qZ Z x - qZ Z y := by
  funext i
  simp [qZ, mul_sub, trace_sub]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem qZ_nil (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {x : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z)
    (hn : IsNilpotent x) : qZ Z x = 0 := by
  funext i
  have hb : ((Module.finBasis k Z i : Z) : Matrix (Fin n) (Fin n) k) ∈ Z := (Module.finBasis k Z i).2
  have hcomm : Commute ((Module.finBasis k Z i : Z) : Matrix (Fin n) (Fin n) k) x := hx _ hb
  have := Matrix.isNilpotent_trace_of_isNilpotent (hcomm.isNilpotent_mul_left hn)
  simpa [qZ] using this.eq_zero


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem qZ_inj [CharZero k] {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) {c c' : Matrix (Fin n) (Fin n) k}
    (hc : c ∈ Z) (hc' : c' ∈ Z) (h : qZ Z c = qZ Z c') : c = c' := by
  have h0 : qZ Z (c - c') = 0 := by rw [qZ_sub, h, sub_self]
  rw [← sub_eq_zero]
  refine eq_zero_of_trace hZ (Z.sub_mem hc hc') fun b hb => ?_
  let ℓ : Z →ₗ[k] k :=
    { toFun := fun a => trace ((a : Matrix (Fin n) (Fin n) k) * (c - c'))
      map_add' := fun a b => by simp [add_mul, trace_add]
      map_smul' := fun a b => by simp [trace_smul] }
  have hℓ : ℓ = 0 := (Module.finBasis k Z).ext fun i => by
    have := congrFun h0 i
    simpa [qZ, ℓ] using this
  exact congrArg (fun f : Z →ₗ[k] k => f ⟨b, hb⟩) hℓ


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem qZ_surj [CharZero k] {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z)
    (y : Fin (Module.finrank k Z) → k) : ∃ c ∈ Z, qZ Z c = y := by
  let φ : Z →ₗ[k] (Fin (Module.finrank k Z) → k) :=
    { toFun := fun c => qZ Z (c : Matrix (Fin n) (Fin n) k)
      map_add' := fun a b => qZ_add Z a b
      map_smul' := fun a b => by funext i; simp [qZ, trace_smul] }
  have hinj : Function.Injective φ := fun a b h => Subtype.ext (qZ_inj hZ a.2 b.2 h)
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨c, hc⟩ := hsurj y
  exact ⟨c, c.2, hc⟩


theorem fibZN [CharZero k] : FibZN (k := k) := by
  intro n Z hZ y
  obtain ⟨c, hc, hcy⟩ := qZ_surj hZ y
  refine ⟨c, hc, hcy, fun x hx => ⟨fun ⟨hqy, c', hc', hnil⟩ => ?_, fun hnil => ⟨?_, c, hc, hnil⟩⟩⟩
  · have hx' : x - c' ∈ Bz Z := fun a ha => by
      rw [mul_sub, sub_mul, hx a ha, hZ.1 a ha c' hc']
    have h1 : qZ Z x = qZ Z c' := by
      have := qZ_nil Z hx' hnil
      rw [qZ_sub, sub_eq_zero] at this
      exact this
    have : c' = c := qZ_inj hZ hc' hc (by rw [← h1, hqy, hcy])
    rwa [this] at hnil
  · have hx' : x - c ∈ Bz Z := fun a ha => by
      rw [mul_sub, sub_mul, hx a ha, hZ.1 a ha c hc]
    have := qZ_nil Z hx' hnil
    rw [qZ_sub, sub_eq_zero] at this
    rw [this, hcy]

end PositivityTheory.RgUd.T.Nil.Orb.Ofib
