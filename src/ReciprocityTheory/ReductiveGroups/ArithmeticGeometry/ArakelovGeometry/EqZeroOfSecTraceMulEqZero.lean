module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.XZeroPowDvdOfIsHomogeneousAeval
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.BasisOfLinearIndependentOfCardEqFinrank

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo Polynomial Module

variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ}

theorem fnField_comp_le (x : κ → Ω) (e : Fin (D + 1) → κ) : fnField (x ∘ e) ≤ fnField x := by
  exact TraceNormBounds.fnField_comp_le' x e

theorem projDeg_pos (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) :
    0 < projDeg x e :=
  TraceNormBounds.projDeg_pos' x e h

def fnTrace (x : κ → Ω) (e : Fin (D + 1) → κ) (t : Ω) : Ω :=
  open Classical in
  if ht : t ∈ fnField x then
    ((Algebra.trace (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le x e)) ⟨t, ht⟩ : fnField (x ∘ e)) : Ω)
  else 0

def secTrace (x : κ → Ω) (e : Fin (D + 1) → κ) (n : ℕ) (s : Ω) : Ω :=
  x (e 0) ^ n * fnTrace x e (s / x (e 0) ^ n)

theorem exists_indep_sections (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) :
    ∃ (k : ℕ) (ε : Fin (projDeg x e) → Ω), (∀ l, ε l ∈ sec ℤ x k) ∧
      LinearIndependent (fnField (x ∘ e)) ε := by
  exact TraceNormBounds.exists_indep_sections' x e h

theorem secTrace_mem (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e) (n : ℕ) {s : Ω}
    (hs : s ∈ sec ℤ x n) : secTrace x e n s ∈ sec ℤ (x ∘ e) n := by
  unfold secTrace fnTrace
  rw [dite_eq_left (TraceNormBounds.sec_div_mem x (e 0) hs)]
  exact TraceNormBounds.trace_mem_sec x e h n hs

theorem eq_zero_of_secTrace_mul_eq_zero (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e)
    {k : ℕ} (ε : Fin (projDeg x e) → Ω) (hε : ∀ l, ε l ∈ sec ℤ x k)
    (hli : LinearIndependent (fnField (x ∘ e)) ε) (n : ℕ) {s : Ω} (hs : s ∈ sec ℤ x n)
    (h0 : ∀ l, secTrace x e (n + k) (s * ε l) = 0) : s = 0 := by
  have hx0 : x (e 0) ≠ 0 := by
    intro h0
    have hmem : (MvPolynomial.X 0 : MvPolynomial (Fin (D + 1)) ℤ) ∈ coordIdeal ℤ (x ∘ e) := by
      rw [coordIdeal, RingHom.mem_ker]
      simp [coneMap, h0]
    rw [h.free] at hmem
    exact MvPolynomial.X_ne_zero 0 ((Ideal.mem_bot).1 hmem)
  refine TraceNormBounds.eq_zero_of_trace' x e h ε hε hli n hs (fun l => ?_)
  have h1 := h0 l
  unfold secTrace fnTrace at h1
  split_ifs at h1 with hm
  · exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ hx0)
  · exact absurd (TraceNormBounds.sec_div_mem x (e 0) (by first | exact TraceNormBounds.mul_mem_sec x hs (hε l) | exact mul_mem_sec x hs (hε l) | exact ReciprocityTheory.ChartRestriction.G.Geo.mul_mem_sec x hs (hε l))) hm

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
