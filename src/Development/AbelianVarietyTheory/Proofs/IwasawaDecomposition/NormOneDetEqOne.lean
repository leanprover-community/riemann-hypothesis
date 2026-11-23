module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer

@[expose] public section

namespace GlobalTheory.Mem.Col2.IdxEx

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem apply_single_of_mem_unip {F : Type} [Field F] {n c : ℕ} {r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)}
    (hr : r ∈ Loc.N1 F n c) (s l : Fin (n + c)) (hl : s ≤ l) :
    r (Pi.single s 1) l = (Pi.single s 1 : Fin (n + c) → F) l := by
  obtain ⟨h1, h2⟩ := hr
  by_cases hs : s.1 < n
  · have e : (Pi.single s 1 : Fin (n + c) → F) = Loc.inX F n c (Pi.single ⟨s.1, hs⟩ 1) := by
      funext m
      by_cases hm : m.1 < n
      · simp [Loc.inX, hm, Pi.single_apply, Fin.ext_iff]
      · have : m ≠ s := fun h => hm (h ▸ hs)
        simp [Loc.inX, hm, this]
    rw [e, h2]
  · have e : (Pi.single s 1 : Fin (n + c) → F) = Loc.eN F (n + c) (n + (s.1 - n)) := by
      funext m
      have : n + (s.1 - n) = s.1 := by omega
      simp [Loc.eN, this, Pi.single_apply, Fin.ext_iff]
    have h3 := h1.1.2.2 (s.1 - n) l (by
      have : s.1 ≤ l.1 := hl
      simp only [Set.mem_setOf_eq]
      omega)
    rw [e]
    exact sub_eq_zero.1 h3

theorem det_eq_one_of_mem_unip :
    ∀ (F : Type) [Field F] (n c : ℕ), ∀ r ∈ Loc.N1 F n c, LinearEquiv.det r = 1 := by
  intro F _ n c r hr
  apply Units.ext
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix', Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun s _ => ?_
    have := apply_single_of_mem_unip hr s s le_rfl
    rw [LinearMap.toMatrix'_apply]
    simpa using this
  · intro l s hls
    have hls' : s < l := hls
    have := apply_single_of_mem_unip hr s l hls'.le
    rw [LinearMap.toMatrix'_apply]
    simpa [hls'.ne'] using this

end GlobalTheory.Mem.Col2.IdxEx
