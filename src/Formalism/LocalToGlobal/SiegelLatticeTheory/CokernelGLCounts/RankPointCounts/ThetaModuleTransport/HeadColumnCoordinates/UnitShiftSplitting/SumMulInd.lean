module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.SumIndL
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem ite_ind (a b : Fin (r + 1)) (x : F) :
    (if b = Fin.last r ∧ a = Fin.last r then x else 0) = ind r a b * x := by
  unfold ind
  by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;> simp [ha, hb]

theorem sum_mul_ind (x : Fin (r + 1) → F) (b : Fin (r + 1)) (u : F) :
    ∑ a, x a * (ind r a b * u) = if b = Fin.last r then x (Fin.last r) * u else 0 := by
  have : ∑ a, x a * (ind r a b * u) = (∑ a, x a * ind r a b) * u := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun a _ => by ring
  rw [this, sum_ind_l]
  split_ifs <;> simp

section Rows

variable (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (c : Ix r → M.L.O)

abbrev GG : Matrix (Ix r) (Ix r) E :=
  gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')

theorem row_inl (b : Fin (r + 1)) :
    g.e (∑ i, (c i : E) * GG (g := g) Zh T T' i (Sum.inl b)) =
      (∑ a, (g.q : F)⁻¹ * (g.e (Zh b a)).1 * (g.e (c (Sum.inr a) : E)).1 +
          (if b = Fin.last r then (g.q : F)⁻¹ * T * (g.e (c (Sum.inr (Fin.last r)) : E)).1 -
            T * (g.e (c (Sum.inl (Fin.last r)) : E)).1 else 0),
        ∑ a, (g.q : F)⁻¹ * (g.e (Zh b a)).2 * (g.e (c (Sum.inr a) : E)).2 +
          (if b = Fin.last r then (g.q : F)⁻¹ * T * (g.e (c (Sum.inr (Fin.last r)) : E)).2 -
            T * (g.e (c (Sum.inl (Fin.last r)) : E)).2 else 0)) := by

  rw [map_sum, Fintype.sum_sum_type]
  simp only [map_mul, e_gram]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.fst_sum, Prod.fst_mul]
    have h1 : ∑ a, (g.e (c (Sum.inl a) : E)).1 * (ind r a b * -T) =
        if b = Fin.last r then (g.e (c (Sum.inl (Fin.last r)) : E)).1 * -T else 0 := sum_mul_ind _ _ _
    have h2 : ∑ a, (g.e (c (Sum.inr a) : E)).1 * ((g.q : F)⁻¹ * ((g.e (Zh b a)).1 + ind r a b * T)) =
        ∑ a, (g.q : F)⁻¹ * (g.e (Zh b a)).1 * (g.e (c (Sum.inr a) : E)).1 +
          ∑ a, (g.e (c (Sum.inr a) : E)).1 * (ind r a b * ((g.q : F)⁻¹ * T)) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun a _ => by ring
    rw [h1, h2, sum_mul_ind]
    split_ifs <;> ring
  · simp only [Prod.snd_add, Prod.snd_sum, Prod.snd_mul]
    have h1 : ∑ a, (g.e (c (Sum.inl a) : E)).2 * (ind r a b * -T) =
        if b = Fin.last r then (g.e (c (Sum.inl (Fin.last r)) : E)).2 * -T else 0 := sum_mul_ind _ _ _
    have h2 : ∑ a, (g.e (c (Sum.inr a) : E)).2 * ((g.q : F)⁻¹ * ((g.e (Zh b a)).2 + ind r a b * T)) =
        ∑ a, (g.q : F)⁻¹ * (g.e (Zh b a)).2 * (g.e (c (Sum.inr a) : E)).2 +
          ∑ a, (g.e (c (Sum.inr a) : E)).2 * (ind r a b * ((g.q : F)⁻¹ * T)) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun a _ => by ring
    rw [h1, h2, sum_mul_ind]
    split_ifs <;> ring

theorem row_inr (b : Fin (r + 1)) :
    g.e (∑ i, (c i : E) * GG (g := g) Zh T T' i (Sum.inr b)) =
      (∑ a, ((g.q : F)⁻¹ * (g.e (Zh a b)).2 * (g.e (c (Sum.inl a) : E)).1 +
            (g.q : F)⁻¹ * (g.q : F)⁻¹ * (-(g.e (Zh b a)).1 - (g.e (Zh a b)).2) * (g.e (c (Sum.inr a) : E)).1) +
          (if b = Fin.last r then (g.q : F)⁻¹ * T * (g.e (c (Sum.inl (Fin.last r)) : E)).1 -
            (g.q : F)⁻¹ * (g.q : F)⁻¹ * (T + T') * (g.e (c (Sum.inr (Fin.last r)) : E)).1 else 0),
        ∑ a, ((g.q : F)⁻¹ * (g.e (Zh a b)).1 * (g.e (c (Sum.inl a) : E)).2 +
            (g.q : F)⁻¹ * (g.q : F)⁻¹ * (-(g.e (Zh b a)).2 - (g.e (Zh a b)).1) * (g.e (c (Sum.inr a) : E)).2) +
          (if b = Fin.last r then (g.q : F)⁻¹ * T * (g.e (c (Sum.inl (Fin.last r)) : E)).2 -
            (g.q : F)⁻¹ * (g.q : F)⁻¹ * (T + T') * (g.e (c (Sum.inr (Fin.last r)) : E)).2 else 0)) := by

  rw [map_sum, Fintype.sum_sum_type]
  simp only [map_mul, e_gram]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.fst_sum, Prod.fst_mul]
    have h : ∀ a, (g.e (c (Sum.inl a) : E)).1 * ((g.q : F)⁻¹ * ((g.e (Zh a b)).2 + ind r a b * T)) +
        (g.e (c (Sum.inr a) : E)).1 * ((g.q : F)⁻¹ * (g.q : F)⁻¹ *
          (-(g.e (Zh b a)).1 - (g.e (Zh a b)).2 - ind r a b * (T + T'))) =
        ((g.q : F)⁻¹ * (g.e (Zh a b)).2 * (g.e (c (Sum.inl a) : E)).1 +
            (g.q : F)⁻¹ * (g.q : F)⁻¹ * (-(g.e (Zh b a)).1 - (g.e (Zh a b)).2) * (g.e (c (Sum.inr a) : E)).1) +
          ((g.e (c (Sum.inl a) : E)).1 * (ind r a b * ((g.q : F)⁻¹ * T)) +
            (g.e (c (Sum.inr a) : E)).1 * (ind r a b * (-((g.q : F)⁻¹ * (g.q : F)⁻¹ * (T + T'))))) := by
      intro a; ring
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun a _ => h a]
    simp only [Finset.sum_add_distrib, sum_mul_ind]
    split_ifs <;> ring
  · simp only [Prod.snd_add, Prod.snd_sum, Prod.snd_mul]
    have h : ∀ a, (g.e (c (Sum.inl a) : E)).2 * ((g.q : F)⁻¹ * ((g.e (Zh a b)).1 + ind r a b * T)) +
        (g.e (c (Sum.inr a) : E)).2 * ((g.q : F)⁻¹ * (g.q : F)⁻¹ *
          (-(g.e (Zh b a)).2 - (g.e (Zh a b)).1 - ind r a b * (T + T'))) =
        ((g.q : F)⁻¹ * (g.e (Zh a b)).1 * (g.e (c (Sum.inl a) : E)).2 +
            (g.q : F)⁻¹ * (g.q : F)⁻¹ * (-(g.e (Zh b a)).2 - (g.e (Zh a b)).1) * (g.e (c (Sum.inr a) : E)).2) +
          ((g.e (c (Sum.inl a) : E)).2 * (ind r a b * ((g.q : F)⁻¹ * T)) +
            (g.e (c (Sum.inr a) : E)).2 * (ind r a b * (-((g.q : F)⁻¹ * (g.q : F)⁻¹ * (T + T'))))) := by
      intro a; ring
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun a _ => h a]
    simp only [Finset.sum_add_distrib, sum_mul_ind]
    split_ifs <;> ring

end Rows

end Formalism.L2.SG.LocalCountModules.AlgGSplit
