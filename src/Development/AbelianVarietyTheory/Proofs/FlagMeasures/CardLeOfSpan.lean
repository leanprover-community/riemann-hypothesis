module

public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
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

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S.Lat
open scoped Classical

namespace GlobalTheory.GenericOrder

theorem mem_locP' {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    (L : Submodule R W) (x : W) : x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s, s ∉ p ∧ s • x ∈ L := Iff.rfl

theorem frame_mem {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
    (Λ : Submodule (𝓞 E) S.V) {T : E} (F : LFlag S r T) (hL : IsLift Λ F) (hF : ∀ b, frame F b ∈ Λ)
    (b : Fin (r + 1)) : frame F b ∈ XLam Λ F ⊔ Submodule.span (𝓞 E) {F.zt} := by
  have hb := hF b
  induction b using Fin.lastCases with
  | last =>
    refine Submodule.mem_sup_right (Submodule.subset_span ?_)
    simp [frame, Formalism.MainNotions.S.FlagG.fvec, hL.2]
  | cast i =>
    refine Submodule.mem_sup_left ⟨hb, ?_⟩
    have : frame F i.castSucc = F.fl.e i := by simp [frame, Formalism.MainNotions.S.FlagG.fvec]
    rw [this]
    exact Submodule.subset_span (s := Set.range F.fl.e) ⟨i, rfl⟩

end GlobalTheory.GenericOrder
