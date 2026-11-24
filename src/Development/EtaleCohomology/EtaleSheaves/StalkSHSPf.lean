module

public import Development.EtaleCohomology.EtaleSheaves.FibStalkPf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial LateralTheory.E.t_E2Cut LateralTheory.E.FibStalkPf

namespace LateralTheory.E.StalkSHSPf

theorem germs (S : Scheme.{0}) (x : S) (c : ℕ → S.presheaf.stalk x) (s : Finset ℕ) :
    ∃ (U : S.Opens) (_ : IsAffineOpen U) (hx : x ∈ U) (f : ℕ → Γ(S, U)),
      ∀ i ∈ s, (S.presheaf.germ U x hx).hom (f i) = c i := by
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨U, hU, hx, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
      (show x ∈ (⊤ : S.Opens) from trivial)
    exact ⟨U, hU, hx, fun _ => 0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨U, hU, hx, f, hf⟩ := ih
    obtain ⟨V, hxV, g, hg⟩ := S.presheaf.exists_germ_eq (c a)
    obtain ⟨W, hW, hxW, hWUV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
      (show x ∈ U ⊓ V from ⟨hx, hxV⟩)
    refine ⟨W, hW, hxW, fun i => if i = a then (S.presheaf.map (homOfLE (hWUV.trans inf_le_right)).op).hom g
       else (S.presheaf.map (homOfLE (hWUV.trans inf_le_left)).op).hom (f i), ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simp only [if_true]
      rw [← hg, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]
    · have : i ≠ a := fun h => ha (h ▸ hi)
      simp only [this, if_false]
      rw [← hf i hi, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]

theorem stalkAIC : StalkAIC := by
  intro S hS x p hm hd
  obtain ⟨U, hU, hx, f, hf⟩ := germs S x (fun i => p.coeff i) (Finset.range (p.natDegree + 1))
  have hl : p ∈ Polynomial.lifts (S.presheaf.germ U x hx).hom := by
    refine (lifts_iff_coeff_lifts p).2 fun i => ?_
    by_cases hi : i < p.natDegree + 1
    · exact ⟨f i, hf i (Finset.mem_range.2 hi)⟩
    · exact ⟨0, by rw [map_zero, coeff_eq_zero_of_natDegree_lt (by omega)]⟩
  obtain ⟨P, hP, hdeg, hPm⟩ := lifts_and_natDegree_eq_and_monic hl hm
  obtain ⟨r, hr⟩ := hS.2 U hU ⟨x, hx⟩ P hPm (by omega)
  exact ⟨(S.presheaf.germ U x hx).hom r, by rw [← hP, Polynomial.eval_map, eval₂_at_apply, hr, map_zero]⟩

end LateralTheory.E.StalkSHSPf
