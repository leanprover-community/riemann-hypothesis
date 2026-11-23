module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnfoldingAffineSpaceMemIffIntrinsic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnfoldingCharacterArgumentCompUnipotentRadicals
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

namespace GlobalTheory.Proof.unfoldingCharArg_mul_left_unipotent

theorem chArg_left : ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ r ∈ Loc.R1 F n c, ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (t : Loc.FC n' c' n c → F), Loc.chArg (r.toLinearMap ∘ₗ Loc.xx1 xj t) = Loc.chArg (Loc.xx1 xj t) + Loc.n1Arg r := by
  intro F _ n' c' n c hc hc' r hr xj t
  obtain ⟨-, -, h3⟩ := (GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic F n' c' n c hc hc' xj (Loc.xx1 xj t)).1 ⟨t, rfl⟩
  generalize Loc.xx1 xj t = x at h3
  have e : Loc.n1Arg r = ∑ i ∈ Finset.range c, Loc.atN (r (Loc.eN F (n + c) (n + (i + 1)))) (n + i) := by
    obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
    rw [Finset.sum_range_succ, GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.eN_eq_zero (F := F) (N := n + (d + 1)) (i := n + (d + 1)) (by omega),
      map_zero]
    have z : Loc.atN (0 : Fin (n + (d + 1)) → F) (n + d) = 0 := by
      unfold Loc.atN
      split_ifs <;> rfl
    rw [z, add_zero]
    rfl
  rw [e]
  unfold Loc.chArg
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have b3 := atN_of_R1cond hr.1 (h3 (i + 1))
  have b4 : Loc.atN (Loc.eN F (n + c) (n + (i + 1))) (n + i) = 0 := GlobalTheory.Proof.unfoldingCharacterArgument_comp_unipotentRadicals.atN_eN_succ _ _
  simp only [map_sub, atN_sub, b4] at b3
  change Loc.atN (r (x (Loc.eN F (n' + c') (n' + (i + 1))))) (n + i) =
    Loc.atN (x (Loc.eN F (n' + c') (n' + (i + 1)))) (n + i) + _
  linear_combination b3

end GlobalTheory.Proof.unfoldingCharArg_mul_left_unipotent
