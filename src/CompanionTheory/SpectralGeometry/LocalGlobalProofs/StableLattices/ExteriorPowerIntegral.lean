module

public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompoundMatrixCauchyBinetProperties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker ContDiff

namespace GlobalTheory.CompanionTheory.ZuckWedge

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_minor {n l : ℕ} (a b : Fin l → Fin n) :
    ContDiff ℝ ∞ fun g : Matrix (Fin n) (Fin n) ℂ => (g.submatrix a b).det := by
  simp only [det_apply']
  refine ContDiff.sum fun σ _ => ?_
  refine contDiff_const.mul ?_
  refine contDiff_prod fun i _ => ?_
  simp only [submatrix_apply]
  fun_prop

theorem okWedge : OKWedge := by
  intro k r l
  refine FRep.OK.mk ?_ ?_ ?_ ?_
  · exact GlobalTheory.compound_one _ l
  · intro g _ h _
    exact GlobalTheory.compound_mul l g h
  · intro c d g₀ _
    exact ⟨Set.univ, fun g => BranchingSupport.cmp l g c d, isOpen_univ, Set.mem_univ _,
      (contDiff_minor _ _).contDiffOn, fun g _ _ => rfl⟩
  · refine ⟨(Fintype.card (Equiv.Perm (Fin l)) : ℝ), fun g _ c d => ?_⟩
    have hent : ∀ i j, ‖g i j‖ ≤ Formalism.FourierDecayAlt.B.gN g := by
      intro i j
      have h2 : ‖g i j‖ ^ 2 ≤ ∑ i', ∑ j', Complex.normSq (g i' j') := by
        rw [Complex.sq_norm]
        calc Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
              Finset.single_le_sum (fun j' _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
          _ ≤ ∑ i', ∑ j', Complex.normSq (g i' j') :=
              Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
                (fun i' _ => Finset.sum_nonneg fun j' _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
      calc ‖g i j‖ = |‖g i j‖| := (abs_of_nonneg (norm_nonneg _)).symm
        _ ≤ _ := Real.abs_le_sqrt h2
    show ‖(g.submatrix _ _).det‖ ≤ _
    rw [det_apply']
    refine (norm_sum_le _ _).trans ?_
    calc ∑ σ : Equiv.Perm (Fin l), ‖((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, g.submatrix _ _ (σ i) i‖
        ≤ ∑ σ : Equiv.Perm (Fin l), Formalism.FourierDecayAlt.B.gN g ^ l := by
          refine Finset.sum_le_sum fun σ _ => ?_
          have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
          rw [norm_mul, hs, one_mul, norm_prod]
          calc ∏ i, ‖g.submatrix _ _ (σ i) i‖ ≤ ∏ _i : Fin l, Formalism.FourierDecayAlt.B.gN g :=
                Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hent _ _)
            _ = Formalism.FourierDecayAlt.B.gN g ^ l := by simp
      _ = (Fintype.card (Equiv.Perm (Fin l)) : ℝ) * Formalism.FourierDecayAlt.B.gN g ^ l := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end GlobalTheory.CompanionTheory.ZuckWedge
