module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem UpperTheory.Reformulated.B.Glb2.fock_dec_k :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E]
      [inst_4 : Algebra F E] {σ : E →ₐ[F] E} {d : PositivityTheory.SiegelWeilFormula.SD_k σ} (R : PositivityTheory.SiegelWeilFormula.RD_k d)
      (w : NumberField.InfinitePlace F),
      ∀ f ∈ R.fock,
        ∃ (k : ℕ) (P : Fin k → PositivityTheory.Rg.Sw.PX d.m d.n) (Ψ : Fin k → PositivityTheory.SiegelWeilFormula.Mx F E d.m d.n → ℂ),
          (∀ (i : Fin k), Ψ i ∈ R.away w) ∧ f = ∑ i : Fin k, R.tens w (PositivityTheory.SiegelWeilFormula.fP (P i)) (Ψ i) := by
  intro F E _ _ _ _ _ σ d R w f hf
  obtain ⟨k, c, u, rfl⟩ := Submodule.mem_span_set'.1 hf
  choose P g hg hu using fun i => (u i).2
  refine ⟨k, fun i => P i w, fun i => c i • _, fun i => Submodule.smul_mem _ (c i)
    (Submodule.subset_span ⟨P i, g i, hg i, rfl⟩), Finset.sum_congr rfl fun i _ => ?_⟩
  rw [hu i]
  funext X
  simp only [PositivityTheory.SiegelWeilFormula.RD_k.tens, Pi.smul_apply, smul_eq_mul]
  rw [mul_left_comm (PositivityTheory.SiegelWeilFormula.fP _ _), ← mul_assoc (PositivityTheory.SiegelWeilFormula.fP _ _),
    @Finset.mul_prod_erase _ _ _ (_) _ (fun v => PositivityTheory.SiegelWeilFormula.fP (P i v) (R.loc v X)) _
      (Finset.mem_univ w)]
