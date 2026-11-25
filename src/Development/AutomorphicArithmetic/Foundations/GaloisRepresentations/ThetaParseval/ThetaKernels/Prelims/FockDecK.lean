module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
/-! # FockDecK: Preliminary helper declarations for global theta kernels. -/

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
