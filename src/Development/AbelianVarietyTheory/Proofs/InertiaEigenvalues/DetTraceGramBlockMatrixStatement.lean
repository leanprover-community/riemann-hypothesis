module

public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Trace.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetTraceGramBlockMatrix
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


theorem _root_.GlobalTheory.T.det_trace_gram_block_eq_pow_mul_norm_det : ∀ {E E' : Type} [Field E] [Field E'] [Algebra E E'] [FiniteDimensional E E'] {d n : ℕ} (w : Module.Basis (Fin d) E E') (H : Matrix (Fin n) (Fin n) E') (v : Fin d → E'), (Matrix.of fun (p q : Fin d × Fin n) => Algebra.trace E E' (w p.1 * H p.2 q.2 * v q.1)).det = (Matrix.of fun k l => Algebra.trace E E' (w k * v l)).det ^ n * Algebra.norm E H.det := by
  first | exact @GlobalTheory.det_traceGram_blockMatrix | exact GlobalTheory.det_traceGram_blockMatrix | (intros; apply GlobalTheory.det_traceGram_blockMatrix <;> assumption)
