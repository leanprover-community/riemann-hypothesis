module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.OrthZero
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.TwTrSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.piFinOf_pf :
    PiAdm → TensType → CvType → CvIn → TypeIn → PiFin := by
  intro hA hT hC hI hY E _ _ _ n hn D π hπ μa μb ha hb Ma Mb κ ka kb va vb R ψ U h1 h2 h3 h4 h5 i j
  obtain ⟨ht, K, W, k1, k2, w1, w2, hl⟩ := hT E n μa μb ha hb Ma Mb κ ka kb va vb R ψ U h1 h2 h3 h4 h5 i j
  obtain ⟨Y, y1, y2, y3⟩ := hA E n hn π hπ K W k1 w1
  refine ⟨Y, y1, y2, fun u hu φ hφ => ?_⟩
  obtain ⟨s0, s1⟩ := hI E n hn D π hπ φ hφ
  obtain ⟨s2, s3, -⟩ := s1 _ u ht hu
  have ty := hC E n D K W _ u φ.1 k2 w1 ht hl hu s0.1
  obtain ⟨φ', m, e⟩ := hY E n hn D π hπ K W k1 k2 w1 w2 _ s2 s3 ty
  refine ⟨φ', y3 φ' m ?_, fun x => congrFun e x⟩
  rw [← e] at ty
  exact ty
