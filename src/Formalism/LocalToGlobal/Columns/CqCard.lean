module

public import Formalism.LocalToGlobal.Columns.UnfoldingPhiCompLeftUnipotentSource
public import Formalism.LocalToGlobal.Columns.ReductionColumnStandardBasis
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

@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

theorem cq_card {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : Nat.card (𝓞 E ⧸ P.asIdeal) = qOf P := by
  unfold qOf
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem cq_covT : TruncatedUnfoldingChangeOfVarsTarget := by
  intro E _ _ _ P K _ n' c' n c hc hp hu psi D a b e hadd hint Ψ hsupp haD hinv r hr g hgI hg hre _ heD A B hA hbB _ wt y
  subst hc
  exact finite_sum_target_equality (ciQ_mem P) hu hp (cq_card P) psi hadd hint Ψ hsupp haD hinv r hr g hgI hg hre heD hA hbB wt y

end Formalism.L2.Col
