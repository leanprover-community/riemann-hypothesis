module

public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.HeckeStdStatement
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAct
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverF
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverFP
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.BasicNotions

namespace Formalism.L2

section Rfl

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

end Rfl

theorem heckeStdPlain_of_statement (h : ReciprocityTheory.ChartRestriction.L3H.HeckeStdStatement) : HeckeStdPlain := by
  intro L _ _ _ n a J χ B hJo hB s ϖ k hs hu hk1 hk2
  exact h L n a.W a.ρ a.alg J χ B hJo hB s ϖ k hs hu hk1 hk2

theorem linkEtaTw_of_statement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : ReciprocityTheory.ChartRestriction.L3H.HeckeStdStatement)
    (hfam : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (_ : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M ∧ SplitEx (Fm.D x i)) :
    LocsCoverTwF Fm :=
  linkEtaTw_of_plain Fm (heckeStdPlain_of_statement h) hfam

end Formalism.L2
