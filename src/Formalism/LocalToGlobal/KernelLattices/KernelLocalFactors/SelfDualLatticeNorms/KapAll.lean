module

public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.KapNon
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.LiftOneFormsToCompatibleApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.KS

open Formalism.MainNotions
open Formalism.L2.Th1.H (IsSelfDual)

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem kappaAt_of (hsd : IsSelfDual (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) B.latA) (hcc : cc ≠ ⊥) (h0 : δ ≠ 0)
    (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) : B.KappaAt p ι := by
  by_cases hs : SplitK D p
  · exact kappaAt_split B hsd p ι hs
  · exact kappaAt_nonsplit_of B h0 hcc p hs ι (kappa_norm_nonsplit B.kc ι hs)

theorem kappaAt (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) :
    B.KappaAt p ι :=
  kappaAt_of B (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.selfDual B hcc hδ) hcc.1 (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D cc δ B) p ι

theorem kappaAll (D : D7) : KappaAll D :=
  fun _ _ B hcc hδ p _ ι _ => kappaAt B hcc hδ p ι

theorem kappaSplit (D : D7) : KappaSplit D :=
  fun _ _ B hcc hδ p _ ι _ => kappaAt B hcc hδ p ι

end Formalism.L2.Ker.KS
