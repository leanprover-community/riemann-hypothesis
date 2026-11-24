module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsNatSmulSingle
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem hgt_one_components : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ → (∀ v, ∀ k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV V Λ v k = 1) ∧ (∀ κ ∈ GfC V, ∀ w, GlobalTheory.AdelicU.projArch D.sp.cm.sig V.gram w κ = 1) ∧ ∀ b ∈ GinfC V, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v b = 1 := by
  intro D V Λ hΛ
  haveI : Submodule.IsFullLattice D.host.E Λ := Formalism.IndefR.Fin.PDA.selfDual_isFullLattice V Λ hΛ
  refine ⟨fun v k hk => ?_, fun κ hκ w => ?_, fun b hb v => ?_⟩
  · have hK := (GlobalTheory.Doubling.ioH_mem_KFin (L := Λ) (GlobalTheory.Doubling.gram_hdbl V) (g := k) (g' := 1)).2 ⟨hk, one_mem _⟩
    have := GlobalTheory.Doubling.hgtH_of_mem (GlobalTheory.Doubling.continuous_absEv v) (GlobalTheory.Doubling.isCompact_KFin v) hK
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV
    exact_mod_cast this
  · exact GlobalTheory.AdelicU.mem_finPts_iff_forall.1 hκ w
  · exact GlobalTheory.AdelicU.mem_infPts_iff_forall.1 hb v

end GlobalTheory.ChainOnto
