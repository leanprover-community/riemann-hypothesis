module

public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

namespace Formalism.IndefR.RationalEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

abbrev inst : Formalism.MainNotions.S.AutInst := Formalism.L2.SG.InstExistsPf.instOf D

def iota : GA D (D.sp.Y 0) ≃ₜ* (inst D).GA :=
  (Formalism.L2.SG.AdBridge.toHA (inst D) (Formalism.L2.SG.Closed.adelic_isomorphism_statement (inst D)).1).symm

theorem iota_symm_isBridge : Formalism.L2.SG.AdBridge.IsBridge (inst D) (iota D).symm :=
  Formalism.L2.SG.AdBridge.toHA_isBridge (inst D) (Formalism.L2.SG.Closed.adelic_isomorphism_statement (inst D)).1

theorem iota_rat (g : GA D (D.sp.Y 0)) : g ∈ GQ (D.sp.Y 0) ↔ iota D g ∈ (inst D).GFset := by
  have hS := Formalism.L2.SG.Closed.adelic_isomorphism_statement (inst D)
  have hb := Formalism.L2.SG.AdBridge.toHA_isBridge (inst D) hS.1
  have hGF := hS.2.1 _ hb
  have hg : Formalism.L2.SG.AdBridge.toHA (inst D) hS.1 (iota D g) = g :=
    (Formalism.L2.SG.AdBridge.toHA (inst D) hS.1).apply_symm_apply g
  rw [← (Formalism.L2.SG.AdBridge.toHA (inst D) hS.1).injective.mem_set_image (a := iota D g)
    (s := (inst D).GFset), hGF, hg]
  exact Iff.rfl

end Formalism.IndefR.RationalEmbedding

end
