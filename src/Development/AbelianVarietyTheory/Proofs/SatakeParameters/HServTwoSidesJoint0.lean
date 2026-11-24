module

public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.HermitianForms.ExtraSym
public import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.KernelLattices.TopLawQ
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.hServTwoSidesJoint0 : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (C : ColsTiedSym D) (full : ColsFullS C), g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → ∀ u, Joint0 g.herm.lev0 u (g.forms u) := by
  intro D Gt c g C full hh hf u
  rw [hh, hf]
  have e : full.1.to0.lev0 = C.herm.base.lev0 :=
    congrArg (fun X : Formalism.L2.Herm.ColsHermS D => X.base.lev0) full.2
  rw [e]
  exact C.joint0 u
