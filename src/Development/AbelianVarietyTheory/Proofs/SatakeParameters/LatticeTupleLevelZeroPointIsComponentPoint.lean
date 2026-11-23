module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryPt
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Realises
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem latticeTupleLevelZero_point_isComponentPoint : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (La : (sysS H X std).Lt 0), ((sysS H X std).Pj 0).IsLatTup La.2 → ∃ g : ∀ v, GL (Fin (((sysS H X std).Pj 0).m + 1)) (((sysS H X std).Pj 0).Qq v), (∀ v, La.2 v = colSpan (((sysS H X std).Pj 0).W v) (g v).1) ∧ (lev0At J.Gd u w hg).A.IsPt La.1 g (J.pt std 0 (Nat.zero_le _) La).1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD La hLa
  obtain ⟨⟨hr, he⟩, -⟩ := hD 0 (Nat.zero_le _) La hLa
  simp only [Joint.cp, cpAt, chAt] at he
  refine ⟨basesAt (chainAt H hT) std _ _ _ _ _ _ _ 0 La.2, fun v => ?_, ?_⟩
  · unfold basesAt
    obtain ⟨g0, hg0⟩ := Formalism.MainNotions.G.KAat.exists_bases1 La.2 hLa
    exact Classical.epsilon_spec (⟨g0 v, hg0 v⟩ : ∃ g : GL (Fin (((sysS H X std).Pj 0).m + 1)) (((sysS H X std).Pj 0).Qq v),
      La.2 v = colSpan (((sysS H X std).Pj 0).W v) (g : Matrix _ _ _))
  · rw [he]
    convert (Classical.epsilon_spec (GlobalTheory.TwU.exists_unitary_pt J.one.good La.1
      (basesAt (chainAt H hT) std _ _ _ _ _ _ _ 0 La.2))).1 using 1
    ext i j
    rfl

end GlobalTheory.TwV.DelA
