module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open scoped Classical TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.NormSteps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X) {u : D.what₂.Word}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂)

def colDS (h h' : Hfin X u) : X.B.I.Gf := ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)

def LeviOntoS : Prop :=
  ∀ (q : {Λ // Λ ∈ what₂}) (s : Iof TR), ∃ h : Hfin X u,
    colDS (cs.h (cs.base q.1)) h ∈ X.B.I.Kset ∧ colDS h (cs.h (cs.base q.1)) ∈ X.B.I.Kset ∧
      levi TR (colDS (cs.h (cs.base q.1)) h) = s

def ColLatRepS (hK : X.LevelSubgroupCharacter) : Prop :=
  ∀ (q : {Λ // Λ ∈ what₂}) (h : Hfin X u) (ρ : cs.Cl) (γ : Gam X u) (κ : Ku X u hK),
    colDS (cs.h (cs.base q.1)) h ∈ X.B.I.Kset → h = iotaF X u γ * cs.h ρ * (κ : Hfin X u) → cs.lamOf ρ = q.1

end Formalism.L2.SG.Pf.NormSteps
