module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.PoincareInHH.Cut

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def NeatKu (hK : X.LevelSubgroupCharacter) : Prop := Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK)

def GamFinKu (hK : X.LevelSubgroupCharacter) : Prop :=
  ∀ (h : Hfin X u) (γ : Gam X u), h⁻¹ * iotaF X u γ * h ∈ Ku X u hK → IsOfFinOrder γ

def GamUnipKu (hK : X.LevelSubgroupCharacter) : Prop :=
  ∀ (h : Hfin X u) (γ : Gam X u), h⁻¹ * iotaF X u γ * h ∈ Ku X u hK → IsOfFinOrder γ → γ = 1

theorem cols_dim_of_neat (hK : X.LevelSubgroupCharacter) (hN : NeatKu X u hK) (hC : ClassFin X u hK) :
    FiniteDimensional ℂ (Cu X u hK) ∧
      Module.finrank ℂ (Cu X u hK) =
        Module.finrank ℂ (X.Vpi u) * Nat.card (Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u hK)) := by
  exact Formalism.L2.SG.ColsDim.columns_dimension _ _ _ ℂ (X.Vpi u) (iotaI X u) (iotaF X u) (Ku X u hK) (Ku X u hK)
    (psiK X u hK) (piRep X u) le_rfl hN hC inferInstance

end Formalism.L2.SG.PoincareInHH.Cut
