module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinOrd
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

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.PoincareInHH.Cut.GU

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def piG (v : VA X.B.I) : VA X.B.I :=
  v - ∑ a, hA X.B.I (X.f0 a) v • X.e0 a - ∑ a, hA X.B.I (X.e0 a) v • X.f0 a + hA X.B.I X.z0 v • X.z0
    - ∑ i, hA X.B.I (X.bwd i) v • X.bw i - ∑ i, hA X.B.I (X.bw i) v • X.bwd i

def ProjModG : Prop := ∀ v ∈ X.B.I.Lf, piG X v ∈ mL X.B.I X.B.g

def UnipCore : Prop :=
  ∀ κ : X.B.I.Gf, κ ∈ X.K2 → κ⁻¹ ∈ X.K2 →
  ∀ Y : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I), Y ≤ X.B.I.Lf →
    (∀ v ∈ Y, X.B.I.fmat κ *ᵥ v ∈ Y) →
    (∀ v ∈ Y, (∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) v) ∧ ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) v)) ∧
      ZMod' X.B.I X.B.g (hA X.B.I X.z0 v)) →
    ∀ v ∈ Y, ((X.B.I.fmat κ - 1) ^ D.R.k) *ᵥ v ∈ mL X.B.I X.B.g

def CoreOfProj : Prop := ProjModG X → UnipCore X

def GlobalCondition (hK : X.LevelSubgroupCharacter) : Prop := LatOfLattice X u → UnipCore X → GamUnipKu X u hK

theorem gamUnipKu_of_projModG (hK : X.LevelSubgroupCharacter) (hP : ProjModG X) (hC : CoreOfProj X) (hG : GlobalCondition X u hK)
    (hL : LatOfLattice X u) : GamUnipKu X u hK :=
  hG hL (hC hP)

end Formalism.L2.SG.PoincareInHH.Cut.GU
