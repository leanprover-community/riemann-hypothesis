module

public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.BaseSt
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasBrg
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodGA
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
import Mathlib.Tactic.Linter.Style
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

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open scoped TensorProduct Matrix

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} (fr : UI.Frames D V)

def kf (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) : Set (UI.instV fr).Gf :=
  {y | (y.1 : GL (Fin V.rank) (Lev.EAf D)) ∈ K}

theorem brg_mem_levA (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (x : (UI.instV fr).GA) :
    UI.brg fr x ∈ Lev.levA V K ↔ x.1 = 1 ∧ x.2 ∈ kf fr K := by
  show UI.brg fr x ∈ GfC V ⊓ K.comap (Lev.finE V) ↔ _
  rw [Subgroup.mem_inf, Subgroup.mem_comap, brg_mem_GfC, finE_brg]
  rfl

theorem kf_isCompact_isOpen_of_levelA (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (hK : IsLevelA V K) :
    IsCompact (kf fr K) ∧ IsOpen (kf fr K) := by
  have hpre : kf fr K = jf fr ⁻¹' (Lev.levA V K : Set (GA D V)) := by
    ext y
    show y ∈ kf fr K ↔ UI.brg fr (1, y) ∈ Lev.levA V K
    rw [brg_mem_levA]
    exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  refine ⟨?_, ?_⟩
  · rw [hpre]
    exact (jf_isClosedEmbedding fr).isCompact_preimage hK.1
  · have hmem : ∀ y, jf fr y ∈ GfC V := fun y => (brg_mem_GfC fr (1, y)).mpr rfl
    let jc : (UI.instV fr).Gf → GfC V := fun y => ⟨jf fr y, hmem y⟩
    have hjc : Continuous jc := (jf_isClosedEmbedding fr).continuous.subtype_mk _
    have e : kf fr K = jc ⁻¹' (((Lev.levA V K).subgroupOf (GfC V)) : Set (GfC V)) := by
      rw [hpre]
      ext y
      simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf, jc]
    rw [e]
    exact hK.2.preimage hjc


end Formalism.IndefR.Eqv

end
