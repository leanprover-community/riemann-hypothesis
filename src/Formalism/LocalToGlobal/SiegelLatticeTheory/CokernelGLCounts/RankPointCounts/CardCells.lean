module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CellRelIff
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioConjSub
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

open scoped Classical

namespace Formalism.L2.SG.Pf.CountAb

variable {G 𝒳 : Type} [Group G] [MulAction G 𝒳]
variable (W : 𝒳) (S N' K : Subgroup G) (π : G →* G) (g : G)

def cellEquiv (hD : Data W S N' K π) :
    Quotient (Setoid.ker (Formalism.L2.SG.Pf.ProdEP2Core.dcMap (Ak S K) (πk W S N' K π hD) (Hk W K g))) ≃
      Quotient (cellRel W N' K g) := by
  refine Equiv.ofBijective (Quotient.lift (fun k => (⟦toCell W S N' K π g hD k⟧ : Quotient (cellRel W N' K g)))
    (fun k₁ k₂ h => ?_)) ⟨?_, ?_⟩
  · apply Quotient.sound
    exact (cellRel_iff W S N' K π g hD k₁ k₂).2
      ((Formalism.L2.SG.Pf.ProdEP2Core.dcMap_eq_iff (Ak S K) (πk W S N' K π hD) (Hk W K g) k₁ k₂).1 h)
  · intro x y hxy
    induction x using Quotient.inductionOn with
    | h k₁ =>
      induction y using Quotient.inductionOn with
      | h k₂ =>
        apply Quotient.sound
        have h2 := Quotient.exact hxy
        exact (Formalism.L2.SG.Pf.ProdEP2Core.dcMap_eq_iff (Ak S K) (πk W S N' K π hD) (Hk W K g) k₁ k₂).2
          ((cellRel_iff W S N' K π g hD k₁ k₂).1 h2)
  · intro y
    induction y using Quotient.inductionOn with
    | h c =>
      obtain ⟨k, rfl⟩ := toCell_surj W S N' K π g hD c
      exact ⟨⟦k⟧, rfl⟩

theorem card_cells (hD : Data W S N' K π) :
    Nat.card (Quotient (cellRel W N' K g)) = ((Hk W K g).map (πk W S N' K π hD)).index := by
  rw [← Nat.card_congr (cellEquiv W S N' K π g hD)]
  exact Formalism.L2.SG.Pf.ProdEP2Core.card_dc (Ak S K) (πk W S N' K π hD) (Hk W K g) (πk_id W S N' K π hD)

end Formalism.L2.SG.Pf.CountAb
