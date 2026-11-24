module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceIdemFacts

variable {D : D7}

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]

theorem algebraMap_pairA (α : Af D.host.F) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) := rfl

theorem placeIdem_mem_idAt {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {P : Pl D → Prop} (hP : P v) :
    algebraMap (AF D.host.F) (AE D) ε ∈ idAt D P := by
  obtain ⟨α, rfl, -, h0⟩ := hε
  rw [algebraMap_pairA]
  exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt (fun w hw => h0 w fun h => hw (h ▸ hP)) 1

theorem infPart_placeIdem {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
  obtain ⟨α, rfl, -, -⟩ := hε
  exact TensorProduct.zero_tmul _ _

theorem placeIdem_mul {v v' : Pl D} {ε ε' : AF D.host.F} (hε : IsPlaceIdem D v ε) (hε' : IsPlaceIdem D v' ε')
    (h : v ≠ v') : ε * ε' = 0 := by
  obtain ⟨α, rfl, -, h0⟩ := hε
  obtain ⟨α', rfl, -, h0'⟩ := hε'
  have hαα : α * α' = 0 := by
    apply RestrictedProduct.ext
    intro w
    change evalV D.host.F w (α * α') = evalV D.host.F w 0
    rw [map_mul, map_zero]
    by_cases hw : w = v
    · subst hw
      rw [h0' w h, mul_zero]
    · rw [h0 w hw, zero_mul]
  show ((0 : Ainf D.host.F), α) * ((0 : Ainf D.host.F), α') = 0
  rw [Prod.mk_mul_mk, mul_zero, hαα]
  rfl

theorem idem_facts : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k), cA D (q.e + cA D q.e) = q.e + cA D q.e ∧
      (∀ (P : Pl D → Prop), P q.v → ∀ (m n : ℕ) (w : Mx D m n), IsHalf (q.e + cA D q.e) w →
        MxAt P w ∧ w.map (infPart D) = 0) ∧
      ∀ (k' : Type) [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (q' : SplitPt D k'),
        q.v ≠ q'.v → (q.e + cA D q.e) * (q'.e + cA D q'.e) = 0 := by
  intro D k _ _ _ _ q
  obtain ⟨ε, hε, heq⟩ := q.above
  refine ⟨by rw [map_add (f := _), cA_cA, add_comm], fun P hP m n w hw => ⟨fun i j => ?_, ?_⟩,
    fun k' _ _ _ _ q' hv => ?_⟩
  · rw [← hw i j, heq]
    exact Ideal.mul_mem_right _ _ (placeIdem_mem_idAt hε hP)
  · ext i j
    rw [Matrix.map_apply, Matrix.zero_apply, ← hw i j, map_mul, heq, infPart_placeIdem hε, zero_mul]
  · obtain ⟨ε', hε', heq'⟩ := q'.above
    rw [heq, heq', ← map_mul, placeIdem_mul hε hε' hv, map_zero]

end GlobalTheory.PlaceIdemFacts

end
