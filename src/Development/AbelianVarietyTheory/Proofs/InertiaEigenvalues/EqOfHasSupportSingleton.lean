module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open ValuativeRel GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.DZeroDegOne

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_of_hasSupport_singleton {y z : IrrGL (k := k)} (h : HasSupport y.rep {z}) : y = z := by
  obtain ⟨r, u, hu, hi, hc, e, hsub⟩ := h
  obtain rfl : r = 1 := by simpa using congrArg Multiset.card hu
  obtain rfl : u = fun _ => z := funext fun i => by
    rw [Subsingleton.elim i 0]
    simpa using hu
  obtain ⟨d, c⟩ := y
  obtain rfl : z.1 = d := by simpa using Fintype.card_congr e
  have hd : ∑ _ : Fin 1, z.1 = z.1 := by simp
  let e' := stdBlocks (fun _ : Fin 1 => z.1) hd
  obtain ⟨φ⟩ : Nonempty ((multiProd e fun _ => z.rep).Equiv (multiProd e' fun _ => z.rep)) := by
    obtain ⟨w, hw⟩ := Placing.exists_moves (R := k) e' e
    have hw' : Placing.Moves e e' w⁻¹ := by
      intro g x y
      rw [← hw (w⁻¹ * g * w⁻¹⁻¹) x y]
      simp [mul_assoc]
    let ρ := twist (piTensor fun _ : Fin 1 => z.rep) (deltaHalf k fun _ : Fin 1 => Fin z.1)
    have conjugate {f f' : (Σ _ : Fin 1, Fin z.1) ≃ Fin z.1} {v : GL (Fin z.1) k}
        (hv : Placing.Moves f f' v) (p : parab k f) :
        ∃ q : parab k f', (q : GL (Fin z.1) k) = v * p * v⁻¹ ∧
          (ρ.comp (leviProj k f')) q = (ρ.comp (leviProj k f)) p := by
      have hq : v * (p : GL (Fin z.1) k) * v⁻¹ ∈ parab k f' := by
        rw [mem_parab]
        intro i j hij
        exact (hij.ne (Subsingleton.elim _ _)).elim
      refine ⟨⟨_, hq⟩, rfl, ?_⟩
      simp only [MonoidHom.comp_apply]
      congr 1
      refine funext fun a => Units.ext (Matrix.ext fun i j => ?_)
      simpa only [leviProj_apply] using hv (p : GL (Fin z.1) k) ⟨a, i⟩ ⟨a, j⟩
    exact Placing.smInd_equiv w (conjugate hw) (conjugate hw')
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one z hd
  let χ := φ.trans ψ.symm
  obtain ⟨θ⟩ := IsSubquotient.nonempty_equiv
    (hsub.trans (.of_injective χ.toIntertwiningMap χ.toLinearEquiv.injective)) hi z.2.rep.irr
  exact ((IrrGL.of_rep z).symm.trans ((IrrGL.of_eq_of.2 ⟨θ⟩).trans (IrrGL.of_rep ⟨_, c⟩))).symm

end GlobalTheory.DZeroDegOne
