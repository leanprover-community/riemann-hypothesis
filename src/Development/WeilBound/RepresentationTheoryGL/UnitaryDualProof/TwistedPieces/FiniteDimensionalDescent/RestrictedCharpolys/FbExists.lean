module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PullPieces
import GroundTheory.AutomorphicForms.GLnLocal
import GroundTheory.AutomorphicForms.MeasuresModulus
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Restr.PphiA

open PositivityTheory.RgUd.TP.Desc.Restr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

structure FB (k : Type) [Field k] [TopologicalSpace k] (q d : ℕ) where
  β : Fin d → k
  cF : k →+ (Fin d → k)
  recon : ∀ a, ∑ j, cF a j ^ q * β j = a
  uniq : ∀ w : Fin d → k, cF (∑ j, w j ^ q * β j) = w
  cont : Continuous cF

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem fb_smul {q d : ℕ} (B : FB k q d) (l a : k) : B.cF (l ^ q * a) = fun j => l * B.cF a j := by
  conv_lhs => rw [← B.recon a, Finset.mul_sum]
  have : ∑ j, l ^ q * (B.cF a j ^ q * B.β j) = ∑ j, (l * B.cF a j) ^ q * B.β j :=
    Finset.sum_congr rfl fun j _ => by rw [mul_pow]; ring
  rw [this, B.uniq]

theorem fb_exists (hF : FinDim k) (p c : ℕ) [Fact p.Prime] [CharP k p] :
    ∃ d : ℕ, 0 < d ∧ Nonempty (FB k (p ^ c) d) := by
  letI := frMod (k := k) p c
  obtain ⟨hfd, hpos⟩ := hF p c
  set d := Module.finrank k (Fr k p c) with hd
  let b : Module.Basis (Fin d) k (Fr k p c) := Module.finBasis k (Fr k p c)
  let toK : Fr k p c → k := fun x => x
  let ofK : k → Fr k p c := fun x => x
  have hsm : ∀ (a : k) (x : Fr k p c), a • x = ofK (a ^ p ^ c * toK x) := by
    intro a x
    show iterateFrobenius k p c a * toK x = _
    rw [iterateFrobenius_def]
  let β : Fin d → k := fun j => toK (b j)
  let g : (Fin d → k) → k := fun w => ∑ j, w j ^ p ^ c * β j
  have gadd : ∀ v w, g (v + w) = g v + g w := by
    intro v w
    simp only [g, Pi.add_apply, add_pow_char_pow, add_mul, Finset.sum_add_distrib]
  let f : (Fin d → k) →+ k := AddMonoidHom.mk' g gadd
  have hfb : ∀ w, f w = toK (b.equivFun.symm w) := by
    intro w
    rw [Module.Basis.equivFun_symm_apply]
    show ∑ j, w j ^ p ^ c * β j = _
    exact Finset.sum_congr rfl fun j _ => (hsm (w j) (b j)).symm
  have hinj : Function.Injective f := by
    intro v w h
    rw [hfb, hfb] at h
    exact b.equivFun.symm.injective h
  have hsurj : Function.Surjective f := by
    intro a
    refine ⟨b.equivFun (ofK a), ?_⟩
    rw [hfb, LinearEquiv.symm_apply_apply]
  have hcont : Continuous f := by
    show Continuous g
    fun_prop
  have hopen : IsOpenMap f := AddMonoidHom.isOpenMap_of_sigmaCompact f hsurj hcont
  let E : (Fin d → k) ≃+ k := AddEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨d, hpos, ⟨{ β := β, cF := E.symm.toAddMonoidHom, recon := ?_, uniq := ?_, cont := ?_ }⟩⟩
  · intro a
    exact E.apply_symm_apply a
  · intro w
    exact E.symm_apply_apply w
  · show Continuous E.symm
    rw [continuous_def]
    intro U hU
    have himg : ⇑E.symm ⁻¹' U = f '' U := by
      ext y
      constructor
      · intro hy
        exact ⟨E.symm y, hy, E.apply_symm_apply y⟩
      · rintro ⟨x, hx, rfl⟩
        show E.symm (E x) ∈ U
        rw [E.symm_apply_apply]
        exact hx
    rw [himg]
    exact hopen U hU

end PositivityTheory.RgUd.TP.Desc.Restr.PphiA
