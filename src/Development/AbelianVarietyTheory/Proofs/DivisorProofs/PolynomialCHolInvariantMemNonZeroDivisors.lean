module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LactMemDomOfIsom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConn
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspEmb

theorem isOpen_isPreconnected_dom {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U]
    [MulAction U C] (M : TwoLevels E r U C) (c : C) : IsOpen M.dom ∧ IsPreconnected M.dom := by
  have key : ∀ (X : Data E r) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E) (p0 : ℕ),
      X.Ψ = Ψ → X.Gm = Gm → X.p0 = p0 → IsOpen (GG Ψ Gm p0) ∧ IsPreconnected (GG Ψ Gm p0) := by
    intro X Ψ Gm p0 h1 h2 h3
    subst h1 h2 h3
    exact ⟨FourierCoefficientDomain.isOpen_dom X, (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X).isPreconnected⟩
  exact key (M.comp c).toData M.Ψ M.Gm M.p0 (M.comp_Ψ c) (M.comp_Gm c) (M.comp_basePoint c)

theorem C_mem_nonZeroDivisors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U]
    [MulAction U C] (M : TwoLevels E r U C) (D : HA M), (∀ c, ∃ x : M.dom, (D : C → M.dom → ℂ) c x ≠ 0) →
    Polynomial.C D ∈ nonZeroDivisors (Polynomial (HA M)) := by
  intro E _ _ _ r U C _ _ M D hD
  have key : ∀ p : Polynomial (HA M), p * Polynomial.C D = 0 → p = 0 := by
    intro p hp
    apply Polynomial.ext
    intro i
    have hq : p.coeff i * D = 0 := by
      have := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q i) hp
      simp only [Polynomial.coeff_mul_C, Polynomial.coeff_zero] at this
      exact this
    have hq' : ((p.coeff i : HA M) : C → M.dom → ℂ) * (D : C → M.dom → ℂ) = 0 := by
      have := congrArg (fun f : HA M => (f : C → M.dom → ℂ)) hq
      exact this
    rw [Polynomial.coeff_zero]
    apply Subtype.ext
    funext c x
    obtain ⟨x0, hx0⟩ := hD c
    obtain ⟨GD, hGD, hGD'⟩ := D.2.1 c
    obtain ⟨Gq, hGq, hGq'⟩ := (p.coeff i).2.1 c
    obtain ⟨hO, hC⟩ := isOpen_isPreconnected_dom M c
    have h0 : GD x0.1 ≠ 0 := by rw [← hGD']; exact hx0
    have hz := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero hO hC hGD hGq
      (fun y hy => by
        have := congrFun (congrFun hq' c) ⟨y, hy⟩
        simp only [Pi.mul_apply, Pi.zero_apply] at this
        rw [← hGD' ⟨y, hy⟩, ← hGq' ⟨y, hy⟩, mul_comm]
        exact this) x0.2 h0 x.1 x.2
    show ((p.coeff i : HA M) : C → M.dom → ℂ) c x = ((0 : HA M) : C → M.dom → ℂ) c x
    rw [hGq' x, hz]
    rfl
  refine mem_nonZeroDivisors_iff.2 ⟨fun x hx => key x ?_, key⟩
  rwa [mul_comm] at hx

end GlobalTheory.CuspEmb
