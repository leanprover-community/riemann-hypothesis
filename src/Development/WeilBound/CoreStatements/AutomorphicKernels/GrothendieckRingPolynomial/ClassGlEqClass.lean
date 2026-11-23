module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GrothendieckRingPolynomial
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ProdList
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.PhiZBijective
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos



namespace PositivityTheory.Groth

theorem GrothendieckClassGeneralLinear.class_gl_eq_class {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (h : HasFiniteLength π) :
    clsGL π h = cl0 π := by
  unfold cl0; rw [dite_eq_left h]

theorem groth_of_steps (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      Cls k ∧ MulCls k ∧ Assoc k ∧ Comm k ∧ One k ∧ ProdList k ∧ Tri k ∧ MultOne k ∧ JCls k ∧ JSeg k ∧ AltSum k)
    (h1 : TriAut) (h2 : UniTri) : GlobalTheory.Published.GrothendieckRingPolynomial := by
  intro k _ _ _ _ Z hZ
  obtain ⟨hCls, hMul, hAs, hCo, hOne, hPL, hTri, hMO, hJC, hJS, hAlt⟩ := H k
  haveI : Fact (Assoc k) := ⟨hAs⟩
  haveI : Fact (Comm k) := ⟨hCo⟩
  haveI : Fact (One k) := ⟨hOne⟩
  have hst : Steps k := ⟨hCls, hMul, hAs, hCo, hOne, hPL, hTri, hMO, hJC, hJS, hAlt⟩
  have hbij := phiZ_bijective hst h1 h2 Z hZ
  let e := RingEquiv.ofBijective (phiOf fun Δ : Segment k => (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL (k := k))) hbij
  refine ⟨toR.trans e.symm.toAddEquiv, ?_, ?_, ?_⟩
  · change e.symm (toR (GrothGL.unit k)) = 1
    rw [toR_unit, map_one]
  · intro r t V W _ _ _ _ π₁ π₂ h₁ h₂ s₁ s₂ h
    obtain ⟨_, hc⟩ := hMul r t V W π₁ π₂ h₁ h₂ s₁ s₂
    change e.symm (toR (clsGL (prod₂ π₁ π₂) h)) =
      e.symm (toR (clsGL π₁ h₁)) * e.symm (toR (clsGL π₂ h₂))
    rw [GrothendieckClassGeneralLinear.class_gl_eq_class, GrothendieckClassGeneralLinear.class_gl_eq_class, GrothendieckClassGeneralLinear.class_gl_eq_class, hc, toR_mulR, map_mul]
  · intro Δ
    change e.symm (toR (sg (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL (k := k)))) = MvPolynomial.X Δ
    rw [RingEquiv.symm_apply_eq]
    exact (phiOf_X (fun Δ : Segment k => (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL (k := k))) Δ).symm

end PositivityTheory.Groth

end
