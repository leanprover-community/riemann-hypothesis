module

public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GrothendieckRingPolynomial
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.PhiZBijective
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos



namespace CompanionTheory.Groth

theorem GrothendieckClassGeneralLinear.class_gl_eq_class {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (h : HasFiniteLength π) :
    clsGL π h = cl0 π := by
  unfold cl0; rw [dite_eq_left h]

theorem groth_of_steps (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      Cls k ∧ MulCls k ∧ Assoc k ∧ Comm k ∧ One k ∧ ProdList k ∧ Tri k ∧ MultOne k ∧ JCls k ∧ JSeg k ∧ AltSum k)
    (h1 : TriAut) (h2 : UniTri) : GlobalTheory.Published.GrothendieckRingPolynomial := by
  intro k _ _ _ _ Z hZ
  have hk : Steps k := H k
  have : Fact (Assoc k) := ⟨hk.2.2.1⟩
  have : Fact (Comm k) := ⟨hk.2.2.2.1⟩
  have : Fact (One k) := ⟨hk.2.2.2.2.1⟩
  let e : MvPolynomial (Segment k) ℤ ≃+* R k := RingEquiv.ofBijective _ (phiZ_bijective hk h1 h2 Z hZ)
  have he : ∀ p, e p = phiOf (k := k) (fun Δ => ⟨Δ.len * Δ.d, Z Δ⟩) p := fun _ => rfl
  refine ⟨toR.trans e.symm.toAddEquiv, ?_, ?_, ?_⟩
  · show e.symm (toR (GrothGL.unit k)) = 1
    rw [toR_unit, map_one]
  · intro r t V W _ _ _ _ π₁ π₂ h₁ h₂ hs₁ hs₂ h
    show e.symm (toR (clsGL (prod₂ π₁ π₂) h)) = e.symm (toR (clsGL π₁ h₁)) * e.symm (toR (clsGL π₂ h₂))
    rw [GrothendieckClassGeneralLinear.class_gl_eq_class, GrothendieckClassGeneralLinear.class_gl_eq_class, GrothendieckClassGeneralLinear.class_gl_eq_class, (hk.2.1 r t V W π₁ π₂ h₁ h₂ hs₁ hs₂).2, toR_mulR, map_mul]
  · intro Δ
    show e.symm (toR (Finsupp.single ⟨Δ.len * Δ.d, Z Δ⟩ 1)) = MvPolynomial.X Δ
    rw [RingEquiv.symm_apply_eq, he, phiOf_X]
    rfl

end CompanionTheory.Groth

end
