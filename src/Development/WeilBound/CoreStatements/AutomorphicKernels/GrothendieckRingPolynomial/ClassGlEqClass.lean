module

public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistInjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductJacquetShuffleCount
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductWordInShuffle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursOfSubquotient
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.SingleEqSmulSingle
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsClassificationOrderFreeEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsInjectiveOfSocleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsInterleaveSum
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GrothendieckRingPolynomial
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.GrothOfThree

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.PhiZBijective, Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ClassGlEqClass

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.PhiZBijective =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.PhiZBijective", "h": "module\n\npublic import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.GrothOfThree\npublic import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.SingleEqSmulSingle\nimport Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

namespace PositivityTheory.Groth.GrothendieckPhiBijection
open CompanionTheory.Groth (AltSum Assoc Comm JCls One R Steps TriAut UniTri cl0 phiL_main phiOf phiOf_X sg toR)
open CompanionTheory.Groth.GrothendieckPhiBijection (ell ell_prod ell_sg exists_enum msupp_seg prod_X_of_map toMultiset_eq_single_iff vars_lt)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]

theorem ell_phiOf (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hj : LSegJacquet k) (hJ : JCls k) (hAlt : AltSum k)
    (Lseg : Segment k → IrrGL (k := k)) (hL : ∀ Δ, IsLSeg Δ (Lseg Δ).rep)
    (hprod : ∀ (h N : ℕ) (Γ : Fin h → Segment k) (hd : ∑ a, (Lseg (Γ a)).1 = N),
      phiOf Lseg (∏ a, MvPolynomial.X (Γ a)) = toR (cl0 (prodIrr (fun a => Lseg (Γ a)) hd)))
    (Δ : Segment k) (p : MvPolynomial (Segment k) ℤ) :
    ell Δ (toR.symm (phiOf Lseg p)) = p.coeff (Finsupp.single Δ 1) * (-1) ^ (Δ.len - 1) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    obtain ⟨h, Γ, hΓ⟩ := exists_enum u
    have hm : MvPolynomial.monomial u a = MvPolynomial.C a * ∏ i : Fin h, MvPolynomial.X (Γ i) := by
      rw [prod_X_of_map u Γ hΓ, MvPolynomial.C_mul_monomial, mul_one]
    have hC : phiOf Lseg (MvPolynomial.C a) = (a : R k) := by simp [phiOf]
    rw [hm, map_mul, hC, hprod h _ Γ rfl, ← zsmul_eq_mul, map_zsmul, AddEquiv.symm_apply_apply, map_zsmul,
      ell_prod hA hj hJ hAlt Lseg hL Δ Γ rfl, hΓ, MvPolynomial.coeff_C_mul, prod_X_of_map u Γ hΓ,
      MvPolynomial.coeff_monomial]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd ((toMultiset_eq_single_iff u Δ).mp h1) h2
    · exact absurd ((toMultiset_eq_single_iff u Δ).mpr h2) h1
    · simp
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq, MvPolynomial.coeff_add, add_mul]

end PositivityTheory.Groth.GrothendieckPhiBijection

namespace PositivityTheory.Groth
open CompanionTheory.Groth (AltSum Assoc Comm JCls One R Steps TriAut UniTri cl0 phiL_main phiOf phiOf_X sg toR)
open CompanionTheory.Groth.GrothendieckPhiBijection (msupp_seg ell_sg vars_lt)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]

open GrothendieckPhiBijection in
theorem phiZ_bijective (hk : Steps k) (h1 : TriAut) (h2 : UniTri)
    (Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)) (hZ : IsSegmentClass k Z) :
    Function.Bijective (phiOf (k := k) fun Δ => ⟨Δ.len * Δ.d, Z Δ⟩) :=
  _root_.CompanionTheory.Groth.phiZ_bijective hk h1 h2 Z hZ

end PositivityTheory.Groth

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.PhiZBijective =====

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ClassGlEqClass =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ClassGlEqClass", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GrothendieckRingPolynomial\npublic import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.PhiZBijective\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.SingleEqSmulSingle\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

namespace PositivityTheory.Groth
open CompanionTheory.Groth (AltSum Assoc Cls Comm JCls JSeg MulCls MultOne One ProdList Steps Tri TriAut UniTri cl0 phiOf phiOf_X sg toR toR_mulR toR_unit)

theorem GrothendieckClassGeneralLinear.class_gl_eq_class {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (h : HasFiniteLength π) :
    clsGL π h = cl0 π := by
  unfold cl0; rw [dite_eq_left h]

theorem groth_of_steps (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      Cls k ∧ MulCls k ∧ Assoc k ∧ Comm k ∧ One k ∧ ProdList k ∧ Tri k ∧ MultOne k ∧ JCls k ∧ JSeg k ∧ AltSum k)
    (h1 : TriAut) (h2 : UniTri) : GlobalTheory.Published.GrothendieckRingPolynomial :=
  _root_.CompanionTheory.Groth.groth_of_steps H h1 h2

end PositivityTheory.Groth

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ClassGlEqClass =====
