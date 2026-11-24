module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericFiniteByInduction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOnFundamentalDomain
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CuspSubspace

theorem mem_of_mem_span_cuspForms :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
      (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W)
      (J : Set (Module.End ℂ (Sm E a))),
      ∀ φ ∈ Submodule.span ℂ {φ : Sm E a | φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1},
        φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1 := by
  intro E _ _ _ a L W _ _ ρ J φ hφ
  induction hφ using Submodule.span_induction with
  | mem x h => exact h
  | zero =>
    refine ⟨(GlobalTheory.CompanionTheory.AffglAssembly.genSub L ρ J).zero_mem, ?_⟩
    intro r hr hr' inst1 inst2 μ 𝓕 hμ hF g
    change ∫ _ in 𝓕, (0 : ℂ) ∂μ = 0
    simp
  | add x y _ _ hx hy =>
    refine ⟨(GlobalTheory.CompanionTheory.AffglAssembly.genSub L ρ J).add_mem hx.1 hy.1, ?_⟩
    intro r hr hr' inst1 inst2 μ 𝓕 hμ hF g
    have ix := (GlobalTheory.CompanionTheory.ConstTerm.integrableOn_fundamentalDomain E a r x hx.1.1.left hx.1.1.level μ 𝓕 hμ hF).2 g
    have iy := (GlobalTheory.CompanionTheory.ConstTerm.integrableOn_fundamentalDomain E a r y hy.1.1.left hy.1.1.level μ 𝓕 hμ hF).2 g
    have e : ∫ u in 𝓕, (x + y).1 (unip u * g) ∂μ =
        (∫ u in 𝓕, x.1 (unip u * g) ∂μ) + ∫ u in 𝓕, y.1 (unip u * g) ∂μ := integral_add ix iy
    rw [e, hx.2 r hr hr' μ 𝓕 hμ hF g, hy.2 r hr hr' μ 𝓕 hμ hF g, add_zero]
  | smul c x _ hx =>
    refine ⟨(GlobalTheory.CompanionTheory.AffglAssembly.genSub L ρ J).smul_mem c hx.1, ?_⟩
    intro r hr hr' inst1 inst2 μ 𝓕 hμ hF g
    have e : ∫ u in 𝓕, (c • x).1 (unip u * g) ∂μ = c • ∫ u in 𝓕, x.1 (unip u * g) ∂μ :=
      integral_smul c _
    rw [e, hx.2 r hr hr' μ 𝓕 hμ hF g, smul_zero]

end GlobalTheory.CompanionTheory.CuspSubspace

end
