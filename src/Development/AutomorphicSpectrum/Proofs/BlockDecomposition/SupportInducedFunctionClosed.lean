module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem isClosed_support_smooth_ind {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {W₁ : Type}
    [AddCommGroup W₁] [Module ℂ W₁] {Q : Subgroup G} (σ : Representation ℂ Q W₁) (f : smoothPart (ind Q σ)) :
    IsClosed {g : G | f.1.1 g ≠ 0} := by
  have hT : IsOpen {g : G | ind Q σ g f.1 = f.1} := f.2
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro g hg
  have hg0 : f.1.1 g = 0 := by simpa using hg
  have hc : Continuous fun h : G => g⁻¹ * h := continuous_const.mul continuous_id
  have hm : {h : G | g⁻¹ * h ∈ {κ : G | ind Q σ κ f.1 = f.1}} ∈ 𝓝 g :=
    (hT.preimage hc).mem_nhds (by
      show ind Q σ (g⁻¹ * g) f.1 = f.1
      simp)
  filter_upwards [hm] with h hh
  have e : (ind Q σ (g⁻¹ * h) f.1).1 g = f.1.1 g := congrArg (fun F : indSpace Q σ => F.1 g) hh
  have e' : f.1.1 (g * (g⁻¹ * h)) = f.1.1 g := e
  rw [mul_inv_cancel_left] at e'
  simpa [e', hg0] using hg0

end GlobalTheory.CompanionTheory.BZRes
