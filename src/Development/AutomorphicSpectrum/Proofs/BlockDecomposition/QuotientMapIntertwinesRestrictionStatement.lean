module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapIntertwinesRestriction
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.quotient_map_intertwines_restriction : ∀ {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H : Subgroup G) (H' : Subgroup G') (ι : G' →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H' W')
    (q : W →ₗ[ℂ] W'), Continuous ι → (∀ x, x ∈ H' ↔ ι x ∈ H) →
    (∀ (h : H') (hh : ι h ∈ H) (w : W), q (σ ⟨ι h, hh⟩ w) = σ' h (q w)) →
    IsClosed {g : G | ∃ h ∈ H, ∃ x : G', g = h * ι x} →
    (∀ K' ∈ 𝓝 (1 : G'), ∃ K ∈ 𝓝 (1 : G), ∀ x : G', ∀ h ∈ H, ∀ κ ∈ K, ι x = h * κ →
      ∃ h' ∈ H', ∃ κ' ∈ K', x = h' * κ') →
    (∃ K' ∈ 𝓝 (1 : G'), IsCompact K') →
    ∀ f : cIndSpace H σ, ∃ F : cIndSpace H' σ', ∀ x, F.1.1.1 x = q (f.1.1.1 (ι x)) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_restrict | exact GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_restrict | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_restrict <;> assumption)
