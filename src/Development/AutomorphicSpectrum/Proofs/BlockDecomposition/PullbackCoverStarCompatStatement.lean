module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackCoverStarCompat
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
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

theorem _root_.GlobalTheory.T.pullback_cover_star_compat : ∀ {K : Type} [CommRing K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K))
    (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι)
    (hτ : ∀ n (i : Fin (n + 1) → U.ι), capO U.U i ≤ u ⁻¹ᵁ capO W.U (τ ∘ i)) (a : ℕ),
    ∃ hG : ∀ T, KC q U a T → KC p W a ((pullM u hu a).G.obj T),
      ∀ α T, Vk q U a α T → Vk p W a (τ α) ((morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).G.obj T) := by
  first | exact @GlobalTheory.CompanionTheory.OmGlobPush.push_kc | exact GlobalTheory.CompanionTheory.OmGlobPush.push_kc | (intros; apply GlobalTheory.CompanionTheory.OmGlobPush.push_kc <;> assumption)
