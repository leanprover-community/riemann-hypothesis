module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverIntersectionGradedIsoStatement
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.CapVan

theorem capO_eq_iInf_image {X : Scheme.{0}} {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → X.Opens) {m : ℕ}
    (i : Fin m → ι) : capO V i = ⨅ α ∈ Finset.image i Finset.univ, V α := by
  show (⨅ a, V (i a)) = _
  apply le_antisymm
  · refine le_iInf₂ fun α hα => ?_
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hα
    exact iInf_le _ a
  · exact le_iInf fun a => iInf₂_le (i a) (Finset.mem_image_of_mem i (Finset.mem_univ a))

theorem van {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q]
    (U : Cov q) (a n : ℕ) (i : Fin (n + 1) → U.ι) (r : ℕ) (hr : r ≠ a) :
    Subsingleton (HU (Fk q U a) (capT (Vk q U a) i) r) := by
  classical
  obtain ⟨e⟩ := GlobalTheory.T.cover_intersection_graded_iso q U a n i r
  have hV : IsAffineOpen (capO U.U i) := by
    rw [capO_eq_iInf_image]
    exact U.inter _ ⟨i 0, Finset.mem_image_of_mem i (Finset.mem_univ 0)⟩
  haveI := CrystallineSemistableComparison.Pb.gr_aff q (capO U.U i) hV (a + 1) a r (Nat.lt_succ_self a) hr
  exact e.injective.subsingleton

end GlobalTheory.CompanionTheory.CapVan
