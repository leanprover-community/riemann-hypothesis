module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetNeZeroOfHasSignature
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolIndep
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VolRatioUp

theorem volRatio_up : ∀ D : D7, VolTie D → Conclusion2 D → ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK →
    (∀ τ, W.sig τ = (P, Q)) → 2 ≤ P + Q → ∀ U : HSpace D.host.E, U.SigOK → (∀ τ, U.sig τ = (P + 1, Q)) →
    D.vol U / D.vol W = Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E (P + Q + 1) := by
  intro D hT h2 W P Q hW hWs hPQ U hU hUs
  have hUr : U.rank = P + Q + 1 := by
    have := Formalism.BasicNotions.sig_sum U hU D.host.φ₀
    rw [hUs] at this
    simp only at this
    omega
  have hWr : W.rank = P + Q := by
    have := Formalism.BasicNotions.sig_sum W hW D.host.φ₀
    rw [hWs] at this
    exact this.symm
  obtain ⟨x, -, W', ι, -, -, hW'ok, hW's, hratio⟩ :=
    h2 U (P + 1) Q hU hUs (by omega) true (by simp)
  have hW's' : ∀ τ, W'.sig τ = (P, Q) := fun τ => by
    have := hW's τ
    simpa using this
  have hW'r : W'.rank = P + Q := by
    have := Formalism.BasicNotions.sig_sum W' hW'ok D.host.φ₀
    rw [hW's'] at this
    exact this.symm
  obtain ⟨φ, hφ⟩ := GlobalTheory.LandherrSignature.exists_isometry_host D W W' hW hW'ok (by rw [hWr, hW'r])
    (fun τ => by rw [hWs, hW's'])
  have hvol : D.vol W = D.vol W' :=
    (GlobalTheory.VolIndepClosed.volIndep D).2.2 hT W W' P Q ⟨hW, hWs⟩ ⟨hW'ok, hW's'⟩ φ hφ
  rw [hvol, hratio, hUr]

end GlobalTheory.VolRatioUp
