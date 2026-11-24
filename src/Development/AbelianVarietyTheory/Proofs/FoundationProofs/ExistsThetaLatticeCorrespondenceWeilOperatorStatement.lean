module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsThetaLatticeCorrespondenceWeilOperator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_thetaLattice_correspondence_weilOperator : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → δ ≠ 0 → ∀ (N N' : ℕ) (e0 : VC D N N' → ℂ) (W : WeilO D cc δ N N' e0) (g h k : GA D N) (g' h' k' : GA D N') (L₁ L₂ M₁ M₂ : Lat D N) (L₁' L₂' M₁' M₂' : Lat D N'), Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((g * h : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((g' * h' : GA D N') : GL (Fin N') (AE D)) L₂' → Moves D (k : GL (Fin N) (AE D)) M₁ → Moves D (k' : GL (Fin N') (AE D)) M₁' → Moves D ((g * k : GA D N) : GL (Fin N) (AE D)) M₂ → Moves D ((g' * k' : GA D N') : GL (Fin N') (AE D)) M₂' → ∀ F ∈ TT D (tor0 D cc δ) N N', ∃ f : La D (tor0 D cc δ) M₁ M₁' → La D (tor0 D cc δ) M₂ M₂', (∀ x : La D (tor0 D cc δ) M₁ M₁', W.Om g g' (Wd D (tor0 D cc δ) (x : VC D N N') F) = Wd D (tor0 D cc δ) (f x : VC D N N') (W.Om g g' F)) ∧ (∀ x y : La D (tor0 D cc δ) M₁ M₁', (x : VC D N N') - (y : VC D N N') ∈ La D (tor0 D cc δ) L₁ L₁' ↔ (f x : VC D N N') - (f y : VC D N N') ∈ La D (tor0 D cc δ) L₂ L₂') ∧ ∀ y : La D (tor0 D cc δ) M₂ M₂', ∃ x : La D (tor0 D cc δ) M₁ M₁', (f x : VC D N N') - (y : VC D N N') ∈ La D (tor0 D cc δ) L₂ L₂' := by
  first | exact @GlobalTheory.WeilCorr.exists_corr | exact GlobalTheory.WeilCorr.exists_corr | (intros; apply GlobalTheory.WeilCorr.exists_corr <;> assumption)
