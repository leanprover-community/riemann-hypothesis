module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmThetaBaseVectorTranslatesIntegral
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

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem _root_.GlobalTheory.T.cmTheta_baseVector_translates_integral : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ (t : D.what₂.Tau → ℂ) (n : ℕ), Nat.Coprime n q → (n : ℂ) • t ∈ B.lamM → LatInt ι (Ω / ι δ₀) B.lamM (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) t B.thMM) := by
  first | exact @GlobalTheory.MomN.translates_latInt | exact GlobalTheory.MomN.translates_latInt | (intros; apply GlobalTheory.MomN.translates_latInt <;> assumption)
