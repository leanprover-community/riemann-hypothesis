module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PairingScaledDirectionsEqPeriodPairing
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem _root_.GlobalTheory.T.pairing_scaledDirections_eq_period_pairing : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (y : Matrix (Fin N') (Fin N) D.host.E) (a : Fin r → ℤ_[p]), δ / δ₀ ∈ Qbar → δ / δ₀ ≠ 0 → Nat.Coprime (Ideal.absNorm cc) p → (∀ x y : Matrix (Fin N') (Fin N) D.host.E, JMB.beta S.d S.Hm (e (δ • embV D B.tor x)) (e (δ • embV D B.tor y)) = D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) / (Ideal.absNorm cc : ℂ)) → JMB.pairD lam Ω S.d S.Hm (fun i => e (δ • embV D B.tor (b i))) ((δ₀ / δ) • e (δ • embV D B.tor y)) a = pairN D lam (Ω * (Ideal.absNorm cc : ℂ_[p]) * lamC lam (δ / δ₀)) b y a := by
  first | exact @GlobalTheory.MomFin.pairing_scaled | exact GlobalTheory.MomFin.pairing_scaled | (intros; apply GlobalTheory.MomFin.pairing_scaled <;> assumption)
