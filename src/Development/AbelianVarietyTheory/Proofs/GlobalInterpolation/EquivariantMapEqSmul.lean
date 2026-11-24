module

public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BranchesAlongOfIrreducible
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InterlacingEquivariance
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX

@[expose] public section

open MvPolynomial NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance GlobalTheory.BranchFormula

namespace GlobalTheory.Branching

theorem equivariant_map_eq_smul : ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Formalism.MainNotions.PrimeDegreeVariant.Interlace h lam sg → ∀ (φ φ' : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ), (∀ ψ, ψ = φ ∨ ψ = φ' → (∀ f ∈ nablaSq ℂ N lam, ψ f ∈ nablaSq ℂ n sg) ∧ ∀ (g : GL (Fin n) ℂ), ∀ f ∈ nablaSq ℂ N lam, ψ (sqAct ℂ N lam (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N h g) f) = sqAct ℂ n sg g (ψ f)) → (∃ f ∈ nablaSq ℂ N lam, φ' f ≠ 0) → ∃ c : ℂ, ∀ f ∈ nablaSq ℂ N lam, φ f = c • φ' f := by
  intro n N h lam sg hI φ φ' H hne
  let mk : ∀ ψ, (ψ = φ ∨ ψ = φ') → (resRep (MonoidHom.id (GL (Fin n) ℂ)) h lam).IntertwiningMap
      (smallRep (MonoidHom.id (GL (Fin n) ℂ)) sg) := fun ψ hψ =>
    ⟨ψ.restrict (H ψ hψ).1, fun g => LinearMap.ext fun f => Subtype.ext ((H ψ hψ).2 g f.1 f.2)⟩
  have h1 := (comult_id n N h lam sg).1 hI
  have hz : mk φ' (Or.inr rfl) ≠ 0 := by
    obtain ⟨f, hf, hf0⟩ := hne
    intro e
    apply hf0
    have := congrArg (fun F => ((F.toLinearMap ⟨f, hf⟩ : nablaSq ℂ n sg) : MvPolynomial (Fin n × Fin n) ℂ)) e
    exact this
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hz).1 h1 (mk φ (Or.inl rfl))
  refine ⟨c, fun f hf => ?_⟩
  have := congrArg (fun F => ((F.toLinearMap ⟨f, hf⟩ : nablaSq ℂ n sg) : MvPolynomial (Fin n × Fin n) ℂ)) hc
  exact this.symm

end GlobalTheory.Branching
