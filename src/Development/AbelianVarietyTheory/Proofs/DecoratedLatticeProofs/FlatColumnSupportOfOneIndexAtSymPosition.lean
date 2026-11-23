module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatColumnMapEqRootExchangeOperatorTranslateStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.LocFlat.SuppColProof

theorem det_colE {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (c p : ℕ) (β : n → k) :
    Matrix.GeneralLinearGroup.det (colE c p β) = 1 := by
  ext
  simp [colE, upU]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem om_colE {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (μ : kˣ →* ℂˣ) (g h : GL (n ⊕ Fin c) k) (hg : Matrix.GeneralLinearGroup.det g = 1)
    (Φ : Matrix (n ⊕ Fin c) n' k → ℂ) :
    (fun z => om μ 1 h Φ (g.val * z)) = om μ 1 (g⁻¹ * h) Φ := by
  rw [show om μ 1 (g⁻¹ * h) Φ = om μ (1 * 1) (g⁻¹ * h) Φ by rw [mul_one], om_mul]
  funext z
  have hi : Matrix.GeneralLinearGroup.det g⁻¹ = 1 := by rw [map_inv, hg, inv_one]
  simp [om, hi, nabs_one]

end GlobalTheory.LocFlat.SuppColProof


open GlobalTheory.LocFlat.SuppColProof in
theorem GlobalTheory.LocFlat.suppCol_of_oneIndexAt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.OneIndexAt t ν → GlobalTheory.LocFlat.SuppCol S t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hOne j c H r hr h hne
  have hΦ : (S.T t).Phi j (c + 1) (by omega) ∈ SB _ :=
    (Chain.ofType_regular _ _ _ _ _).1 j (c + 1) (by omega)
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hne
  rw [GlobalTheory.T.flatColumnMap_eq_rootExchangeOperator_translate k S.ψ ν S.cond.continuous hν.1 _ _ (c + 1) (r + 1) (by omega) (by omega) _
    (om_mem_SB _ 1 h hΦ) x] at hx
  have hf := om_colE (n' := XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) (S.μ (j + 1))
    (colE (c + 1) (r + 1) fun a => x a (Sum.inr ())) h (det_colE _ _ _) ((S.T t).Phi j (c + 1) (by omega))
  have hx' : opE S.ψ ν (r + 1) (om (S.μ (j + 1)) 1 ((colE (c + 1) (r + 1) fun a => x a (Sum.inr ()))⁻¹ * h)
      ((S.T t).Phi j (c + 1) (by omega))) x.toCols₁ ≠ 0 := by
    rw [← hf]; exact hx
  obtain ⟨q, hq, u, hu, e⟩ := hOne j (c + 1) (by omega) (r + 1) (by omega) (by omega) _ (fun hz => hx' (by rw [hz]; rfl))
  refine ⟨fun a => x a (Sum.inr ()), q, hq, u, hu, ?_⟩
  rw [mul_assoc, ← e, mul_inv_cancel_left]
