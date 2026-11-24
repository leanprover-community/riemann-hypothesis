module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Hi

private theorem UpperTheory.V.Hi.ctrlEq_row {G : Type} [Group G] {I : Iwa G} {O Ω : Type} [CommRing O] [IsLocalRing O] [Field Ω]
    [Algebra O Ω] (W : WtRep I O Ω) (g x : G) (hx : x ∈ I.Nf) (t : I.Tf) (v : Fin (W.d + 1) → Ω) :
    (((W.ξ (g * (x * t)))⁻¹).val *ᵥ v) 0 = (((W.χ t)⁻¹ : Ωˣ) : Ω) * (((W.ξ g)⁻¹).val *ᵥ v) 0 := by
  have h1 : ∀ w : Fin (W.d + 1) → Ω, ((W.ξ x⁻¹).val *ᵥ w) 0 = w 0 := by
    intro w
    have := W.row_N x⁻¹ (inv_mem hx)
    simp only [mulVec, dotProduct]
    simp_rw [this]
    simp
  have h2 : ∀ w : Fin (W.d + 1) → Ω, ((W.ξ ((t⁻¹ : I.Tf) : G)).val *ᵥ w) 0 = (W.χ t⁻¹ : Ω) * w 0 := by
    intro w
    have := W.torusAction t⁻¹
    simp only [mulVec, dotProduct]
    simp_rw [this]
    simp
  have h3 : (W.ξ (g * (x * t)))⁻¹ = W.ξ ((t⁻¹ : I.Tf) : G) * (W.ξ x⁻¹ * (W.ξ g)⁻¹) := by
    simp [mul_assoc]
  rw [h3, Units.val_mul, Units.val_mul, ← mulVec_mulVec, h2, ← mulVec_mulVec, h1, map_inv]

theorem UpperTheory.V.Hi.ctrlEq :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (O Ω : Type) [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) (m : ℕ) (τ : X.Ub →* GL (Fin m) Ω), (∀ u F, X.ctrl m W (X.raF (W.d + 1) τ u F) = X.ra τ u (X.ctrl m W F)) ∧ (∀ (a : X.I.P) F, X.ctrl m W (X.UF m W a F) = X.U Ω m a (X.ctrl m W F)) ∧ (∀ u (b : Gp) F, X.raF (W.d + 1) τ u (X.rpF Ω (W.d + 1) m b F) = X.rpF Ω (W.d + 1) m b (X.raF (W.d + 1) τ u F)) := by
  intro Γ Ga Gp _ _ _ X O Ω _ _ _ _ W m τ
  refine ⟨fun u F => ?_, fun a F => ?_, fun u b F => ?_⟩
  · ext g i
    change (((W.ξ g.2)⁻¹).val *ᵥ fun k => ((τ u).val *ᵥ fun j => F j (g * ((u : Ga), 1)) k) i) 0 =
      ((τ u).val *ᵥ fun j => (((W.ξ (g * ((u : Ga), 1)).2)⁻¹).val *ᵥ F j (g * ((u : Ga), 1))) 0) i
    simp only [mulVec, dotProduct, Prod.snd_mul, mul_one, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  · haveI : Finite (X.I.N ⧸ (X.I.Nconj a).subgroupOf X.I.N) :=
      Nat.finite_of_card_ne_zero (X.I.fin_N a a.2)
    haveI := Fintype.ofFinite (X.I.N ⧸ (X.I.Nconj a).subgroupOf X.I.N)

    simp only [Frame.UF, Frame.U, Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ext g i
    have := UpperTheory.V.Hi.ctrlEq_row W g.2 (q.out : X.I.N) (X.I.N_le q.out.2) ⟨a, X.I.P_le a a.2⟩
      (F i (g * (1, ((q.out : X.I.N) : Gp) * a)))
    exact this.symm
  · ext i g k
    change ((τ u).val *ᵥ fun j => F j (g * ((u : Ga), 1) * (1, b)) k) i =
      ((τ u).val *ᵥ fun j => F j (g * (1, b) * ((u : Ga), 1)) k) i
    simp [mul_assoc]
