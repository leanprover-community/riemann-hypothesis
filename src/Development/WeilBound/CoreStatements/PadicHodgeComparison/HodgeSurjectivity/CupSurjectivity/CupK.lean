module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.ProperGenMap
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.SumCoordBasisDual
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem cupK (P : HTPre l K) {M : Model l K} (hM : M.Sm) {D : ℕ} (S : Sq M D) {i j : ℕ} (X : M.T i) (Y : M.T j)
    (Z : S.P.T (i + j)) (hZ : S.P.CupT (Model.pullT S.p₁ S.h₁ i X) (Model.pullT S.p₂ S.h₂ j Y) Z)
    {m m' : ℕ → ℕ} (b : ∀ a, Module.Basis (Fin (m a)) K (Hdg M.q a i)) (b' : ∀ a, Module.Basis (Fin (m' a)) K (Hdg M.q a j))
    (A : ℕ) (Θ : Module.Dual K (Hdg S.P.q A (i + j))) :
    P.h S.P A (i + j) (S.P.toV _ Z) Θ = ∑ p : (Finset.HasAntidiagonal.antidiagonal A : Finset (ℕ × ℕ)), ∑ s, ∑ s',
      P.h M p.1.1 i (M.toV _ X) ((b p.1.1).coord s) * P.h M p.1.2 j (M.toV _ Y) ((b' p.1.2).coord s') *
        kC K (Θ (cupH S.P.q (Finset.HasAntidiagonal.mem_antidiagonal.1 p.2) rfl (S.pl₁ p.1.1 i (b p.1.1 s))
          (S.pl₂ p.1.2 j (b' p.1.2 s')))) := by
  classical
  have hfin : ∀ a n, FiniteDimensional K (Hdg S.P.q a n) := fun a n => (P.fin S.P S.smP a n).1
  rw [P.cup S.P S.smP (Model.pullT S.p₁ S.h₁ i X) (Model.pullT S.p₂ S.h₂ j Y) Z hZ
    (fun a => Module.finBasis K (Hdg S.P.q a i)) (fun a => Module.finBasis K (Hdg S.P.q a j)) A Θ]
  refine Finset.sum_congr rfl fun p _ => ?_
  obtain ⟨bl, hbl'⟩ : ∃ bl : Hdg S.P.q p.1.1 i →ₗ[K] Hdg S.P.q p.1.2 j →ₗ[K] Hdg S.P.q A (i + j),
      ∀ x y, bl x y = cupH S.P.q (Finset.HasAntidiagonal.mem_antidiagonal.1 p.2) rfl x y :=
    CrystallineSemistableComparison.P.cup_bilin (grOk (smFun _ S.P.q) (Finset.HasAntidiagonal.mem_antidiagonal.1 p.2)).pair (rfl : i + j = i + j)
  have n₁ : ∀ F, P.h S.P p.1.1 i (S.P.toV i (Model.pullT S.p₁ S.h₁ i X)) F = P.h M p.1.1 i (M.toV i X) (F ∘ₗ S.pl₁ p.1.1 i) := by
    intro F
    rw [← pullV_toV S.p₁ S.h₁ i X, P.nat S.P M S.p₁ S.h₁ S.smP hM]
  have n₂ : ∀ F, P.h S.P p.1.2 j (S.P.toV j (Model.pullT S.p₂ S.h₂ j Y)) F = P.h M p.1.2 j (M.toV j Y) (F ∘ₗ S.pl₂ p.1.2 j) := by
    intro F
    rw [← pullV_toV S.p₂ S.h₂ j Y, P.nat S.P M S.p₂ S.h₂ S.smP hM]
  have key := gen2 (kC K) (P.h S.P p.1.1 i (S.P.toV i (Model.pullT S.p₁ S.h₁ i X))) (P.h M p.1.1 i (M.toV i X))
    (P.h S.P p.1.2 j (S.P.toV j (Model.pullT S.p₂ S.h₂ j Y))) (P.h M p.1.2 j (M.toV j Y))
    (fun k φ => P.lin' _ _ _ k _ φ) (fun k φ => P.lin' _ _ _ k _ φ) (fun k φ => P.lin' _ _ _ k _ φ) (fun k φ => P.lin' _ _ _ k _ φ)
    (S.pl₁ p.1.1 i) (S.pl₂ p.1.2 j) n₁ n₂ (bl.compr₂ Θ)
    (Module.finBasis K (Hdg S.P.q p.1.1 i)) (Module.finBasis K (Hdg S.P.q p.1.2 j)) (b p.1.1) (b' p.1.2)
  simp only [LinearMap.compr₂_apply, hbl'] at key
  exact key

end CrystallineSemistableComparison.Onto

end
