module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperplaneSectionVanishingShiftStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZeroDimSupportEulerCharStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore

theorem choose_mul_interNum_le_hdim : ∀ (k : Type) [Field k] [Infinite k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k (X := Y)) → ∀ (L : LB Y) (hL : L.IsLB) (N : ℕ) (b : Fin N → L.Sec), (∀ y : Y, ∃ i, y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (b i)) → ∀ (d : ℕ) (F : Y.Modules) [IsFiniteQC F], suppDim F ≤ d → ∀ (j₀ : ℤ), VanishFrom L F j₀ → ∀ m : ℕ, (m.choose d : ℤ) * GlobalTheory.interNum k F (fun _ : Fin d => L) ≤ GlobalTheory.hdim k (GlobalTheory.twistZ F L (j₀ + m)) 0 := by
  intro k _ _ Y _ hY L hL N b hb d
  have hNo : AlgebraicGeometry.IsNoetherian Y := isNoetherian_of_isProjOver hY
  have hb' : ⨆ i, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (b i) = ⊤ :=
    top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 (hb y)
  have hf := algebraMap_eq_strHom k Y
  induction d with
  | zero =>
    intro F _ hF j₀ _ m
    rw [interNum_of_isEmpty, GlobalTheory.T.zero_dim_support_euler_char k Y hY L hL F (by simpa using hF)]
    simp
  | succ d ih =>
    intro F _ hF j₀ hV m
    obtain ⟨c, hc⟩ := exists_sum_mono_cutHom (k := k) F hL b hb'
    set t : L.Sec := ∑ i, algebraMap k Γ(Y, ⊤) (c i) • b i
    obtain ⟨hV', hr⟩ := GlobalTheory.T.hyperplane_section_vanishing_shift k Y hY L hL F t j₀ hV
    have hI : GlobalTheory.interNum k F (fun _ : Fin (d + 1) => L) =
        GlobalTheory.interNum k (GlobalTheory.cut F hL t) (fun _ : Fin d => L) := by
      rw [← interNum_cons_eq_interNum_cut hL t (P := fun _ : Fin d => L) (fun _ => hL)
        (finiteCohTwists_of_isProjOver hf F hY)]
      congr 1
      funext i
      refine Fin.cases rfl (fun _ => rfl) i
    have ih' := ih (GlobalTheory.cut F hL t) (suppDim_cut_le F hL t hF) (j₀ + 1) hV'
    rw [hI]
    induction m with
    | zero => simp
    | succ m ihm =>
      have h1 := hr (j₀ + 1 + m) (by omega)
      have h2 := ih' m
      have e1 : j₀ + ((m + 1 : ℕ) : ℤ) = j₀ + 1 + m := by push_cast; ring
      have e2 : j₀ + 1 + (m : ℤ) - 1 = j₀ + m := by ring
      rw [e2] at h1
      rw [e1, h1, Nat.choose_succ_succ']
      push_cast
      linarith

end GlobalTheory.HSCore
