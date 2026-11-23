module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldOneVariableTranscendentalFiniteAndEStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleAdelicMatrixFamilyPullbackExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionAdmissibleFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientLineDegreeLeOfTriangularFamilyStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem deg_le_rank_mul_of_linesLE : ∀ (r : ℕ) (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F → ∀ g : Place k F → Matrix (Fin r) (Fin r) F, admitted g → ∀ b : ℝ, LinesLE g b → (deg g : ℝ) ≤ r * b := by
  intro r
  induction r with
  | zero =>
    intro k F _ _ _ _ _ _ g _ b _
    have : deg g = 0 := by simp [deg, ord, Matrix.det_isEmpty]
    simp [this]
  | succ r ih =>
    intro k F _ _ _ _ _ hF g hg b hb

    set S : Set ℝ := {c | LinesLE g c} with hS
    have hbS : b ∈ S := hb

    have hbdd : BddBelow S := by
      refine ⟨(degLine (pullAd (id : Place k F → Place k F) g) (Pi.single 0 1) : ℝ), ?_⟩
      intro c hc
      have hres : IsRes (k := k) (F := F) (E := F) (id : Place k F → Place k F) := by
        intro p x; rfl
      have h1 := hc F id hres (Pi.single 0 1) (by
        intro h; have := congrFun h 0; simp at this)
      simpa [Module.finrank_self] using h1
    set a := sInf S with ha
    have hab : a ≤ b := csInf_le hbdd hbS
    have haS : LinesLE g a := by
      intro E _ _ _ _ _ ρ hρ w hw
      have hn : (0 : ℝ) < Module.finrank F E := by exact_mod_cast Module.finrank_pos
      have : (degLine (pullAd ρ g) w : ℝ) / Module.finrank F E ≤ a := by
        refine le_csInf ⟨b, hbS⟩ ?_
        intro c hc
        rw [div_le_iff₀ hn]
        exact hc E ρ hρ w hw
      rwa [div_le_iff₀ hn] at this
    have key : ∀ ε : ℝ, 0 < ε → (deg g : ℝ) ≤ (r + 1) * a + r * ε := by
      intro ε hε
      have hnot : ¬ LinesLE g (a - ε) := fun h => by
        have := csInf_le hbdd (show a - ε ∈ S from h); linarith
      simp only [LinesLE, not_forall, not_le] at hnot
      obtain ⟨E, _, _, _, _, _, ρ, hρ, x, hx, hlt⟩ := hnot
      have hn : (0 : ℝ) < Module.finrank F E := by exact_mod_cast Module.finrank_pos
      obtain ⟨hGadm, hGdeg, -, hGlines⟩ := GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hF ρ hρ (r + 1) g hg
      have hE : IsFF k E := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k F hF).2 E
      have hLG : LinesLE (pullAd ρ g) (a * Module.finrank F E) := hGlines a haS
      have hδle : (degLine (pullAd ρ g) x : ℝ) ≤ a * Module.finrank F E := haS E ρ hρ x hx
      obtain ⟨h, u, -, -, hzero, hadm', hadmq, hdeg, hsum, hlines⟩ :=
        GlobalTheory.T.iwasawa_decomposition_admissible_family k E hE r (pullAd ρ g) hGadm x hx
      have hLq := GlobalTheory.T.quotient_line_degree_le_of_triangular_family k E hE r (fun v => u v * pullAd ρ g v * h) hadm' hzero hadmq
        (a * Module.finrank F E) (hlines _ hLG)
      rw [hsum] at hLq
      have hq := ih k E hE _ hadmq _ hLq
      have hdegZ : (Module.finrank F E : ℤ) * deg g =
          degLine (pullAd ρ g) x + deg (fun v => (u v * pullAd ρ g v * h).submatrix Fin.succ Fin.succ) := by
        rw [← hGdeg, hdeg]
      have hdegR : (Module.finrank F E : ℝ) * (deg g : ℝ) =
          (degLine (pullAd ρ g) x : ℝ) + (deg (fun v => (u v * pullAd ρ g v * h).submatrix Fin.succ Fin.succ) : ℝ) := by
        exact_mod_cast hdegZ
      set n : ℝ := (Module.finrank F E : ℝ)
      set δ : ℝ := (degLine (pullAd ρ g) x : ℝ)
      have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have h2 : (r : ℝ) * (a * n - δ) ≤ r * (ε * n) := by
        apply mul_le_mul_of_nonneg_left _ hr; nlinarith
      have h3 : n * (deg g : ℝ) ≤ n * ((r + 1) * a + r * ε) := by nlinarith
      exact le_of_mul_le_mul_left h3 hn
    have hfin : (deg g : ℝ) ≤ (r + 1) * a := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have := key (ε / (r + 1)) (by positivity)
      have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have : (r : ℝ) * (ε / (r + 1)) ≤ ε := by
        rw [mul_div_assoc']; rw [div_le_iff₀ (by positivity)]; nlinarith
      linarith
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) r]

end GlobalTheory.Nef
