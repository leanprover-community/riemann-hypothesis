module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ArithmeticPointClassicality
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepTraceNondegenerate
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.RepChi
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem trace_eq_of_charpoly {K : Type} [Field K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K}
    (h : A.charpoly = B.charpoly) : A.trace = B.trace := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [Matrix.trace]
  · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, h]

private theorem kill_of_charpoly {Γ K : Type} [Group Γ] [Field K] [CharZero K] {n : ℕ}
    (ρ : Γ →* GL (Fin n) K) (hss : IsSSRep ρ) (g : Γ)
    (h : ∀ k, ((ρ (g * k) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly =
      ((ρ k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly) : ρ g = 1 := by
  have hx := GlobalTheory.isSSRep_trace_nondegenerate Γ K n ρ hss ((ρ g : Matrix (Fin n) (Fin n) K) - 1)
    (Submodule.sub_mem _ (Submodule.subset_span ⟨g, rfl⟩) (Submodule.subset_span ⟨1, by simp⟩))
    (fun k => by
      rw [sub_mul, one_mul, Matrix.trace_sub, ← Units.val_mul, ← map_mul,
        trace_eq_of_charpoly (h k), sub_self])
  exact Units.ext (by simpa using sub_eq_zero.mp hx)

theorem UpperTheory.V.Ws.Pu.repKill :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} (B : W.UniversalOrdinaryDeterminantRing r) (x : B.Pt) (ρ : G L Ω →* GL (Fin n) (PadicAlgCl l)), x.IsRep ρ → IsSSRep ρ → ∀ g, V.pr g = 1 → ρ g = 1 := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B x ρ hx hss g hg
  refine kill_of_charpoly ρ hss g fun k => ?_
  have h1 := UpperTheory.V.Ws.Pu.repChi V B x ρ hx (g * k)
  have h2 := UpperTheory.V.Ws.Pu.repChi V B x ρ hx k
  rw [map_mul V.pr, hg, one_mul] at h1
  exact h1.trans h2.symm
