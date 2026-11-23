module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.WtDegConst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trHl_of :
    TrRed → TrHl := by
  intro hR l _ n i Z S p _ w hw hl x k
  have hne : ∀ k : ℕ, NeZero (l ^ k) := fun k => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hu : ∀ k : ℕ, IsUnit ((l ^ k : ℕ) : Γ(S, ⊤)) := fun k => by
    rw [Nat.cast_pow]
    exact hl.pow _
  have hT : ∃ T : Hl l (sch.obj Z) n i →ₗ[ℤ_[l]] Hl l (sch.obj S) n i,
      ∀ (x : Hl l (sch.obj Z) n i) (k : ℕ), (T x).1 k = tr p w (l ^ k) n i (x.1 k) := by
    refine ⟨{ toFun := fun x => ⟨fun k => tr p w (l ^ k) n i (x.1 k), fun k => ?_⟩
              map_add' := fun x y => Subtype.ext (funext fun k => map_add (tr p w (l ^ k) n i) (x.1 k) (y.1 k))
              map_smul' := fun r x => Subtype.ext (funext fun k => ?_) }, fun _ _ => rfl⟩
    · haveI := hne (k + 1)
      haveI := hne k
      exact (hR (l ^ (k + 1)) (l ^ k) (pow_dvd_pow l (Nat.le_succ k)) n i p w hw (hu (k + 1)) (x.1 (k + 1))).trans
        (congrArg _ (x.2 k))
    · let f : HtL l k (sch.obj Z) n i →+ HtL l k (sch.obj S) n i := tr p w (l ^ k) n i
      change f (r • x.1 k) = r • f (x.1 k)
      rw [HtL.smul_eq l k k le_rfl, HtL.smul_eq l k k le_rfl]
      exact map_nsmul f _ _
  exact pick_spec (P := fun T : Hl l (sch.obj Z) n i →ₗ[ℤ_[l]] Hl l (sch.obj S) n i =>
    ∀ (x : Hl l (sch.obj Z) n i) (k : ℕ), (T x).1 k = tr p w (l ^ k) n i (x.1 k)) hT x k
