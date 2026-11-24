module

public import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.EtaleTrace

def PtCover : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] (T : Sieve (S k)), T ∈ Scheme.etaleTopology (S k) → T.arrows (𝟙 _)

def TwZero : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)),
  GlobalTheory.EtC.twGen (U := U) 0 ζ = GlobalTheory.EtC.twGen (U := U) 0 ξ

def EvNat : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X U : Scheme.{0}) (α : CochainComplex.HomComplex.Cochain ((chains R).obj (sch.obj X)) (res R F) 0)
  (x : U ⟶ X), ev (R := R) α 0 0 (by simp) U x = Sec.res x (ev (R := R) α 0 0 (by simp) X (𝟙 X))

def CocEq : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})
  (α β : CochainComplex.HomComplex.Cocycle ((chains R).obj (sch.obj X)) (res R F) 0),
  (∀ (U : Scheme.{0}) (x : Sx (sch.obj X) 0 U),
    ev (R := R) α.1 0 0 (by simp) U x = ev (R := R) β.1 0 0 (by simp) U x) → α = β

theorem exists_prim (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k] (hl : (l : k) ≠ 0) (j : ℕ) :
    Nonempty (Prim (l ^ j) Γ(S k, ⊤)) := by
  have hq : 0 < l ^ j := pow_pos (Fact.out : l.Prime).pos j
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (l ^ j) k)
    (Polynomial.degree_cyclotomic_pos (l ^ j) k hq).ne'
  have hu : IsUnit ((l ^ j : ℕ) : k) := by
    rw [Nat.cast_pow]; exact (isUnit_iff_ne_zero.2 hl).pow j
  have hr' : Polynomial.aeval r (Polynomial.cyclotomic (l ^ j) ℤ) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hr
  exact ⟨Prim.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom ⟨r, hu, hr'⟩⟩

end LateralTheory.EtaleTrace
