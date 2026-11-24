module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
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
import Mathlib.RingTheory.DualNumber
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
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZM

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}

structure SFam (h k : ℕ) {o : Type} [CommRing o] (ζ : o) where

  X : Scheme.{0}

  s : X ⟶ Sp o

  smooth : SmoothOfRelativeDimension (h * (h + 1) / 2) s

  qproj : IsQProjOver s

  univ : SiegPre h k ζ s

  princ : univ.Principal

  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (c : SiegPre h k ζ s'), IsReduced S → Dense {x : S | (s' x).asIdeal = ⊥} →
    c.Principal → ∃ f : S ⟶ X, f ≫ s = s' ∧ SiegPB c univ f

  inj : ∀ (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ X) (s' : Sp R ⟶ Sp o) (c : SiegPre h k ζ s'),
    x ≫ s = y ≫ s → SiegPB c univ x → SiegPB c univ y → x = y

def SRep {h p M : ℕ} (Ag : SiegelFamily h p M) : Prop :=
  IsSeparated Ag.s ∧ ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (ZP p M)) (c : SiegPre h M (zetaZP p M) s'), IsReduced S →
    Dense {x : S | (s' x).asIdeal = ⊥} → c.Principal → ∃ f : S ⟶ Ag.X, f ≫ Ag.s = s' ∧ SiegPB c Ag.univ f

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isSeparated_of_isQProjOver {X : Scheme.{0}} {f : X ⟶ Sp o} (h : IsQProjOver f) : IsSeparated f := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  have : IsImmersion i := hi
  unfold PSpace.str
  infer_instance

theorem SFam.isSeparated {h : ℕ} {ζ : o} (F : SFam h k ζ) : IsSeparated F.s := isSeparated_of_isQProjOver F.qproj

theorem SFam.eq_constPt {h : ℕ} {ζ : o} (F : SFam h k ζ) (K : Type) [Field K] (x : Sp (DualNumber K) ⟶ F.X)
    (c : SiegPre h k ζ (x ≫ F.s)) (hs : x ≫ F.s = constPt x ≫ F.s) (h₁ : SiegPB c F.univ x)
    (h₂ : SiegPB c F.univ (constPt x)) : x = constPt x := F.inj (DualNumber K) x (constPt x) (x ≫ F.s) c hs h₁ h₂

theorem SFam.sRep {h p M : ℕ} (F : SFam h M (zetaZP p M))
    (sm : SmoothOfRelativeDimension (h * (h + 1) / 2) F.s) (qc : QuasiCompact F.s) (pr : F.univ.Principal) (pts unr) :
    SRep (⟨F.X, F.s, sm, qc, F.univ, pr, pts, unr⟩ : SiegelFamily h p M) := ⟨F.isSeparated, fun S s' c hS hd hc => F.rep S s' c hS hd hc⟩

end GlobalTheory.ZM
end
