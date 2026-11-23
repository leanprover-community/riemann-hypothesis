module

public import Development.EtaleCohomology.EtaleTrace.TorsionH0PointOfLocalTwist
public import Development.EtaleCohomology.TateTwists.StrictHenselianAcyclic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite

namespace LateralTheory.EtaleTrace

theorem tz_sec_eq_of_loc {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (y z : Sec F U)
    (h : Loc U fun V g => Sec.res g y = Sec.res g z) : y = z := by
  obtain ⟨S, hS, hP⟩ := h
  exact Sheaf.isSeparated F U S hS y z (fun _ g hg => hP _ g hg)

theorem tz_twGen_eq_of_pow {q : ℕ} {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) : twGen (q := q) 0 ξ = twGen 0 ζ := by
  unfold twGen
  congr 1
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, ?_⟩)
  simp
  rfl

def PrimLoc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)),
  Loc U fun V g => ∃ a : (ZMod q)ˣ, (ξ.map g.appTop.hom).1 = (ζ.map g.appTop.hom).1 ^ (a : ZMod q).val

theorem TwZero_of_primLoc (hTw : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hP : PrimLoc) : TwZero := by
  intro q _ U ζ ξ
  obtain ⟨-, -, T3⟩ := hTw q 0
  apply tz_sec_eq_of_loc
  obtain ⟨S, hS, hP'⟩ := hP q U ζ ξ
  refine ⟨S, hS, fun _ g hg => ?_⟩
  obtain ⟨a, ha⟩ := hP' _ g hg
  rw [T3, T3]
  exact (tz_twGen_eq_of_pow _ _ a ha).symm

end LateralTheory.EtaleTrace
