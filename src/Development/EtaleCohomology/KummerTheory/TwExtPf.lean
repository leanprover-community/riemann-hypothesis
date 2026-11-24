module

public import Development.EtaleCohomology.KummerTheory.BockCut
public import Development.EtaleCohomology.TateTwists.EtaleSheafMonoEpiSectionCriteria
public import Development.EtaleCohomology.TateTwists.EtaleTateTwistSectionsLocallyGenerated
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
import Mathlib.Tactic.Linter.Style
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
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.TwExtPf

theorem sep {M : Shv ℤ} {U : Scheme.{0}} (x y : Sec M U)
    (h : Loc U fun V g => Sec.res g x = Sec.res g y) : x = y := by
  obtain ⟨S, hS, hP⟩ := h
  exact Sheaf.isSeparated M U S hS x y (fun V g hg => hP _ g hg)

theorem TwExt_of (hT : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated) (hM : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria) :
    LateralTheory.KummerTheory.BockCut.TwExt := by
  intro Q _ i M φ ψ h
  refine (hM ℤ φ).2.2.2 ψ fun U a => ?_
  obtain ⟨S, hS, hP⟩ := (hT Q i).1 U a
  refine sep _ _ ⟨S, hS, fun V g hg => ?_⟩
  have nφ : Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) :=
    congrArg (fun f => (ModuleCat.Hom.hom f) a) (φ.hom.naturality g.op).symm
  have nψ : Sec.res g (Sec.map ψ a) = Sec.map ψ (Sec.res g a) :=
    congrArg (fun f => (ModuleCat.Hom.hom f) a) (ψ.hom.naturality g.op).symm
  show Sec.res g (Sec.map φ a) = Sec.res g (Sec.map ψ a)
  rw [nφ, nψ]
  have ha : Sec.res g a = 0 ∨ ∃ (ζ : Prim Q Γ(V, ⊤)) (c : ℕ), (Sec.res g a : Sec (LateralTheory.KummerTheory.BockCut.TZ Q i) V) = c • LateralTheory.KummerTheory.BockCut.genZ i ζ := hP V g hg
  rcases ha with h0 | ⟨ζ, c, hc⟩
  · have e : (Sec.res g a : Sec (LateralTheory.KummerTheory.BockCut.TZ Q i) V) = 0 := h0
    rw [e]; simp only [Sec.map, map_zero]
  · rw [hc]; have hh := h V ζ; simp only [Sec.map] at hh ⊢; rw [map_nsmul, map_nsmul, hh]

end LateralTheory.KummerTheory.TwExtPf
