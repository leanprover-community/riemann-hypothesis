module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemMaximalIdealBall
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht
open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.Models (LevComp)

namespace GlobalTheory.LocM.Cocycle

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}

theorem exists_sab_of_isTrans {i i₂ : Idx H p} {τ : (Y i₂).X ⟶ (Y i).X} {mu : SABMap (Y i₂).t (Y i).t τ}
    (h : IsTrans i i₂ τ mu) :
    ∃ (b : i.c.V W →+* i₂.c.V W) (r : (Xo i₂.l).XF i₂.c ⟶ (Xo i.l).XF i.c) (ν : SABMap (Y i₂).oF.t (Y i).oF.t r),
      IsIncl b ∧ (Y i₂).j ≫ τ = r ≫ (Y i).j ∧ τ ≫ (Y i).s = (Y i₂).s ≫ spMap b ∧
      ν.φ ≫ (Y i).m.φ = (Y i₂).m.φ ≫ mu.φ ∧ LevComp (Y i₂).oF (Y i).oF r ν := by
  obtain ⟨b, π', r, hb, h₁, h₂, -, h₃, h₄, h₅⟩ := h
  have e : τ ≫ (Y i).s = (Y i₂).s ≫ spMap b := by
    rw [← h₁, ← h₂, Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨n, hn⟩ := LevelCover.sab_comp (Y i₂).m mu h₃
  obtain ⟨ν, hν⟩ := LevelCover.sab_cancel (Y i).m n r rfl
  refine ⟨b, r, ν, hb, h₃, e, hν.trans hn, fun a => ?_, fun a => ?_⟩
  · exact LevelCover.sec_cancel ν (Y i).m _ _ (by rw [hν, hn]; exact h₄ a)
  · exact LevelCover.sec_cancel ν (Y i).m _ _ (by rw [hν, hn]; exact h₅ a)

end GlobalTheory.LocM.Cocycle
