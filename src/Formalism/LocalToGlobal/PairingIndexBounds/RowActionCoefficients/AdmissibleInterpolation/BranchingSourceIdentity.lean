module

public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.Bridge
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.XFacts
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions.G.LatticeSystems

section Cast

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) (N : ℕ) (hm : P.m + 1 = N)

def emC (b : GlobalTheory P) (v : Fin N × Fin N) : (Σ v : Fin P.nV, Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) :=
  emP P b (Fin.cast hm.symm v.1, Fin.cast hm.symm v.2)

def gamC (g : ∀ v, Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) (b : GlobalTheory P) : Matrix (Fin N) (Fin N) Kf :=
  (gam P g b).submatrix (Fin.cast hm.symm) (Fin.cast hm.symm)

def nuC (b : GlobalTheory P) : Fin N → ℕ := fun t => nuB P b (Fin.cast hm.symm t)

variable (g : ∀ v, Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) (hg : ∀ v, IsUnit (g v).det)

include hg in
theorem htupW_leC (hinj : Function.Injective (algebraMap O Kf)) (T : Submodule O P.Xsp)
    (hT : ∀ F : GlobalTheory P → MvPolynomial (Fin N × Fin N) Kf,
      (∀ b, F b ∈ deltaL O Kf N (nuC P N hm b) (gamC P N hm g b)) →
        (∏ b : GlobalTheory P, (gamC P N hm g b).det ^ (-(eB P b))) • ∏ b, rename (emC P N hm b) (F b) ∈ T) :
    P.HtupW (fun v => colSpan (P.W v) (g v)) ≤ T := by
  subst hm
  exact htupW_le P g hg hinj T hT

include hg in
theorem mem_htupWC (hinj : Function.Injective (algebraMap O Kf)) (F : GlobalTheory P → MvPolynomial (Fin N × Fin N) Kf)
    (hF : ∀ b, F b ∈ deltaL O Kf N (nuC P N hm b) (gamC P N hm g b)) :
    (∏ b : GlobalTheory P, (gamC P N hm g b).det ^ (-(eB P b))) • ∏ b, rename (emC P N hm b) (F b) ∈
      P.HtupW (fun v => colSpan (P.W v) (g v)) := by
  subst hm
  exact mem_htupW P g hg hinj F hF

end Cast

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

theorem branching_source_identity : XBrS := by
  intro p _ X hinj j L g hg hL T hT
  cases j with
  | zero =>
    have hLe : L = fun v => colSpan (X.G.P.W v) (g v) := funext hL
    rw [hLe]
    exact htupW_leC X.G.P _ (rankJ X 0) g hg hinj T hT
  | succ j =>
    have hLe : L = fun v => colSpan (X.G.P.W v) (g v) := funext hL
    rw [hLe]
    exact htupW_leC (X.Fl.Pj (j + 1)) _ (rankJ X (j + 1)) g hg hinj T hT

theorem branching_target_identity : XBrT := by
  intro p _ X hinj j L g hg hL F hF
  cases j with
  | zero =>
    have hLe : L = fun v => colSpan (X.G.P.W v) (g v) := funext hL
    rw [hLe]
    exact mem_htupWC X.G.P _ (rankJ X 0) g hg hinj F hF
  | succ j =>
    have hLe : L = fun v => colSpan (X.G.P.W v) (g v) := funext hL
    rw [hLe]
    exact mem_htupWC (X.Fl.Pj (j + 1)) _ (rankJ X (j + 1)) g hg hinj F hF

end Formalism.L2.PairingIndexBounds.Ent
