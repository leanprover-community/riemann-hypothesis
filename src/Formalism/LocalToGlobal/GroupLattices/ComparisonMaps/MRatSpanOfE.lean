module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RatActGOf
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ProdMemSpan
public import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
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

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} (G : GAtP p) {E LL : Type} [Field E] [Field LL] (e : LL →+* G.Kf)
  (iw : ∀ v : Fin G.P.nV, E →+* G.P.Qq v) (t : ∀ v : Fin G.P.nV, Fin (G.P.n' v) → E →+* LL)

def PosCompat : Prop :=
  ∀ (v : Fin G.P.nV) (s : Fin (G.P.n' v)) (x : E), e (t v s x) = G.P.ι v ((G.P.σ v ^ s.val) (iw v x))

def ActE : Prop :=
  ∀ (i : G.comp) (γ : (G.lev i).Γ), ∃ a : GL (Fin (G.P.m + 1)) E,
    ∀ v, (G.lev i).act v γ = Matrix.GeneralLinearGroup.map (iw v) a

def ChiRat : Prop :=
  ∀ (i : G.comp) (γ : (G.lev i).Γ), ∃ a : LL, e a = algebraMap G.O G.Kf ((G.lev i).χ γ : G.O)

def RatTup : Prop :=
  ∀ L : G.P.Tup, G.P.IsLatTup L → ∃ a : GL (Fin (G.P.m + 1)) E,
    ∀ v, L v = colSpan (G.P.W v) ((a : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) E).map (iw v))

theorem ratLev_of (hp : PosCompat G e iw t) (ha : ActE G iw) (hc : ChiRat G e) : RatLev G e := by
  refine ⟨fun i γ v s => ?_, hc⟩
  obtain ⟨a, ha⟩ := ha i γ
  refine ⟨Matrix.GeneralLinearGroup.map (t v s) a, ?_⟩
  rw [ha v]
  ext j k
  simp [gPosGL, hp v s]

theorem ratBasis_of (hp : PosCompat G e iw t) (hr : RatTup G iw) : RatBasis G e := by
  intro L hL v s
  obtain ⟨a, ha⟩ := hr L hL
  refine ⟨Matrix.GeneralLinearGroup.map (t v s) a, ?_⟩
  rw [ha v, Formalism.MainNotions.G.LatticeSystems.la_extO_G]
  congr 1
  ext j k
  simp [Formalism.MainNotions.G.LatticeSystems.la_tw, hp v s]

end Formalism.L2.G.Cmp
