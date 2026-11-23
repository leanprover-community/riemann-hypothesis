module

public import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel
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

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG

namespace Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem reGL_rfl {a : ℕ} (R : Type) [CommRing R] (x : GL (Fin a) R) : reGL rfl R x = x := by
  apply Units.ext
  ext i j
  simp [reGL]

theorem reV_rfl {a : ℕ} (E : Type) [Field E] (x : Fin a → E) : reV rfl E x = x := by
  ext i
  simp [reV]

theorem reL_rfl {a : ℕ} {E : Type} [Field E] [NumberField E] (L : Submodule (𝓞 E) (Fin a → E)) : reL rfl L = L := by
  ext z
  simp [reL, reV_rfl]

theorem Joint.Pv {D : D7} {X : Formalism.L2.Herm.ColsHerm D} {u : D.what₂.Word} {T : FormsTied D u} (J : Joint X u T)
    (v : (D.mem u).A.vT) : T.atT.Pv v = (X.atT u).Pv v := by
  unfold AtTTied.Pv
  rw [J.res]
  exact (X.atT u).res_ker v

end Formalism.L2.Forms
