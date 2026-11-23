module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Columns.CoefficientsModP
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions

section

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K) (lam : ι → DomWeight n)

theorem dualFr_tauLat_isLattice (τ : ι) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L) :
    Submodule.IsFullLattice K (dualFr (tauLat emb τ L)) :=
  (@dualFrLattice K _ _ starRingOfComm n 1 _ (by simp) (tauLatLattice E K ι n emb τ L hL)).1

theorem nabAtr_isLattice (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L) :
    Submodule.IsFullLattice K (nabAtr emb lam L) :=
  (nabDelLattice K ι n lam _ fun τ => dualFr_tauLat_isLattice emb τ L hL).1

theorem delAtr_isLattice (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L) :
    Submodule.IsFullLattice K (delAtr emb lam L) :=
  (nabDelLattice K ι n lam _ fun τ => dualFr_tauLat_isLattice emb τ L hL).2



variable [StarRing K]

variable (cE : E →+* E) (hc : ∀ τ x, star (emb τ x) = emb τ (cE x)) (J : Matrix (Fin n) (Fin n) E)
  (hJ : Formalism.UG.IsHerm cE J) (hdet : IsUnit J.det) (L L' : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
  (hL' : ∀ y, y ∈ L' ↔ ∀ x ∈ L, Formalism.UG.hform cE J x y ∈ (algebraMap (𝓞 E) E).range)

include hc hJ hdet hL hL'

end

end Formalism.L2.DIV
