module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyBaseChangeIffAndDegreeEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapSurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AV.AbVar

variable {K : Type} [Field K] (L : Type) [Field L] [Algebra K L]

def bcAdd (A : AbVar K) : End A →+ End (baseChange L A) where
  toFun f := End.of (bcMap L f.asHom)
  map_zero' := by
    apply End.ext
    change bcMap L (0 : A ⟶ A) = 0
    have h := bcMap_add L (0 : A ⟶ A) 0
    rw [zero_add] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  map_add' f g := End.ext (bcMap_add L f.asHom g.asHom)

theorem bcMap_intCast_sub (A : AbVar K) (n : ℤ) (f : End A) :
    End.of (bcMap L ((n : End A) - f).asHom) =
      (n : End (baseChange L A)) - End.of (bcMap L f.asHom) := by
  have h1 : bcAdd L A 1 = 1 := End.ext (bcMap_id L A)
  have hn : bcAdd L A (n : End A) = (n : End (baseChange L A)) := by
    simp only [← zsmul_one, map_zsmul, h1]
  change bcAdd L A ((n : End A) - f) = (n : End (baseChange L A)) - bcAdd L A f
  rw [map_sub, hn]

theorem isCharpoly_bcMap_iff (A : AbVar K) (f : End A) (P : Polynomial ℤ) :
    IsCharpoly (End.of (bcMap L f.asHom)) P ↔ IsCharpoly f P := by
  unfold IsCharpoly
  have hd : (baseChange L A).dim = A.dim := rfl
  refine and_congr Iff.rfl (and_congr (by rw [hd]) (forall_congr' fun n => ?_))
  rw [← bcMap_intCast_sub, (isIsogeny_bcMap_iff_and_deg_bcMap K L A A _).2]

theorem isCharpoly_unique {A : AbVar K} (f : End A) {P Q : Polynomial ℤ}
    (hP : IsCharpoly f P) (hQ : IsCharpoly f Q) : P = Q :=
  Polynomial.funext fun n => by rw [hP.2.2 n, hQ.2.2 n]

theorem charpoly_bcMap : ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A : AbVar K) (f : End A),
    charpoly (End.of (bcMap L f.asHom)) = charpoly f := by
  intro K _ L _ _ A f
  classical
  unfold charpoly
  by_cases h : ∃ P, IsCharpoly f P
  · have h' : ∃ P, IsCharpoly (End.of (bcMap L f.asHom)) P :=
      let ⟨P, hP⟩ := h; ⟨P, (isCharpoly_bcMap_iff L A f P).2 hP⟩
    rw [dite_eq_left h, dite_eq_left h']
    exact isCharpoly_unique f ((isCharpoly_bcMap_iff L A f _).1 h'.choose_spec) h.choose_spec
  · have h' : ¬ ∃ P, IsCharpoly (End.of (bcMap L f.asHom)) P :=
      fun ⟨P, hP⟩ => h ⟨P, (isCharpoly_bcMap_iff L A f P).1 hP⟩
    rw [dite_eq_right h, dite_eq_right h']

end GlobalTheory.AV.AbVar

end
