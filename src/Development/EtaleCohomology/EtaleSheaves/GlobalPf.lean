module

public import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi
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
import Mathlib.Tactic.ENatToNat
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
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.GlobalPf

def gam {T : CommRingCat.{0}} {X : Scheme.{0}} (p : X ⟶ Spec T) (V : X.Opens) : T ⟶ Γ(X, V) :=
  (Scheme.ΓSpecIso T).inv ≫ p.appLE ⊤ V (by simp)

def Affine : Prop := ∀ (q : ℕ) (i : ℤ) {T K : CommRingCat.{0}} (k : T ⟶ K) {X : Scheme.{0}} (p : X ⟶ Spec T) (V : X.Opens),
  IsAffineOpen V → BC q i k (gam p V) → Eqv _ (sch.map (pullback.fst p (Spec.map k) ∣_ V)) (tw q i)

def LocEt : Prop := ∀ {T : CommRingCat.{0}} {X : Scheme.{0}} (p : X ⟶ Spec T) [Smooth p] (x : X),
  ∃ (U : X.Opens) (n : ℕ), x ∈ U ∧ ∀ V : X.Opens, IsAffineOpen V → V ≤ U →
    ∃ c : CommRingCat.of (MvPolynomial (Fin n) T) ⟶ Γ(X, V), Et c ∧
      CommRingCat.ofHom (MvPolynomial.C : T →+* MvPolynomial (Fin n) T) ≫ c = gam p V

theorem Global_of (hZ : ZarLocal) (hA : Affine) (hL : LocEt) : Global := by
  intro H q i T K k hG X p _
  refine hZ H (ZMod q) (tw q i) (pullback.fst p (Spec.map k)) fun x => ?_
  obtain ⟨U, n, hx, hU⟩ := hL p x
  refine ⟨U, hx, fun V hV hVU => ?_⟩
  obtain ⟨c, hc, hcg⟩ := hU V hV hVU
  have hb := hG n _ c hc
  rw [hcg] at hb
  exact hA q i k p V hV hb

end LateralTheory.E.GlobalPf

end
