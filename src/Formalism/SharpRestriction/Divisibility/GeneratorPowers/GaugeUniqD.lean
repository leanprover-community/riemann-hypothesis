module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GaugeR

def gam (A : Type) [CommRing A] : Γ(Sp A, ⊤) →+* A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom

theorem gam_toΓ (A : Type) [CommRing A] (a : A) : gam A (toΓ A a) = a := by
  simp [gam, toΓ]

theorem gam_pull {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : Γ(Sp A, ⊤)) :
    gam B (((spMap f).app ⊤).hom x) = f (gam A x) := by
  have h := congrArg (fun g => g.hom x) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  simp only [gam, spMap]
  exact h

theorem gam_pullUnit {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Γ(Sp A, ⊤)ˣ) :
    gam B (pullUnit (spMap f) u : Γ(Sp B, ⊤)) = f (gam A u) := by
  simp only [pullUnit, pullU, Units.coe_map, MonoidHom.coe_coe]
  exact gam_pull f (u : Γ(Sp A, ⊤))

theorem scaled_genPow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {Y : Scheme.{0}} {K : Type} [Fintype K]
    (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ) {u : Γ(Y, ⊤)ˣ}
    {t t' : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)} (h : IsScaled u t t') (k : ℕ) :
    IsScaled (u ^ k) (genPow φ ε t k) (genPow φ ε t' k) := by
  unfold IsScaled at h ⊢
  intro j
  show t'.s j ^ k = _ * t.s j ^ k
  rw [h j, mul_pow, map_pow]
  rfl

theorem value_scaled {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (hL : L.IsLB) (a : ℤ)
    {T : Over S0} (s : LB.Sec (LPow A L a T)) (z : T ⟶ A)
    (τ τ' : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)))
    (v v' : Γ(T.left, ⊤)) (U : Γ(T.left, ⊤)ˣ) (h : IsValueAt A L a s z τ v) (h' : IsValueAt A L a s z τ' v')
    (hs : IsScaled U τ τ') : v = (U : Γ(T.left, ⊤)) * v' := by
  unfold IsValueAt at h h'
  unfold IsScaled at hs
  have key : ∀ j, (T.left.presheaf.map
      (homOfLE (le_top : (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)).U j ≤ ⊤)).op).hom v =
      (T.left.presheaf.map
      (homOfLE (le_top : (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)).U j ≤ ⊤)).op).hom ((U : Γ(T.left, ⊤)) * v') := by
    intro j
    have e := (h j).symm.trans (h' j)
    have e2 := congrArg Units.val (hs j)
    simp only [res, Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at e2
    simp only [e2] at e
    rw [map_mul]
    refine (Units.mul_left_inj (τ.s j)).mp ?_
    calc _ = _ := e
      _ = _ := mul_left_comm _ _ _
      _ = _ := (mul_assoc _ _ _).symm
  have hcov : (⊤ : T.left.Opens) ≤ ⨆ j, (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)).U j := by
    intro x _
    have hx : z.left.base x ∈ (⊤ : A.left.Opens) := trivial
    rw [← hL.cover] at hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨fun _ => i, ?_⟩
    show x ∈ L.wchart (fun _ => z.left) (fun _ => i)
    unfold LB.wchart
    exact Set.mem_iInter.mpr fun _ => hi
  exact T.left.sheaf.eq_of_locally_eq' _ ⊤ (fun j => homOfLE le_top) hcov v ((U : Γ(T.left, ⊤)) * v') key

end GaugeR

end Formalism.MainNotions.ModuliIntegralCharts.H1
